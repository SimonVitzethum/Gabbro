/-
  File:      Grammatik/Isabelle/Absenkung_Parametrisch.lean
  Part of:   Gabbro -- Lean port of `beweise/Absenkung_Parametrisch.thy`
             (the lowering theorem, parametric over the target semantics;
             lane 168).

  What this file is: the finding that "the generated computes the model
  function" is FALSE, at a nameable place. It holds at the OCCUPIED slot
  (`absenkung_am_belegten_platz`) and falls at the free one
  (`absenkung_geht_am_freien_platz_auseinander` -- the model occupies the
  slot, the generated C leaves it free). What holds unconditionally is a
  case split with two branches (`absenkung_relabel`), and what the
  generator claims in prose is the weaker INVARIANT theorem
  (`relabel_erhaelt_wohlgeformt`) -- which holds, for a different reason
  than expected. The two counterexamples (aliasing without E4,
  `option.sonderwert` without E6) live in the weak locale: they satisfy
  E1--E3 and break the theorem.

  Model notes: the locales `zielraum`/`zielsemantik` are Lean structures
  (extends); `abbild` is the same definition (`deutebelegt` returns
  `Bool`, so the condition is `... = true` -- the same proposition).
  The `interpretation` proofs are structure instances (`aliasbruch`,
  `sonderwert_inst`, and the healthy `gesund` for the witnesses).
  Everything else -- `umhaengen`, `wohlgeformt`, `erreicht`, `ueber`,
  `umhaengen_erhaelt` -- is imported from `Table_Ops_Erhaltung`.

  No bridge to the model semantics: the named properties E1--E6 are
  about the C/machine target, which has no counterpart in
  `Semantik.lean` -- that absence is the point of the parametrisation.
-/

import Grammatik.Isabelle.Table_Ops_Erhaltung

namespace Gabbro.Grammatik.AbsenkungParam

open Gabbro.Grammatik.TableOps

set_option linter.unusedVariables false

/-! ## The readout -- how a target state reads as a table -/

/-- A lowering is not a statement without a readout: the map from a
    target state to the model. Three parts: `i < N` (capacity),
    `deutebelegt` (occupancy at its own site), `deute` (the parent
    pointer, read). -/
def Abbild {Z L W : Type} (lies : Z → L → W) (ort belegtort : Nat → L)
    (deute : W → Option Nat) (deutebelegt : W → Bool) (N : Nat) (z : Z) :
    Tabelle :=
  fun i => if i < N ∧ deutebelegt (lies z (belegtort i)) = true
    then some ({ elter := deute (lies z (ort i)) } : Slot) else none

/-! ## The NAMED properties of the target semantics -/

/-- The weak locale: E1 frame, E2 hit, E3 assignment. -/
structure Zielraum (Z L W : Type) where
  lies : Z → L → W
  schreib : Z → L → W → Z
  ort : Nat → L
  belegtort : Nat → L
  deute : W → Option Nat
  deutebelegt : W → Bool
  wort : Nat → W
  N : Nat
  wirkung : Nat → Nat → Z → Z
  E1 : ∀ (z : Z) (a b : L) (v : W), b ≠ a → lies (schreib z a v) b = lies z b
  E2 : ∀ (z : Z) (a : L) (v : W), lies (schreib z a v) a = v
  E3 : ∀ (s p : Nat) (z : Z), s < N → p < N → wirkung s p z = schreib z (ort s) (wort p)

/-- The full locale: E4 separate, E5 disjoint, E6 faithful decoding. -/
structure Zielsemantik (Z L W : Type) extends Zielraum Z L W where
  E4 : ∀ (i j : Nat), i < N → j < N → i ≠ j → ort i ≠ ort j
  E5 : ∀ (i j : Nat), i < N → j < N → ort i ≠ belegtort j
  E6 : ∀ (i : Nat), i < N → deute (wort i) = some i

/-- The readout of a target state. -/
def Ab {Z L W : Type} (S : Zielraum Z L W) (z : Z) : Tabelle :=
  Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N z

/-! ## What does NOT move -- every other slot -/

/-- A-1: a slot other than `s` reads unchanged after the write, in both
    fields. Needs E1, E4, E5 and nothing else. -/
theorem anderer_platz_unberuehrt {Z L W : Type} (S : Zielsemantik Z L W)
    (s p : Nat) (z : Z) (i : Nat)
    (hs : s < S.N) (hp : p < S.N) (hne : i ≠ s) :
    Ab S.toZielraum (S.wirkung s p z) i = Ab S.toZielraum z i := by
  by_cases hi : i < S.N
  · have schritt : S.wirkung s p z = S.schreib z (S.ort s) (S.wort p) :=
      S.E3 s p z hs hp
    have hb : S.lies (S.wirkung s p z) (S.belegtort i)
        = S.lies z (S.belegtort i) := by
      rw [schritt]
      exact S.E1 z (S.ort s) (S.belegtort i) (S.wort p)
        (Ne.symm (S.E5 s i hs hi))
    have ho : S.lies (S.wirkung s p z) (S.ort i) = S.lies z (S.ort i) := by
      rw [schritt]
      exact S.E1 z (S.ort s) (S.ort i) (S.wort p) (S.E4 i s hi hs hne)
    show Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N
        (S.wirkung s p z) i
      = Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N z i
    simp only [Abbild, hb, ho]
  · have c1 : ¬ (i < S.N
        ∧ S.deutebelegt (S.lies (S.wirkung s p z) (S.belegtort i)) = true) :=
      fun h => hi h.1
    have c2 : ¬ (i < S.N
        ∧ S.deutebelegt (S.lies z (S.belegtort i)) = true) :=
      fun h => hi h.1
    have e1 : Ab S.toZielraum (S.wirkung s p z) i = none := by
      show Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N
        (S.wirkung s p z) i = none
      simp [Abbild, c1]
    have e2 : Ab S.toZielraum z i = none := by
      show Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N z i
        = none
      simp [Abbild, c2]
    rw [e1, e2]

/-- A-2: and the OCCUPANCY of the relinked slot does not move either.
    The line on which the theorem later breaks: the generated C writes
    the parent field and does NOT touch occupancy. -/
theorem belegung_von_s_unberuehrt {Z L W : Type} (S : Zielsemantik Z L W)
    (s p : Nat) (z : Z) (hs : s < S.N) (hp : p < S.N) :
    S.deutebelegt (S.lies (S.wirkung s p z) (S.belegtort s))
      = S.deutebelegt (S.lies z (S.belegtort s)) := by
  have schritt : S.wirkung s p z = S.schreib z (S.ort s) (S.wort p) :=
    S.E3 s p z hs hp
  have hne : S.belegtort s ≠ S.ort s := Ne.symm (S.E5 s s hs hs)
  have e : S.lies (S.wirkung s p z) (S.belegtort s)
      = S.lies z (S.belegtort s) := by
    rw [schritt]
    exact S.E1 z (S.ort s) (S.belegtort s) (S.wort p) hne
  rw [e]

/-! ## The theorem -- and it holds only at the OCCUPIED slot -/

/-- S-1: the lowering in the shape §7 requires. The third premise is
    the finding: it is in neither U-3 nor the generated head. -/
theorem absenkung_am_belegten_platz {Z L W : Type} (S : Zielsemantik Z L W)
    (s p : Nat) (z : Z)
    (hs : s < S.N) (hp : p < S.N)
    (hbelegt : S.deutebelegt (S.lies z (S.belegtort s)) = true) :
    Ab S.toZielraum (S.wirkung s p z) = Umhaengen (Ab S.toZielraum z) s p := by
  apply funext
  intro i
  by_cases heq : i = s
  · rw [heq]
    have schritt : S.wirkung s p z = S.schreib z (S.ort s) (S.wort p) :=
      S.E3 s p z hs hp
    have noch : S.deutebelegt (S.lies (S.wirkung s p z) (S.belegtort s))
        = true := by
      rw [belegung_von_s_unberuehrt S s p z hs hp]
      exact hbelegt
    have gelesen : S.lies (S.wirkung s p z) (S.ort s) = S.wort p := by
      rw [schritt]
      exact S.E2 z (S.ort s) (S.wort p)
    have gedeutet : S.deute (S.lies (S.wirkung s p z) (S.ort s))
        = some p := by
      rw [gelesen]
      exact S.E6 p hp
    have e1 : Ab S.toZielraum (S.wirkung s p z) s
        = some ({ elter := some p } : Slot) := by
      show Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N
        (S.wirkung s p z) s = _
      simp [Abbild, hs, noch, gedeutet]
    have e2 : Umhaengen (Ab S.toZielraum z) s p s
        = some ({ elter := some p } : Slot) :=
      upd_at _ _ _
    rw [e1, e2]
  · have h1 : Ab S.toZielraum (S.wirkung s p z) i = Ab S.toZielraum z i :=
      anderer_platz_unberuehrt S s p z i hs hp heq
    have h2 : Umhaengen (Ab S.toZielraum z) s p i = Ab S.toZielraum z i :=
      upd_diff _ _ _ _ heq
    rw [h1, h2]

/-! ## And it falls at the FREE slot -- that is the finding -/

/-- S-2: at the free slot the product does not move the model AT ALL. -/
theorem relabel_am_freien_platz_ist_wirkungslos {Z L W : Type}
    (S : Zielsemantik Z L W) (s p : Nat) (z : Z)
    (hs : s < S.N) (hp : p < S.N)
    (hfrei : ¬ S.deutebelegt (S.lies z (S.belegtort s)) = true) :
    Ab S.toZielraum (S.wirkung s p z) = Ab S.toZielraum z := by
  apply funext
  intro i
  by_cases heq : i = s
  · rw [heq]
    have hnoch : ¬ S.deutebelegt (S.lies (S.wirkung s p z) (S.belegtort s))
        = true := by
      rw [belegung_von_s_unberuehrt S s p z hs hp]
      exact hfrei
    have e1 : Ab S.toZielraum (S.wirkung s p z) s = none := by
      show Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N
        (S.wirkung s p z) s = none
      simp [Abbild, hs, hnoch]
    have e2 : Ab S.toZielraum z s = none := by
      show Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N z s
        = none
      simp [Abbild, hs, hfrei]
    rw [e1, e2]
  · exact anderer_platz_unberuehrt S s p z i hs hp heq

/-- S-3: so the two come apart -- a `Some` against a `None`, at exactly
    one place. -/
theorem absenkung_geht_am_freien_platz_auseinander {Z L W : Type}
    (S : Zielsemantik Z L W) (s p : Nat) (z : Z)
    (hs : s < S.N) (hp : p < S.N)
    (hfrei : ¬ S.deutebelegt (S.lies z (S.belegtort s)) = true) :
    Ab S.toZielraum (S.wirkung s p z)
      ≠ Umhaengen (Ab S.toZielraum z) s p := by
  have hworher : Ab S.toZielraum z s = none := by
    show Abbild S.lies S.ort S.belegtort S.deute S.deutebelegt S.N z s
      = none
    simp [Abbild, hs, hfrei]
  have hlinks : Ab S.toZielraum (S.wirkung s p z) s = none := by
    rw [relabel_am_freien_platz_ist_wirkungslos S s p z hs hp hfrei]
    exact hworher
  have hrechts : Umhaengen (Ab S.toZielraum z) s p s
      = some ({ elter := some p } : Slot) :=
    upd_at _ _ _
  intro hcon
  have e := congrFun hcon s
  rw [hlinks, hrechts] at e
  cases e

/-! ## What holds UNCONDITIONALLY: two branches, not one -/

/-- S-4: the honest form, with two branches. -/
theorem absenkung_relabel {Z L W : Type} (S : Zielsemantik Z L W)
    (s p : Nat) (z : Z) (hs : s < S.N) (hp : p < S.N) :
    Ab S.toZielraum (S.wirkung s p z)
      = (if S.deutebelegt (S.lies z (S.belegtort s)) = true
          then Umhaengen (Ab S.toZielraum z) s p else Ab S.toZielraum z) := by
  by_cases h : S.deutebelegt (S.lies z (S.belegtort s)) = true
  · rw [if_pos h]
    exact absenkung_am_belegten_platz S s p z hs hp h
  · rw [if_neg h]
    exact relabel_am_freien_platz_ist_wirkungslos S s p z hs hp h

/-- S-5: and the INVARIANT lowers unconditionally -- the theorem `emit.rs`
    carries in prose. The two branches hold for DIFFERENT reasons. -/
theorem relabel_erhaelt_wohlgeformt {Z L W : Type} (S : Zielsemantik Z L W)
    (s p : Nat) (z : Z)
    (hs : s < S.N) (hp : p < S.N)
    (hwf : Wohlgeformt (Ab S.toZielraum z))
    (helter : Erreicht (Ab S.toZielraum z) p)
    (hnicht : ¬ Ueber (Ab S.toZielraum z) p s) :
    Wohlgeformt (Ab S.toZielraum (S.wirkung s p z)) := by
  by_cases h : S.deutebelegt (S.lies z (S.belegtort s)) = true
  · have e : Ab S.toZielraum (S.wirkung s p z)
        = Umhaengen (Ab S.toZielraum z) s p :=
      absenkung_am_belegten_platz S s p z hs hp h
    rw [e]
    exact umhaengen_erhaelt _ _ _ hwf helter hnicht
  · have e : Ab S.toZielraum (S.wirkung s p z) = Ab S.toZielraum z :=
      relabel_am_freien_platz_ist_wirkungslos S s p z hs hp h
    rw [e]
    exact hwf

/-! ## Two counterexamples -- the properties are no decoration -/

/-- Point update on the toy target. -/
def updW (z : Nat → Nat) (a v : Nat) : Nat → Nat :=
  fun x => if x = a then v else z x

theorem updW_self (z : Nat → Nat) (a v : Nat) : updW z a v a = v := by
  show (if a = a then v else z a) = _
  rw [if_pos rfl]

theorem updW_diff (z : Nat → Nat) (a v x : Nat) (h : x ≠ a) :
    updW z a v x = z x := by
  show (if x = a then v else z x) = _
  rw [if_neg h]

/-- The thinnest carrier for a counterexample: states are maps. -/
def wlies (z : Nat → Nat) (a : Nat) : Nat :=
  z a

def wschreib (z : Nat → Nat) (a v : Nat) : Nat → Nat :=
  updW z a v

def wbelegtort (i : Nat) : Nat :=
  10 + i

def wdeutebelegt : Nat → Bool :=
  fun w => decide (w ≠ 0)

def wwort (i : Nat) : Nat :=
  i

/-- Without E4: two slots share their parent field. -/
def gort : Nat → Nat :=
  fun _ => 0

def gdeute : Nat → Option Nat :=
  fun w => if w = 2 then none else some w

def gwirkung (s p : Nat) (z : Nat → Nat) : Nat → Nat :=
  updW z (gort s) (wwort p)

/-- The alias break satisfies E1--E3. -/
def aliasbruch : Zielraum (Nat → Nat) Nat Nat where
  lies := wlies
  schreib := wschreib
  ort := gort
  belegtort := wbelegtort
  deute := gdeute
  deutebelegt := wdeutebelegt
  wort := wwort
  N := 2
  wirkung := gwirkung
  E1 := by
    intro z a b v h
    show updW z a v b = z b
    exact updW_diff _ _ _ _ h
  E2 := by
    intro z a v
    show updW z a v a = v
    exact updW_self _ _ _
  E3 := by
    intro s p z _ _
    rfl

theorem aliasbruch_verletzt_E4 : gort 0 = gort 1 :=
  rfl

theorem aliasbruch_bricht_die_absenkung :
    Abbild wlies gort wbelegtort gdeute wdeutebelegt 2
        (gwirkung 0 0 (fun _ => 1))
      ≠ Umhaengen
        (Abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (fun _ => 1))
        0 0 := by
  intro hcon
  have vorher : Abbild wlies gort wbelegtort gdeute wdeutebelegt 2
      (fun _ => 1) 1
      = some ({ elter := some 1 } : Slot) := by
    decide
  have nachher : Abbild wlies gort wbelegtort gdeute wdeutebelegt 2
      (gwirkung 0 0 (fun _ => 1)) 1
      = some ({ elter := some 0 } : Slot) := by
    decide
  have u : Umhaengen
      (Abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (fun _ => 1))
      0 0 1
      = some ({ elter := some 1 } : Slot) := by
    have e : Umhaengen
        (Abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (fun _ => 1))
        0 0 1
        = Abbild wlies gort wbelegtort gdeute wdeutebelegt 2 (fun _ => 1) 1 :=
      upd_diff _ _ _ _ (by decide)
    rw [e]
    exact vorher
  have e := congrFun hcon 1
  rw [nachher, u] at e
  cases e

/-- Without E6: the `option.sonderwert` break. -/
def dgort : Nat → Nat :=
  fun i => i

def dgdeute : Nat → Option Nat :=
  fun w => if w = 1 then none else some w

def dgwirkung (s p : Nat) (z : Nat → Nat) : Nat → Nat :=
  updW z (dgort s) (wwort p)

/-- The sonderwert break satisfies E1--E3. -/
def sonderwert_inst : Zielraum (Nat → Nat) Nat Nat where
  lies := wlies
  schreib := wschreib
  ort := dgort
  belegtort := wbelegtort
  deute := dgdeute
  deutebelegt := wdeutebelegt
  wort := wwort
  N := 2
  wirkung := dgwirkung
  E1 := by
    intro z a b v h
    show updW z a v b = z b
    exact updW_diff _ _ _ _ h
  E2 := by
    intro z a v
    show updW z a v a = v
    exact updW_self _ _ _
  E3 := by
    intro s p z _ _
    rfl

/-- E4 and E5 HOLD here -- otherwise two things would break at once and
    the counterexample would say nothing about E6. -/
theorem sonderwert_haelt_E4 {i j : Nat} (_hi : i < 2) (_hj : j < 2)
    (hne : i ≠ j) : dgort i ≠ dgort j :=
  hne

theorem sonderwert_haelt_E5 {i j : Nat} (hi : i < 2) (hj : j < 2) :
    dgort i ≠ wbelegtort j := by
  show i ≠ 10 + j
  omega

theorem sonderwert_verletzt_E6 : dgdeute (wwort 1) ≠ some 1 := by
  show (if (1 : Nat) = 1 then (none : Option Nat) else some 1) ≠ some 1
  rw [if_pos rfl]
  decide

theorem sonderwert_bricht_die_absenkung :
    Abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2
        (dgwirkung 0 1 (fun _ => 5))
      ≠ Umhaengen
        (Abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2 (fun _ => 5))
        0 1 := by
  intro hcon
  have nachher : Abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2
      (dgwirkung 0 1 (fun _ => 5)) 0
      = some ({ elter := none } : Slot) := by
    decide
  have u : Umhaengen
      (Abbild wlies dgort wbelegtort dgdeute wdeutebelegt 2 (fun _ => 5))
      0 1 0
      = some ({ elter := some 1 } : Slot) :=
    upd_at _ _ _
  have e := congrFun hcon 0
  rw [nachher, u] at e
  cases e

/-! ## Witnesses: the healthy target.

Separating slots, disjoint occupancy, faithful decoding, exact
occupancy reading -- every premise of the full locale fires. -/

/-- The healthy instance: `ort i = i`, decoding is `some`, every slot
    reads occupied. -/
def gesund : Zielsemantik (Nat → Nat) Nat Nat where
  lies := wlies
  schreib := wschreib
  ort := fun i => i
  belegtort := wbelegtort
  deute := fun w => some w
  deutebelegt := fun _ => true
  wort := fun i => i
  N := 2
  wirkung := fun s p z => updW z s p
  E1 := by
    intro z a b v h
    show updW z a v b = z b
    exact updW_diff _ _ _ _ h
  E2 := by
    intro z a v
    show updW z a v a = v
    exact updW_self _ _ _
  E3 := by
    intro s p z _ _
    rfl
  E4 := by
    intro i j _ _ h
    exact h
  E5 := by
    intro i j hi hj
    show i ≠ 10 + j
    omega
  E6 := by
    intro i _
    rfl

/-- The free-slot instance: everything of E1--E6, but no slot reads
    occupied -- the shape the S-2/S-3 witnesses need. -/
def gesundFrei : Zielsemantik (Nat → Nat) Nat Nat where
  lies := wlies
  schreib := wschreib
  ort := fun i => i
  belegtort := wbelegtort
  deute := fun w => some w
  deutebelegt := fun _ => false
  wort := fun i => i
  N := 2
  wirkung := fun s p z => updW z s p
  E1 := by
    intro z a b v h
    show updW z a v b = z b
    exact updW_diff _ _ _ _ h
  E2 := by
    intro z a v
    show updW z a v a = v
    exact updW_self _ _ _
  E3 := by
    intro s p z _ _
    rfl
  E4 := by
    intro i j _ _ h
    exact h
  E5 := by
    intro i j hi hj
    show i ≠ 10 + j
    omega
  E6 := by
    intro i _
    rfl

theorem anderer_platz_unberuehrt_zeuge :
    Ab gesund.toZielraum (gesund.wirkung 0 1 (fun _ => 5)) 1
      = Ab gesund.toZielraum (fun _ => 5) 1 :=
  anderer_platz_unberuehrt gesund 0 1 (fun _ => 5) 1
    (by decide) (by decide) (by decide)

theorem belegung_von_s_unberuehrt_zeuge : (true : Bool) = true :=
  belegung_von_s_unberuehrt gesund 0 1 (fun _ => 5)
    (by decide) (by decide)

theorem absenkung_am_belegten_platz_zeuge :
    Ab gesund.toZielraum (gesund.wirkung 0 1 (fun _ => 5))
      = Umhaengen (Ab gesund.toZielraum (fun _ => 5)) 0 1 :=
  absenkung_am_belegten_platz gesund 0 1 (fun _ => 5)
    (by decide) (by decide) (by decide)

theorem relabel_am_freien_platz_ist_wirkungslos_zeuge :
    Ab gesundFrei.toZielraum (gesundFrei.wirkung 0 1 (fun _ => 0))
      = Ab gesundFrei.toZielraum (fun _ => 0) := by
  apply relabel_am_freien_platz_ist_wirkungslos gesundFrei 0 1 (fun _ => 0)
    (by decide) (by decide)
  decide

theorem absenkung_geht_am_freien_platz_auseinander_zeuge :
    Ab gesundFrei.toZielraum (gesundFrei.wirkung 0 1 (fun _ => 0))
      ≠ Umhaengen (Ab gesundFrei.toZielraum (fun _ => 0)) 0 1 := by
  apply absenkung_geht_am_freien_platz_auseinander gesundFrei 0 1 (fun _ => 0)
    (by decide) (by decide)
  decide

theorem absenkung_relabel_zeuge :
    Ab gesund.toZielraum (gesund.wirkung 0 1 (fun _ => 5))
      = (if gesund.deutebelegt
            (gesund.lies (fun _ => 5) (gesund.belegtort 0)) = true
          then Umhaengen (Ab gesund.toZielraum (fun _ => 5)) 0 1
          else Ab gesund.toZielraum (fun _ => 5)) :=
  absenkung_relabel gesund 0 1 (fun _ => 5) (by decide) (by decide)

theorem relabel_erhaelt_wohlgeformt_zeuge
    (hwf : Wohlgeformt (Ab gesund.toZielraum (fun _ => 5)))
    (helter : Erreicht (Ab gesund.toZielraum (fun _ => 5)) 1)
    (hnicht : ¬ Ueber (Ab gesund.toZielraum (fun _ => 5)) 1 0) :
    Wohlgeformt (Ab gesund.toZielraum (gesund.wirkung 0 1 (fun _ => 5))) :=
  relabel_erhaelt_wohlgeformt gesund 0 1 (fun _ => 5)
    (by decide) (by decide) hwf helter hnicht

end Gabbro.Grammatik.AbsenkungParam
