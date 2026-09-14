/-
  File:      Grammatik/Isabelle/Table_Ops_Erhaltung.lean
  Part of:   Gabbro -- Lean port of `beweise/Table_Ops_Erhaltung.thy`
             (template `table.ops.erhaltung`, S5; lane 168).

  What this file is: the amortisation law (Part I -- once per operation,
  not per call site), THREE concrete generated mutations against the
  concrete invariant of the corpus (Part II -- `insert` needs a fresh
  slot and a reachable parent, `delete_leaf` needs a leaf, `relabel`
  needs the no-cycle condition `¬ über σ p s`), and two boundaries as
  counterexamples (Part III -- relinking falls WITHOUT its condition,
  and a connecting invariant is not covered).

  Model notes: the locale `traeger` is section-free explicit parameters
  (`wirkung`, `online`, and the `je_operation` assumption as an explicit
  premise per lemma -- Isabelle's `assumes` lines). The `slot` record is
  a Lean structure; `erreicht` and `ueber` are Lean inductives with the
  same two constructors each; `wohlgeformt`, `blatt`, the three
  mutations and `zwei` are the same definitions (function update is
  `upd` -- `Function.update` does not exist in this core).

  No bridge to the model semantics: the mutations are hand-defined
  model functions (that the emitted C bodies ARE these functions is not
  proved -- the same boundary as in the theory).
-/

namespace Gabbro.Grammatik.TableOps

set_option linter.unusedVariables false

variable {Op Z : Type}

/-! ## Part I -- the amortisation law -/

/-- Running a list of generated operations. -/
def laufen (wirkung : Op → Z → Z) : List Op → Z → Z
  | [], z => z
  | p :: ps, z => laufen wirkung ps (wirkung p z)

/-- Reachability: `z'` is reachable from `z` by generated operations. -/
def erreichbar (wirkung : Op → Z → Z) (z z' : Z) : Prop :=
  ∃ ps, laufen wirkung ps z = z'

/-- K-1: a SEQUENCE of generated operations preserves every `online`
    invariant. The licence: the generator shows it per operation, the
    programmer uses it any number of times. -/
theorem folge_erhaelt (wirkung : Op → Z → Z) (online : (Z → Prop) → Prop)
    (je : ∀ (p : Op) (I : Z → Prop), online I → ∀ z, I z → I (wirkung p z))
    (I : Z → Prop) (ps : List Op) (z : Z)
    (hI : online I) (hz : I z) : I (laufen wirkung ps z) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih => exact ih _ (je p I hI z hz)

/-- K-2: so it holds in EVERY reachable state. -/
theorem erreichbares_erhaelt (wirkung : Op → Z → Z)
    (online : (Z → Prop) → Prop)
    (je : ∀ (p : Op) (I : Z → Prop), online I → ∀ z, I z → I (wirkung p z))
    (I : Z → Prop) (z z' : Z)
    (hI : online I) (hz : I z) (h : erreichbar wirkung z z') : I z' := by
  obtain ⟨ps, hps⟩ := h
  rw [← hps]
  exact folge_erhaelt wirkung online je I ps z hI hz

/-! ## Part II -- three concrete mutations, the corpus invariant -/

/-- A slot of the running example: one parent pointer. -/
structure Slot where
  elter : Option Nat
deriving DecidableEq

/-- The table state. -/
abbrev Tabelle : Type :=
  Nat → Option Slot

/-- Point update. -/
def upd (σ : Tabelle) (n : Nat) (w : Option Slot) : Tabelle :=
  fun s => if s = n then w else σ s

theorem upd_at (σ : Tabelle) (n : Nat) (w : Option Slot) :
    upd σ n w n = w := by
  show (if n = n then w else σ n) = _
  rw [if_pos rfl]

theorem upd_diff (σ : Tabelle) (n s : Nat) (w : Option Slot) (h : s ≠ n) :
    upd σ n w s = σ s := by
  show (if s = n then w else σ s) = _
  rw [if_neg h]

/-- Reachability of the root along parent pointers. -/
inductive Erreicht (σ : Tabelle) : Nat → Prop where
  | wurzel (s : Nat) (sl : Slot) :
      σ s = some sl → sl.elter = none → Erreicht σ s
  | aufstieg (s : Nat) (sl : Slot) (p : Nat) :
      σ s = some sl → sl.elter = some p → Erreicht σ p → Erreicht σ s

/-- The corpus invariant: every occupied slot reaches the root. -/
def Wohlgeformt (σ : Tabelle) : Prop :=
  ∀ s sl, σ s = some sl → Erreicht σ s

/-- A slot is a LEAF when nobody names it as a parent. -/
def Blatt (σ : Tabelle) (s : Nat) : Prop :=
  ∀ t tl, σ t = some tl → tl.elter ≠ some s

/-- The first mutation: hanging a FRESH slot under a reachable one. -/
def Einfuegen (σ : Tabelle) (n p : Nat) : Tabelle :=
  upd σ n (some { elter := some p })

/-- The second mutation: deleting a LEAF. -/
def BlattLoeschen (σ : Tabelle) (s : Nat) : Tabelle :=
  upd σ s none

/-- The third mutation: relinking -- relabel. -/
def Umhaengen (σ : Tabelle) (s p : Nat) : Tabelle :=
  upd σ s (some { elter := some p })

/-- `ueber σ x s`: `s` lies on `x`'s parent chain, `x` included. The
    reflexive-transitive hull of the parent edge. Reflexivity is half
    the statement: `umhaengen σ s s` is a loop. -/
inductive Ueber (σ : Tabelle) : Nat → Nat → Prop where
  | hier (s : Nat) : Ueber σ s s
  | hoeher (x : Nat) (xl : Slot) (q s : Nat) :
      σ x = some xl → xl.elter = some q → Ueber σ q s → Ueber σ x s

/-- M-1: a fresh slot disturbs no existing reachability. Every chain
    consists of slots occupied in `σ`, and `n` is not. -/
theorem erreicht_bleibt_bei_frischem (σ : Tabelle) (n x : Nat)
    (sl0 : Option Slot) (hfrisch : σ n = none) (h : Erreicht σ x) :
    Erreicht (upd σ n sl0) x := by
  induction h with
  | wurzel s sl hs he =>
    have hne : s ≠ n := by
      intro hcon
      rw [hcon] at hs
      rw [hfrisch] at hs
      cases hs
    have hs' : upd σ n sl0 s = some sl := by
      rw [upd_diff _ _ _ _ hne]; exact hs
    exact Erreicht.wurzel s sl hs' he
  | aufstieg s sl p hs he _ ih =>
    have hne : s ≠ n := by
      intro hcon
      rw [hcon] at hs
      rw [hfrisch] at hs
      cases hs
    have hs' : upd σ n sl0 s = some sl := by
      rw [upd_diff _ _ _ _ hne]; exact hs
    exact Erreicht.aufstieg s sl p hs' he ih

/-- M-2: so the invariant holds. The two premises are exactly the two
    lines the generator would have to write. -/
theorem einfuegen_erhaelt (σ : Tabelle) (n p : Nat)
    (hwf : Wohlgeformt σ) (hfrisch : σ n = none) (helter : Erreicht σ p) :
    Wohlgeformt (Einfuegen σ n p) := by
  have pneu : Erreicht (Einfuegen σ n p) p :=
    erreicht_bleibt_bei_frischem σ n p (some { elter := some p }) hfrisch helter
  intro s sl hs
  by_cases hsn : s = n
  · have hss : Einfuegen σ n p n = some ({ elter := some p } : Slot) :=
      upd_at σ n _
    rw [hsn] at hs
    rw [hss] at hs
    rw [hsn]
    exact Erreicht.aufstieg n { elter := some p } p hss rfl pneu
  · have hs' : σ s = some sl := by
      have e : Einfuegen σ n p s = σ s := upd_diff σ n s _ hsn
      rw [e] at hs
      exact hs
    have hr : Erreicht σ s := hwf s sl hs'
    exact erreicht_bleibt_bei_frischem σ n s (some { elter := some p }) hfrisch hr

/-- M-3: a chain that does not START at `s` never touches `s` when `s`
    is a leaf -- it would have to enter `s` through a parent pointer,
    and there is none. -/
theorem erreicht_ohne_blatt (σ : Tabelle) (s x : Nat)
    (hblatt : Blatt σ s) (h : Erreicht σ x) :
    x ≠ s → Erreicht (upd σ s none) x := by
  induction h with
  | wurzel t tl hs he =>
    intro hne
    have hs' : upd σ s none t = some tl := by
      have e : upd σ s none t = σ t := upd_diff σ s t _ hne
      rw [e]; exact hs
    exact Erreicht.wurzel t tl hs' he
  | aufstieg t tl p hs he _ ih =>
    intro hne
    have hps : p ≠ s := by
      intro hcon
      rw [hcon] at he
      exact hblatt t tl hs he
    have qda := ih hps
    have hs' : upd σ s none t = some tl := by
      have e : upd σ s none t = σ t := upd_diff σ s t _ hne
      rw [e]; exact hs
    exact Erreicht.aufstieg t tl p hs' he qda

theorem blatt_loeschen_erhaelt (σ : Tabelle) (s : Nat)
    (hwf : Wohlgeformt σ) (hblatt : Blatt σ s) :
    Wohlgeformt (BlattLoeschen σ s) := by
  intro x xl hx
  have hne : x ≠ s := by
    intro hcon
    have e : BlattLoeschen σ s x = none := by
      rw [hcon]
      exact upd_at σ s _
    rw [e] at hx
    cases hx
  have hx' : σ x = some xl := by
    have e : BlattLoeschen σ s x = σ x := upd_diff σ s x _ hne
    rw [← e]
    exact hx
  have hr : Erreicht σ x := hwf x xl hx'
  exact erreicht_ohne_blatt σ s x hblatt hr hne

/-- U-1: a chain that never touches `s` survives relinking unchanged. -/
theorem umhaengen_ausserhalb (σ : Tabelle) (s p x : Nat)
    (h : Erreicht σ x) : ¬ Ueber σ x s → Erreicht (Umhaengen σ s p) x := by
  induction h with
  | wurzel y yl hs he =>
    intro hnu
    have hne : y ≠ s := by
      intro hcon
      apply hnu
      rw [hcon]
      exact Ueber.hier s
    have hs' : Umhaengen σ s p y = some yl := by
      have e : Umhaengen σ s p y = σ y := upd_diff σ s y _ hne
      rw [e]; exact hs
    exact Erreicht.wurzel y yl hs' he
  | aufstieg y yl q hs he _ ih =>
    intro hnu
    have hne : y ≠ s := by
      intro hcon
      apply hnu
      rw [hcon]
      exact Ueber.hier s
    have hnq : ¬ Ueber σ q s := by
      intro hcon
      apply hnu
      exact Ueber.hoeher y yl q s hs he hcon
    have qda := ih hnq
    have hs' : Umhaengen σ s p y = some yl := by
      have e : Umhaengen σ s p y = σ y := upd_diff σ s y _ hne
      rw [e]; exact hs
    exact Erreicht.aufstieg y yl q hs' he qda

/-- U-2: and whoever reaches `s` at all continues past `s` afterwards.
    Both cases -- through `s` or past it -- in the same induction. -/
theorem umhaengen_durch_s (σ : Tabelle) (s p x : Nat)
    (h : Erreicht σ x) :
    Erreicht (Umhaengen σ s p) s → Erreicht (Umhaengen σ s p) x := by
  induction h with
  | wurzel y yl hs he =>
    intro hsda
    by_cases heq : y = s
    · rw [heq]
      exact hsda
    · have hs' : Umhaengen σ s p y = some yl := by
        have e : Umhaengen σ s p y = σ y := upd_diff σ s y _ heq
        rw [e]; exact hs
      exact Erreicht.wurzel y yl hs' he
  | aufstieg y yl q hs he _ ih =>
    intro hsda
    by_cases heq : y = s
    · rw [heq]
      exact hsda
    · have hs' : Umhaengen σ s p y = some yl := by
        have e : Umhaengen σ s p y = σ y := upd_diff σ s y _ heq
        rw [e]; exact hs
      have qda := ih hsda
      exact Erreicht.aufstieg y yl q hs' he qda

/-- U-3, the theorem. Three premises, and the third is the new one:
    `s` is not on `p`'s parent chain. -/
theorem umhaengen_erhaelt (σ : Tabelle) (s p : Nat)
    (hwf : Wohlgeformt σ) (helter : Erreicht σ p)
    (hnicht : ¬ Ueber σ p s) :
    Wohlgeformt (Umhaengen σ s p) := by
  have pneu : Erreicht (Umhaengen σ s p) p :=
    umhaengen_ausserhalb σ s p p helter hnicht
  have swert : Umhaengen σ s p s = some ({ elter := some p } : Slot) :=
    upd_at σ s _
  have sneu : Erreicht (Umhaengen σ s p) s :=
    Erreicht.aufstieg s { elter := some p } p swert rfl pneu
  intro x xl hx
  by_cases heq : x = s
  · rw [heq]
    exact sneu
  · have hx' : σ x = some xl := by
      have e : Umhaengen σ s p x = σ x := upd_diff σ s x _ heq
      rw [e] at hx
      exact hx
    have hr : Erreicht σ x := hwf x xl hx'
    exact umhaengen_durch_s σ s p x hr sneu

/-- What the theorem does NOT require: that the relinked slot is
    occupied. `umhaengen` SETS the slot; on a free `s` it is the same
    as `einfuegen`. The proposed form falls out of the proved one. -/
theorem umhaengen_erhaelt_am_belegten_platz (σ : Tabelle) (s p : Nat)
    (sl : Slot) (hwf : Wohlgeformt σ) (_hbelegt : σ s = some sl)
    (helter : Erreicht σ p) (hnicht : ¬ Ueber σ p s) :
    Wohlgeformt (Umhaengen σ s p) :=
  umhaengen_erhaelt σ s p hwf helter hnicht

/-! ## Part III -- two boundaries, as counterexample -/

/-- Two slots: `0` is the root, `1` hangs below it. -/
def zwei : Tabelle :=
  fun i => if i = 0 then some ({ elter := none } : Slot)
    else if i = 1 then some ({ elter := some 0 } : Slot) else none

theorem zwei_belegt0 : zwei 0 = some ({ elter := none } : Slot) := by
  show (if (0 : Nat) = 0 then (some ({ elter := none } : Slot)) else _) = _
  rw [if_pos rfl]

theorem zwei_belegt1 : zwei 1 = some ({ elter := some 0 } : Slot) := by
  show (if (1 : Nat) = 0 then (some ({ elter := none } : Slot)) else
    if (1 : Nat) = 1 then (some ({ elter := some 0 } : Slot)) else none) = _
  rw [if_neg (by decide), if_pos rfl]

theorem zwei_wohlgeformt : Wohlgeformt zwei := by
  intro s sl hs
  have h0 : Erreicht zwei 0 :=
    Erreicht.wurzel 0 { elter := none } zwei_belegt0 rfl
  by_cases hs0 : s = 0
  · rw [hs0]; exact h0
  · by_cases hs1 : s = 1
    · rw [hs1]
      exact Erreicht.aufstieg 1 { elter := some 0 } 0 zwei_belegt1 rfl h0
    · have hz : zwei s = none := by
        show (if s = 0 then (some ({ elter := none } : Slot)) else
          if s = 1 then (some ({ elter := some 0 } : Slot)) else none) = _
        rw [if_neg hs0, if_neg hs1]
      rw [hz] at hs
      cases hs

/-- Hanging `0` under `1` makes a cycle, and NEITHER reaches a root
    anymore. -/
theorem zyklus_erreicht_nichts (x : Nat)
    (h : Erreicht (Umhaengen zwei 0 1) x) : False := by
  induction h with
  | wurzel s sl hs he =>
    by_cases hs0 : s = 0
    · have e : Umhaengen zwei 0 1 s = some ({ elter := some 1 } : Slot) := by
        rw [hs0]
        exact upd_at zwei 0 _
      rw [e] at hs
      have hsl : ({ elter := some 1 } : Slot) = sl := Option.some_inj.mp hs
      rw [hsl.symm] at he
      have he' : (some (1 : Nat)) = none := he
      cases he'
    · by_cases hs1 : s = 1
      · have e : Umhaengen zwei 0 1 s = some ({ elter := some 0 } : Slot) := by
          have e2 : Umhaengen zwei 0 1 s = zwei s := upd_diff zwei 0 s _ hs0
          rw [e2, hs1]
          exact zwei_belegt1
        rw [e] at hs
        have hsl : ({ elter := some 0 } : Slot) = sl := Option.some_inj.mp hs
        rw [hsl.symm] at he
        have he' : (some (0 : Nat)) = none := he
        cases he'
      · have e : Umhaengen zwei 0 1 s = zwei s := upd_diff zwei 0 s _ hs0
        rw [e] at hs
        have hs' : zwei s = some sl := hs
        show False
        have hz : zwei s = none := by
          show (if s = 0 then (some ({ elter := none } : Slot)) else
            if s = 1 then (some ({ elter := some 0 } : Slot)) else none) = _
          rw [if_neg hs0, if_neg hs1]
        rw [hz] at hs'
        cases hs'
  | aufstieg _ _ _ _ _ _ ih => exact ih

theorem umhaengen_faellt : ¬ Wohlgeformt (Umhaengen zwei 0 1) := by
  intro hw
  have h0 : Umhaengen zwei 0 1 0 = some ({ elter := some 1 } : Slot) :=
    upd_at zwei 0 _
  have hr := hw 0 { elter := some 1 } h0
  exact zyklus_erreicht_nichts 0 hr

/-- G-1: the first two premises of U-3 HOLD at the counterexample. -/
theorem gegenbeispiel_erfuellt_die_alten :
    Wohlgeformt zwei ∧ Erreicht zwei 1 := by
  have h0 : Erreicht zwei 0 :=
    Erreicht.wurzel 0 { elter := none } zwei_belegt0 rfl
  have h1 : Erreicht zwei 1 :=
    Erreicht.aufstieg 1 { elter := some 0 } 0 zwei_belegt1 rfl h0
  exact ⟨zwei_wohlgeformt, h1⟩

/-- G-2: and the third one falls, and only it. -/
theorem gegenbeispiel_verletzt_die_neue : Ueber zwei 1 0 :=
  Ueber.hoeher 1 { elter := some 0 } 0 0 zwei_belegt1 rfl (Ueber.hier 0)

/-- An operation touching only the first carrier. -/
def setze_eins (z : Nat × Nat) : Nat × Nat :=
  (1, z.2)

/-- An invariant of the first carrier alone. -/
def eigen (z : Nat × Nat) : Prop :=
  z.1 ≤ 1

/-- A connecting invariant across carriers. -/
def verbindend (z : Nat × Nat) : Prop :=
  z.1 = z.2

theorem eigen_bleibt (z : Nat × Nat) (h : eigen z) : eigen (setze_eins z) := by
  show (1 : Nat) ≤ 1
  decide

theorem zweiter_traeger_unberuehrt (z : Nat × Nat) :
    (setze_eins z).2 = z.2 := rfl

theorem verbindung_nicht_gedeckt :
    verbindend (0, 0) ∧ ¬ verbindend (setze_eins (0, 0)) := by
  show (0 : Nat) = 0 ∧ ¬ (1 : Nat) = 0
  exact ⟨rfl, by decide⟩

/-! ## Witnesses: the table with one root slot.

`wσ` is occupied exactly at `0` (a root); slot `5` is free. Every
syntax premise fires on it. -/

/-- The witness table: a root at `0`, slot `5` free. -/
def wσ : Tabelle :=
  fun i => if i = 5 then none else some ({ elter := none } : Slot)

theorem wσ_frisch : wσ 5 = none := by
  show (if (5 : Nat) = 5 then (none : Option Slot) else _) = _
  rw [if_pos rfl]

theorem wσ_belegt0 : wσ 0 = some ({ elter := none } : Slot) := by
  show (if (0 : Nat) = 5 then (none : Option Slot) else some { elter := none }) = _
  rw [if_neg (by decide)]

theorem wσ_belegt1 : wσ 1 = some ({ elter := none } : Slot) := by
  show (if (1 : Nat) = 5 then (none : Option Slot) else some { elter := none }) = _
  rw [if_neg (by decide)]

theorem wσ_erreicht0 : Erreicht wσ 0 :=
  Erreicht.wurzel 0 { elter := none } wσ_belegt0 rfl

theorem wσ_erreicht1 : Erreicht wσ 1 :=
  Erreicht.wurzel 1 { elter := none } wσ_belegt1 rfl

theorem wσ_wohlgeformt : Wohlgeformt wσ := by
  intro s sl hs
  by_cases heq : s = 5
  · rw [heq] at hs
    rw [wσ_frisch] at hs
    cases hs
  · have e : wσ s = some ({ elter := none } : Slot) := by
      show (if s = 5 then (none : Option Slot) else some { elter := none }) = _
      rw [if_neg heq]
    exact Erreicht.wurzel s { elter := none } e rfl

theorem wσ_blatt5 : Blatt wσ 5 := by
  intro t tl ht
  by_cases heq : t = 5
  · rw [heq] at ht
    rw [wσ_frisch] at ht
    cases ht
  · have e : wσ t = some ({ elter := none } : Slot) := by
      show (if t = 5 then (none : Option Slot) else some { elter := none }) = _
      rw [if_neg heq]
    rw [e] at ht
    have htl : tl = { elter := none } := (Option.some_inj.mp ht).symm
    rw [htl]
    show (none : Option Nat) ≠ some 5
    decide

/-- Inversion for the witness table: `ueber` collapses to equality --
    relinking can never cycle here. -/
theorem ueber_wσ_inv (x s : Nat) (h : Ueber wσ x s) : x = s := by
  induction h with
  | hier _ => rfl
  | hoeher x xl q s hs he _ _ =>
    by_cases hx : x = 5
    · rw [hx] at hs
      rw [wσ_frisch] at hs
      cases hs
    · have e : wσ x = some ({ elter := none } : Slot) := by
        show (if x = 5 then (none : Option Slot) else some { elter := none }) = _
        rw [if_neg hx]
      rw [e] at hs
      have hxl : xl = { elter := none } := (Option.some_inj.mp hs).symm
      rw [hxl] at he
      have he' : (none : Option Nat) = some q := he
      cases he'

theorem wσ_nueber (q : Nat) (hq : q ≠ 5) : ¬ Ueber wσ q 5 := by
  intro h
  have e := ueber_wσ_inv q 5 h
  exact absurd e hq

theorem erreicht_bleibt_bei_frischem_zeuge :
    Erreicht (upd wσ 5 (some ({ elter := none } : Slot))) 0 :=
  erreicht_bleibt_bei_frischem wσ 5 0 _ wσ_frisch wσ_erreicht0

theorem einfuegen_erhaelt_zeuge : Wohlgeformt (Einfuegen wσ 5 0) :=
  einfuegen_erhaelt wσ 5 0 wσ_wohlgeformt wσ_frisch wσ_erreicht0

theorem erreicht_ohne_blatt_zeuge (hne : 0 ≠ 5) :
    Erreicht (upd wσ 5 none) 0 :=
  erreicht_ohne_blatt wσ 5 0 wσ_blatt5 wσ_erreicht0 hne

theorem blatt_loeschen_erhaelt_zeuge : Wohlgeformt (BlattLoeschen wσ 5) :=
  blatt_loeschen_erhaelt wσ 5 wσ_wohlgeformt wσ_blatt5

theorem umhaengen_ausserhalb_zeuge (hnu : ¬ Ueber wσ 0 5) :
    Erreicht (Umhaengen wσ 5 0) 0 :=
  umhaengen_ausserhalb wσ 5 0 0 wσ_erreicht0 hnu

theorem umhaengen_ausserhalb_belegt_zeuge :
    Erreicht (Umhaengen wσ 5 0) 0 :=
  umhaengen_ausserhalb wσ 5 0 0 wσ_erreicht0 (wσ_nueber 0 (by decide))

theorem umhaengen_durch_s_zeuge (hsneu : Erreicht (Umhaengen wσ 5 0) 5) :
    Erreicht (Umhaengen wσ 5 0) 0 :=
  umhaengen_durch_s wσ 5 0 0 wσ_erreicht0 hsneu

theorem umhaengen_erhaelt_zeuge : Wohlgeformt (Umhaengen wσ 5 0) :=
  umhaengen_erhaelt wσ 5 0 wσ_wohlgeformt wσ_erreicht0
    (wσ_nueber 0 (by decide))

theorem umhaengen_erhaelt_am_belegten_platz_zeuge :
    Wohlgeformt (Umhaengen wσ 0 1) :=
  umhaengen_erhaelt_am_belegten_platz wσ 0 1 { elter := none }
    wσ_wohlgeformt wσ_belegt0 wσ_erreicht1
    (fun h => absurd (ueber_wσ_inv 1 0 h) (by decide))

/-- The witness operation: the identity, with the trivial invariant. -/
theorem folge_erhaelt_zeuge :
    (fun _ : Nat => True)
      (laufen (wirkung := fun (_ : Unit) (z : Nat) => z) ([] : List Unit) 0) :=
  folge_erhaelt (wirkung := fun (_ : Unit) (z : Nat) => z)
    (online := fun (_ : Nat → Prop) => True)
    (je := fun (_ : Unit) (I : Nat → Prop) (_ : True) (z : Nat) (h : I z) => h)
    (I := fun (_ : Nat) => True) ([] : List Unit) 0 trivial trivial

theorem erreichbares_erhaelt_zeuge : (fun _ : Nat => True) 0 :=
  erreichbares_erhaelt (wirkung := fun (_ : Unit) (z : Nat) => z)
    (online := fun (_ : Nat → Prop) => True)
    (je := fun (_ : Unit) (I : Nat → Prop) (_ : True) (z : Nat) (h : I z) => h)
    (I := fun (_ : Nat) => True) 0 0 trivial trivial ⟨[], rfl⟩

end Gabbro.Grammatik.TableOps
