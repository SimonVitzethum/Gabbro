/-
   File:      Grammatik/GabbroV/GvBaum.lean
   Subject:   Agent 04 task V-04c: the `TreeState` projection -- a World's
              tree edges plus occupancy into the abstract structure the
              `GvTreeParent` lemmas consume, lifted along a world run.

   Per-field commutation of the projection with `storeSlot` (on the
   `kantenBild_slotfeld_anders` pattern, reusing the accepted frames
   plus `storeSlot_anders`); run lifts for `benutzt`-preservation,
   `elternKonsistent` and `lokalBenutzt`; the `blatt_loeschen` call
   obligation (`benutzt(opfer)` for the reached victim) as a theorem
   from per-call contracts plus the initial state, with the
   reachability-monotonicity link stated as an explicit premise (it
   holds for relink shapes, fails for naive clears -- see the planted
   failure). Witness: a real leaf deletion on a concrete 3-node tree;
   planted failure: deleting a non-leaf is not covered.
-/
import Grammatik.Kern.Semantik.Semantik
import Grammatik.GabbroV.GvTreeParent
import Grammatik.GabbroV.GvStore
import Grammatik.GabbroV.GvVerkettung

namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik
open Gabbro.Grammatik.X86

variable {D : Deklaration}

/-! ## Fixture: three edge fields plus occupancy -/

/-- Parent, child, sibling edges plus the occupancy flag. -/
inductive BaumFeld | Elter | Kind | Naechstes | Belegt deriving DecidableEq

/-- Minimal declaration in the `swD`/`kettenD` shape: one unshared
    table with 3 slots, three `option index` edge fields and one bool
    occupancy field; everything else empty. -/
def baumD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 3
  Feld := fun _ => BaumFeld
  decFeld := fun _ => inferInstance
  typ := fun _ f => match f with
    | .Elter => .opt 3
    | .Kind => .opt 3
    | .Naechstes => .opt 3
    | .Belegt => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun g => nomatch g
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ g => nomatch g
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-! ## Occupancy projection and the `TreeState` record -/

/-- Occupancy read through a bool field. -/
def belegtBild (D : Deklaration) (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .bool) : Nat → Bool :=
  fun k => wahr? (hf ▸ σ.slots t k f : Wert D .bool)

/-- Occupancy commutes with a foreign-table store, pointwise. -/
theorem belegtBild_tabelle_anders (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .bool) (j : Nat)
    (t₀ : D.Tab) (k₀ : Int) (f₀ : D.Feld t₀) (v : Wert D (D.typ t₀ f₀))
    (h : t₀ ≠ t) :
    belegtBild D (σ.storeSlot t₀ k₀ f₀ v) t f hf j
      = belegtBild D σ t f hf j := by
  have hfr : (σ.storeSlot t₀ k₀ f₀ v).slots t j f = σ.slots t j f :=
    seite_rahmen_fremd σ (Ne.symm h) k₀ j f₀ v f
  simp only [belegtBild, hfr]

/-- Occupancy commutes with a same-table store elsewhere, pointwise:
    another slot, or another field at any slot. -/
theorem belegtBild_slotfeld_anders (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .bool) (j : Nat)
    (k₀ : Int) (f₀ : D.Feld t) (v : Wert D (D.typ t f₀))
    (h : (j : Int) ≠ k₀ ∨ f₀ ≠ f) :
    belegtBild D (σ.storeSlot t k₀ f₀ v) t f hf j
      = belegtBild D σ t f hf j := by
  have h' : (j : Int) ≠ k₀ ∨ f ≠ f₀ := by
    cases h with
    | inl hkj => exact Or.inl hkj
    | inr hfj => exact Or.inr (Ne.symm hfj)
  have hfr : (σ.storeSlot t k₀ f₀ v).slots t j f = σ.slots t j f :=
    storeSlot_anders σ t k₀ f₀ v j f h'
  simp only [belegtBild, hfr]

/-! ## The `TreeState` record projection -/

/-- The full `TreeState` of one table: slot count, the three edge maps
    as `Nat` maps, occupancy. The per-field commutations above (plus
    the `kantenBild` pair) are its commutation, component by component;
    no separate record-equality wrapper is stated. -/
def baumBild (D : Deklaration) (σ : World D) (t : D.Tab)
    (fp fc fs : D.Feld t)
    (hfP : D.typ t fp = .opt (D.count t))
    (hfC : D.typ t fc = .opt (D.count t))
    (hfS : D.typ t fs = .opt (D.count t))
    (fb : D.Feld t) (hfb : D.typ t fb = .bool) : TreeState where
  n := (D.count t).toNat
  parent := fun k => match kantenBild D σ t fp hfP k with
    | none => none
    | some z => some z.n.toNat
  child := fun k => match kantenBild D σ t fc hfC k with
    | none => none
    | some z => some z.n.toNat
  sibling := fun k => match kantenBild D σ t fs hfS k with
    | none => none
    | some z => some z.n.toNat
  benutzt := belegtBild D σ t fb hfb

/-! ## Nat-level chain maps and the frame helper -/

/-- Edge map at `Nat` indices (slots are `Int` in `World`). -/
def kanteNat (D : Deklaration) (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .opt (D.count t)) : Nat → Option Nat :=
  fun k => match kantenBild D σ t f hf k with
    | none => none
    | some z => some z.n.toNat

/-- Reachability from `s` with the slot count as fuel (the `reaches`
    convention). -/
def erreichtProj (D : Deklaration) (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .opt (D.count t)) (s d : Nat) : Bool :=
  ketteNext (kanteNat D σ t f hf) (D.count t).toNat s d

/-- Frame along a run: a slot no victim touches keeps its occupancy.
    One reverted bound, induction on the steps (the `Table_Zaehlung`
    pattern: the hypothesis comes first). -/
theorem frame_ausser_opfer (t : D.Tab) (fb : D.Feld t)
    (hfb : D.typ t fb = .bool)
    (lauf : Nat → World D) (opfer : Nat → Nat)
    (hfrisch : ∀ i d, d ≠ opfer i →
      belegtBild D (lauf (i + 1)) t fb hfb d
        = belegtBild D (lauf i) t fb hfb d)
    (i : Nat) (d : Nat) (hd : ∀ j, j < i → d ≠ opfer j) :
    belegtBild D (lauf i) t fb hfb d
      = belegtBild D (lauf 0) t fb hfb d := by
  revert hd
  induction i with
  | zero =>
      intro hd
      rfl
  | succ m ih =>
      intro hd
      have h0 : belegtBild D (lauf (m + 1)) t fb hfb d
          = belegtBild D (lauf m) t fb hfb d :=
        hfrisch m d (hd m (by omega))
      have hm : ∀ j, j < m → d ≠ opfer j := by
        intro j hj
        exact hd j (by omega)
      have ihm := ih hm
      rw [h0]
      exact ihm

/-! ## Run lifts: frame first, then links -/

/-- Lift along a world run: a per-step preserved `Bool` property holds
    at every step. The per-step preservation is the premise -- for link
    agreement that preservation is the open relink work (rule 14:
    recorded, not assumed). -/
theorem weltEigenschaft_bleibt (eig : World D → Bool)
    (lauf : Nat → World D) (n : Nat)
    (hschritt : ∀ i, i < n → eig (lauf i) = true → eig (lauf (i + 1)) = true)
    (i : Nat) (hi : i ≤ n)
    (h0 : eig (lauf 0) = true) :
    eig (lauf i) = true := by
  revert hi
  induction i with
  | zero =>
      intro hi
      exact h0
  | succ m ih =>
      intro hi
      have hilt : m < n := by omega
      have hle : m ≤ n := by omega
      exact hschritt m hilt (ih hle)

/-- `elternKonsistent` lifts along a run whose steps preserve it. -/
theorem elternKonsistent_bleibt (t : D.Tab)
    (fp fc fs : D.Feld t)
    (hfP : D.typ t fp = .opt (D.count t))
    (hfC : D.typ t fc = .opt (D.count t))
    (hfS : D.typ t fs = .opt (D.count t))
    (fb : D.Feld t) (hfb : D.typ t fb = .bool)
    (lauf : Nat → World D) (n : Nat)
    (hschritt : ∀ i, i < n →
      elternKonsistent (baumBild D (lauf i) t fp fc fs hfP hfC hfS fb hfb) = true →
      elternKonsistent (baumBild D (lauf (i + 1)) t fp fc fs hfP hfC hfS fb hfb) = true)
    (i : Nat) (hi : i ≤ n)
    (h0 : elternKonsistent (baumBild D (lauf 0) t fp fc fs hfP hfC hfS fb hfb) = true) :
    elternKonsistent (baumBild D (lauf i) t fp fc fs hfP hfC hfS fb hfb) = true :=
  weltEigenschaft_bleibt
    (fun σ => elternKonsistent (baumBild D σ t fp fc fs hfP hfC hfS fb hfb))
    lauf n hschritt i hi h0

/-- `lokalBenutzt` lifts along a run whose steps preserve it. -/
theorem lokalBenutzt_bleibt (t : D.Tab)
    (fp fc fs : D.Feld t)
    (hfP : D.typ t fp = .opt (D.count t))
    (hfC : D.typ t fc = .opt (D.count t))
    (hfS : D.typ t fs = .opt (D.count t))
    (fb : D.Feld t) (hfb : D.typ t fb = .bool)
    (lauf : Nat → World D) (n : Nat)
    (hschritt : ∀ i, i < n →
      lokalBenutzt (baumBild D (lauf i) t fp fc fs hfP hfC hfS fb hfb) = true →
      lokalBenutzt (baumBild D (lauf (i + 1)) t fp fc fs hfP hfC hfS fb hfb) = true)
    (i : Nat) (hi : i ≤ n)
    (h0 : lokalBenutzt (baumBild D (lauf 0) t fp fc fs hfP hfC hfS fb hfb) = true) :
    lokalBenutzt (baumBild D (lauf i) t fp fc fs hfP hfC hfS fb hfb) = true :=
  weltEigenschaft_bleibt
    (fun σ => lokalBenutzt (baumBild D σ t fp fc fs hfP hfC hfS fb hfb))
    lauf n hschritt i hi h0

/-! ## The call obligation, conditionally: victim stays occupied -/

/-- The `blatt_loeschen(opfer)` obligation as a theorem: at step `i`
    the reached victim is occupied -- from initial occupancy of the
    victims, the traverse reaching each victim now, victim-scoped
    reachability monotonicity, the frame (only the victim loses
    occupancy), and fresh victims. What is NOT shown: the link itself
    (`hverb` -- true for relink shapes, false for naive clears) and
    the store-level relink preservation. Leaf-ness is not among the
    premises: the occupancy obligation does not need it (it governs
    progress, not the call precondition -- see the planted failure). -/
theorem blatt_rufsicher_bedingt (t : D.Tab)
    (fr : D.Feld t) (hfr : D.typ t fr = .opt (D.count t))
    (fb : D.Feld t) (hfb : D.typ t fb = .bool)
    (lauf : Nat → World D) (opfer : Nat → Nat) (n wurzel : Nat)
    (hinit : ∀ i, i < n →
      erreichtProj D (lauf 0) t fr hfr wurzel (opfer i) = true →
      belegtBild D (lauf 0) t fb hfb (opfer i) = true)
    (hopfer : ∀ i, i < n →
      erreichtProj D (lauf i) t fr hfr wurzel (opfer i) = true)
    (hverb : ∀ i, i < n →
      erreichtProj D (lauf i) t fr hfr wurzel (opfer i) = true →
      erreichtProj D (lauf 0) t fr hfr wurzel (opfer i) = true)
    (hfrisch : ∀ i d, d ≠ opfer i →
      belegtBild D (lauf (i + 1)) t fb hfb d
        = belegtBild D (lauf i) t fb hfb d)
    (hneu : ∀ a b, a < n → b < a → opfer a ≠ opfer b)
    (i : Nat) (hi : i < n) :
    belegtBild D (lauf i) t fb hfb (opfer i) = true := by
  have hreach0 : erreichtProj D (lauf 0) t fr hfr wurzel (opfer i) = true :=
    hverb i hi (hopfer i hi)
  have hben0 : belegtBild D (lauf 0) t fb hfb (opfer i) = true :=
    hinit i hi hreach0
  have hfrisch_i : ∀ j, j < i → opfer i ≠ opfer j := by
    intro j hj
    exact hneu i j hi hj
  have hframe := frame_ausser_opfer t fb hfb lauf opfer hfrisch i (opfer i) hfrisch_i
  exact hframe.trans hben0

/-! ## Witness: leaf-first deletion on a three-node tree -/

/-- Field equations of the fixture, by computation. -/
theorem hfNaechstes : baumD.typ () .Naechstes = .opt (baumD.count ()) := rfl
theorem hfBelegt : baumD.typ () .Belegt = .bool := rfl
theorem hfKind : baumD.typ () .Kind = .opt (baumD.count ()) := rfl

/-- Three-node tree: sibling chain 0 → 1 → 2, back-pointers, first
    child 0 → 1, all occupied. Nodes 1 and 2 are leaves. -/
def baumWelt : World baumD :=
  { slots := fun _ k f =>
      match f with
      | .Elter =>
        match k with
        | 1 => some ⟨0, by decide, by decide⟩
        | 2 => some ⟨1, by decide, by decide⟩
        | _ => none
      | .Kind =>
        match k with
        | 0 => some ⟨1, by decide, by decide⟩
        | _ => none
      | .Naechstes =>
        match k with
        | 0 => some ⟨1, by decide, by decide⟩
        | 1 => some ⟨2, by decide, by decide⟩
        | _ => none
      | .Belegt => true
    globs := fun g => nomatch g
    spur := [] }

/-- Step worlds: delete leaf 2 (clear + unlink), then leaf 1. -/
def baumWelt1 : World baumD :=
  ((baumWelt.storeSlot () 2 .Belegt false).storeSlot () 1 .Naechstes none).storeSlot
    () 2 .Elter none

def baumWelt2 : World baumD :=
  ((baumWelt1.storeSlot () 1 .Belegt false).storeSlot () 0 .Naechstes none).storeSlot
    () 1 .Elter none

/-- The leaf-first run: victims 2, then 1. -/
def baumLauf : Nat → World baumD
  | 0 => baumWelt
  | 1 => baumWelt1
  | _ => baumWelt2

def baumOpfer : Nat → Nat
  | 0 => 2
  | _ => 1

/-- Field disequalities of the fixture, by constructor discrimination. -/
theorem naechstes_ne_belegt : BaumFeld.Naechstes ≠ BaumFeld.Belegt :=
  fun h => BaumFeld.noConfusion h

theorem elter_ne_belegt : BaumFeld.Elter ≠ BaumFeld.Belegt :=
  fun h => BaumFeld.noConfusion h

/-- Step contract of the witness run: only the victim loses occupancy
    (the three stores per step, each framed elsewhere). -/
theorem baumLauf_schritt : ∀ i d, d ≠ baumOpfer i →
    belegtBild baumD (baumLauf (i + 1)) () .Belegt hfBelegt d
      = belegtBild baumD (baumLauf i) () .Belegt hfBelegt d := by
  intro i d hne
  have hi2 : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
  cases hi2 with
  | inl h =>
      subst h
      have hne2 : d ≠ 2 := hne
      have hneI : (d : Int) ≠ 2 := by omega
      have e1 := belegtBild_slotfeld_anders baumWelt () BaumFeld.Belegt hfBelegt d
        2 BaumFeld.Belegt false (Or.inl hneI)
      have e2 := belegtBild_slotfeld_anders
        (baumWelt.storeSlot () 2 BaumFeld.Belegt false) () BaumFeld.Belegt hfBelegt d
        1 BaumFeld.Naechstes none (Or.inr naechstes_ne_belegt)
      have e3 := belegtBild_slotfeld_anders
        ((baumWelt.storeSlot () 2 BaumFeld.Belegt false).storeSlot () 1 BaumFeld.Naechstes none)
        () BaumFeld.Belegt hfBelegt d 2 BaumFeld.Elter none (Or.inr elter_ne_belegt)
      simp only [baumLauf, baumWelt1]
      rw [e3, e2, e1]
  | inr h =>
      cases h with
      | inl h =>
          subst h
          have hne2 : d ≠ 1 := hne
          have hneI : (d : Int) ≠ 1 := by omega
          have e1 := belegtBild_slotfeld_anders baumWelt1 () BaumFeld.Belegt hfBelegt d
            1 BaumFeld.Belegt false (Or.inl hneI)
          have e2 := belegtBild_slotfeld_anders
            (baumWelt1.storeSlot () 1 BaumFeld.Belegt false) () BaumFeld.Belegt hfBelegt d
            0 BaumFeld.Naechstes none (Or.inr naechstes_ne_belegt)
          have e3 := belegtBild_slotfeld_anders
            ((baumWelt1.storeSlot () 1 BaumFeld.Belegt false).storeSlot () 0 BaumFeld.Naechstes none)
            () BaumFeld.Belegt hfBelegt d 1 BaumFeld.Elter none (Or.inr elter_ne_belegt)
          simp only [baumLauf, baumWelt2]
          rw [e3, e2, e1]
      | inr h =>
          have hm2 : ∀ m, baumLauf (m + 3) = baumWelt2 := by
            intro m
            simp [baumLauf]
          have hm1 : ∀ m, baumLauf (m + 2) = baumWelt2 := by
            intro m
            simp [baumLauf]
          obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
          rw [hm2 m, hm1 m]

/-- Fresh victims: 2 then 1. -/
theorem baumOpfer_neu : ∀ a b, a < 2 → b < a → baumOpfer a ≠ baumOpfer b := by
  intro a b ha hb
  have ha2 : a = 0 ∨ a = 1 := by omega
  cases ha2 with
  | inl h =>
      subst h
      omega
  | inr h =>
      subst h
      have hb0 : b = 0 := by omega
      subst hb0
      decide

/-- Initial occupancy of the victims. -/
theorem baumAnfang : ∀ i, i < 2 →
    erreichtProj baumD (baumLauf 0) () .Naechstes hfNaechstes 0 (baumOpfer i) = true →
    belegtBild baumD (baumLauf 0) () .Belegt hfBelegt (baumOpfer i) = true := by
  intro i hi _
  have hi2 : i = 0 ∨ i = 1 := by omega
  cases hi2 with
  | inl h => subst h; decide
  | inr h => subst h; decide

/-- The traverse reaches each victim in time. -/
theorem baumErreicht : ∀ i, i < 2 →
    erreichtProj baumD (baumLauf i) () .Naechstes hfNaechstes 0 (baumOpfer i)
      = true := by
  intro i hi
  have hi2 : i = 0 ∨ i = 1 := by omega
  cases hi2 with
  | inl h => subst h; decide
  | inr h => subst h; decide

/-- Victim reachability is monotone here (pure removal, no new edges). -/
theorem baumBleibt : ∀ i, i < 2 →
    erreichtProj baumD (baumLauf i) () .Naechstes hfNaechstes 0 (baumOpfer i)
      = true →
    erreichtProj baumD (baumLauf 0) () .Naechstes hfNaechstes 0 (baumOpfer i)
      = true := by
  intro i hi hr
  have hi2 : i = 0 ∨ i = 1 := by omega
  cases hi2 with
  | inl h => subst h; exact hr
  | inr h => subst h; decide

/-- Witness (non-degenerate): after the real leaf-first deletion the
    victim is still occupied at call time -- per-call contracts plus
    the initial state, no unrolling. -/
theorem baumBlatt_zeuge :
    belegtBild baumD (baumLauf 1) () .Belegt hfBelegt (baumOpfer 1) = true :=
  blatt_rufsicher_bedingt () BaumFeld.Naechstes hfNaechstes BaumFeld.Belegt hfBelegt
    baumLauf baumOpfer 2 0 baumAnfang baumErreicht baumBleibt
    baumLauf_schritt baumOpfer_neu 1 (by omega)

/-- The root has a child: deleting it first is a non-leaf deletion. -/
theorem baumWurzel_hat_kind :
    ((kantenBild baumD baumWelt () .Kind hfKind 0).map Zahl.n) = some 1 := by
  decide

/-- Non-leaf-first run: victim 0 (cutting off the subtree), then 1. -/
def laufB : Nat → World baumD
  | 0 => baumWelt
  | 1 => ((baumWelt.storeSlot () 0 .Belegt false).storeSlot () 0 .Naechstes none).storeSlot
    () 0 .Kind none
  | _ => ((baumWelt.storeSlot () 0 .Belegt false).storeSlot () 0 .Naechstes none).storeSlot
    () 0 .Kind none

/-- Planted failure: after cutting the root, node 1 is unreachable --
    the traverse cannot reach its next victim, so the call obligation
    has no premise to fire on. A deletion of a non-leaf is not covered. -/
theorem baumSchnitt_widerlegt :
    erreichtProj baumD (laufB 1) () .Naechstes hfNaechstes 0 1 = false := by
  decide

/-
   CUTS: what is not proved.
   - Proved: `baumD` (3 slots, 3 edge fields + occupancy); occupancy
     commutation both shapes; the `TreeState` record `baumBild`; the
     frame-lift `frame_ausser_opfer`; the generic run lift with link
     corollaries; the conditional call obligation
     (`blatt_rufsicher_bedingt`); the leaf-first witness
     (`baumBlatt_zeuge`: victim occupied at call time) and the
     non-leaf planted failure (`baumSchnitt_widerlegt`: cutoff victim
     unreachable, plus `baumWurzel_hat_kind` recording the non-leaf).
   - Only stated: `baumWelt`/`baumLauf`/`laufB` fixture shapes.
   - Not modelled: per-step `elternKonsistent` preservation across
     relink stores (the open relink work -- the lifts take it as an
     explicit premise); runs past the contract bound in one go;
     `GvTraversal`/`GvSplits`/`GvParserFragment` reconciliation.
   - No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere; every
     premise is used; no premise has type `Prop` itself.
-/

#print axioms frame_ausser_opfer
#print axioms blatt_rufsicher_bedingt
#print axioms baumBlatt_zeuge

end Gabbro.Grammatik.GabbroV
