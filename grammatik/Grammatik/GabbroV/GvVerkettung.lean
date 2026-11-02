/-
   File:      Grammatik/GabbroV/GvVerkettung.lean
   Subject:   Agent 04 follow-up: the person's linked-structure arguments
              (TODO 0f; `01-tabelle`, `55-kindkette`, `F01`, `kapraum`;
              `programmlogik/PLAN.md` 5.1).

   Per unit, the person owes a `reaches`-invariant across a relink (PLAN
   5.1); the GvTreeParent decision (NO: `deklaration_schliesst_eltern_nicht`,
   `deklaration_schliesst_benutzt_nicht`) shows the declaration does not
   give it. Lemma (a) below is the walk bound every `traverse` domain
   needs; lemma (b) is pop-preserves-acyclicity for free lists.
-/
module
public import Grammatik.GabbroV.GvVerkettungBasis
import all Grammatik.GabbroV.GvVerkettungBasis
public import Grammatik.GabbroV.GvTreeParent
@[expose] public section


namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik.GabbroV

/-- Acyclic below `n`: no slot leads back to itself. Fuel `n` matches
    the `reaches` convention (`Semantik.lean:262`); cycle completeness
    past fuel `n` is NOT proved (see CUTS). -/
def ketteAzyklisch (nxt : Nat → Option Nat) (n : Nat) : Bool :=
  alleUnter (fun s =>
    match nxt s with
    | none => true
    | some m => ((ketteNext nxt n m s) == false)) n

/-- Pop at `h`: clear `h`'s edge. A free-list pop takes the head out of
    the chain; the head pointer move itself is bookkeeping outside the
    edge map. -/
def kettePop (nxt : Nat → Option Nat) (h : Nat) : Nat → Option Nat
  | j => if j = h then none else nxt j

/-- Edge removal simulates backwards: every post-pop path is a pre-pop
    path, at the same fuel. -/
theorem kettePop_simuliert (nxt : Nat → Option Nat) (h : Nat)
    (fuel a d : Nat)
    (hp : ketteNext (kettePop nxt h) fuel a d = true) :
    ketteNext nxt fuel a d = true := by
  induction fuel generalizing a with
  | zero =>
      simpa [ketteNext] using hp
  | succ fuel ih =>
      by_cases heq : a = d
      · subst heq
        exact ketteNext_refl nxt _ _
      · rw [ketteNext_schritt _ _ _ _ heq] at hp
        cases hpa : kettePop nxt h a with
        | none => simp only [hpa, Bool.false_eq_true] at hp
        | some m =>
            have hrest : ketteNext (kettePop nxt h) fuel m d = true := by
              rw [hpa] at hp
              exact hp
            by_cases hah : a = h
            · subst hah
              simp only [kettePop, ↓reduceIte, reduceCtorEq] at hpa
            · have hold : nxt a = some m := by
                simpa [kettePop, if_neg hah] using hpa
              rw [ketteNext_schritt nxt _ _ _ heq, hold]
              exact ih m hrest

/-- Free-list pop keeps acyclicity. The `release_slot`/clear half of
    `F01.gab:302-305` and `kapraum.gab:108-113`: clearing edges cannot
    close a cycle. -/
theorem kettePop_erhaelt_azyklisch (nxt : Nat → Option Nat) (n h : Nat)
    (hazy : ketteAzyklisch nxt n = true) :
    ketteAzyklisch (kettePop nxt h) n = true := by
  simp only [ketteAzyklisch, alleUnter] at hazy ⊢
  apply alleAb_voll
  intro s hs0 hsn
  cases hns : nxt s with
  | none =>
      have hpop : kettePop nxt h s = none := by
        simp only [kettePop]
        by_cases hsh2 : s = h
        · rw [if_pos hsh2]
        · rw [if_neg hsh2, hns]
      rw [hpop]
  | some m' =>
      have hold : ((ketteNext nxt n m' s) == false) = true := by
        have hmem := alleAb_gilt _ 0 n s hazy (Nat.zero_le s) hsn
        rw [hns] at hmem
        exact hmem
      by_cases hsh : s = h
      · have hpop : kettePop nxt h s = none := by
          simp only [kettePop]
          rw [if_pos hsh]
        rw [hpop]
      · have hpop : kettePop nxt h s = some m' := by
          simp only [kettePop]
          rw [if_neg hsh]
          exact hns
        by_cases hw : ketteNext (kettePop nxt h) n m' s = true
        · have hold2 := kettePop_simuliert nxt h n m' s hw
          rw [hold2] at hold
          simp only [beq_false, Bool.not_true, Bool.false_eq_true] at hold
        · have hneg : ((ketteNext (kettePop nxt h) n m' s) == false) = true := by
            simp only [hw, BEq.rfl]
          simpa [hpop] using hneg

/-! ## Witnesses: three slots, a cycle, an escape -/

/-- Three-slot chain 0 → 1 → 2 → end. Non-degenerate: every edge bound,
    the walk stops exactly at fuel 3. -/
def kette3 : Nat → Option Nat
  | 0 => some 1
  | 1 => some 2
  | _ => none

/-- Two-cycle 0 → 1 → 0. Non-degenerate cyclic fixture: the walk never
    stops, positions repeat below 2. -/
def ring2 : Nat → Option Nat
  | 0 => some 1
  | 1 => some 0
  | _ => none

/-- Escaping chain 0 → 1 → 2 → 99. The range premise fails at slot 2;
    the walk leaves the table. -/
def flucht : Nat → Option Nat
  | 0 => some 1
  | 1 => some 2
  | 2 => some 99
  | _ => none

/-- All edges inside range: the `hrand` premise of `kette_schranke`
    as a `Bool`. -/
def randOk (nxt : Nat → Option Nat) (n : Nat) : Bool :=
  alleUnter (fun j =>
    match nxt j with
    | none => true
    | some m => decide (m < n)) n

/-- Witness (bound, stop half): the three-chain ends at fuel 3. -/
theorem kette3_endet : geh kette3 3 0 = none := by decide

/-- Witness (bound, range premise holds on the fixture). -/
theorem kette3_innen : randOk kette3 3 = true := by decide

/-- Witness (bound, repeat half): the cycle repeats a slot below 2. -/
theorem ring2_wiederholt :
    wert ring2 2 0 0 = wert ring2 2 0 2 ∧ wert ring2 2 0 0 < 2 := by
  decide

/-- Planted failure (bound): without the range premise the walk escapes
    the table -- `randOk` is false and position 3 is out of range. -/
theorem flucht_ausserhalb : randOk flucht 3 = false := by decide

/-- Planted failure (bound): the escaping walk reaches slot 99. -/
theorem flucht_entweicht : geh flucht 3 0 = some 99 := by decide

/-- Witness (acyclicity): the three-chain is acyclic. -/
theorem kette3_azyklisch : ketteAzyklisch kette3 3 = true := by decide

/-- Witness (pop): popping the head keeps the three-chain acyclic --
    the `release_slot` shape of `F01.gab:308-320`. -/
theorem kette3_pop_azyklisch :
    ketteAzyklisch (kettePop kette3 0) 3 = true := by decide

/-- Planted failure (acyclicity): the two-cycle is cyclic -- the
    predicate bites, so the pop lemma is not vacuous. -/
theorem ring2_zyklisch : ketteAzyklisch ring2 2 = false := by decide

/-! ## Generic use: the Bool shadow discharges the premise -/

/-- Bridge: a true `randOk` gives the range premise `hrand` for every
    slot. This is what makes `kette_schranke` reusable: check `randOk`
    by `decide`, get `hrand` for free. -/
theorem randOk_gibt_hrand (nxt : Nat → Option Nat) (n : Nat)
    (h : randOk nxt n = true) :
    ∀ j, j < n → ∀ m, nxt j = some m → m < n := by
  intro j hjn m hjm
  have hmem : (match nxt j with
      | none => true
      | some mm => decide (mm < n)) = true := by
    have hall := h
    simp only [randOk, alleUnter] at hall
    have halle := alleAb_gilt _ 0 n j hall (Nat.zero_le j) (by omega)
    exact halle
  rw [hjm] at hmem
  exact of_decide_eq_true hmem

/-- Witness (`kette_schranke` at work): on the three-chain every premise
    discharges -- `0 < 3` by `decide`, `hrand` by the bridge from the
    checked `kette3_innen` -- and the stop disjunct fires. -/
theorem kette_schranke_zeuge :
    (∃ k, k ≤ 3 ∧ geh kette3 k 0 = none) ∨
      (∃ i j, i < j ∧ j ≤ 3 ∧
        wert kette3 3 0 i = wert kette3 3 0 j ∧ wert kette3 3 0 i < 3) :=
  kette_schranke kette3 3 0 (by decide)
    (randOk_gibt_hrand kette3 3 kette3_innen)

/-- Witness (`kettePop_erhaelt_azyklisch` at work): popping the head of
    the three-chain keeps it acyclic, from the checked `kette3_azyklisch`. -/
theorem kettePop_erhaelt_azyklisch_zeuge :
    ketteAzyklisch (kettePop kette3 0) 3 = true :=
  kettePop_erhaelt_azyklisch kette3 3 0 kette3_azyklisch

/-- Witness (`schubladenSatz` at work): three values below two repeat. -/
theorem schubladenSatz_zeuge :
    ∃ i j, i < j ∧ j < 2 + 1 ∧
      (fun k => if k = 2 then 0 else k) i =
      (fun k => if k = 2 then 0 else k) j :=
  schubladenSatz _ 2 (by
    intro k hk
    have h3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    cases h3 with
    | inl h => simp only [h, reduceCtorEq, ↓reduceIte, Nat.zero_lt_succ]
    | inr h =>
        cases h with
        | inl h => simp only [h, Nat.reduceEqDiff, ↓reduceIte, Nat.lt_add_one]
        | inr h => simp only [h, ↓reduceIte, Nat.zero_lt_succ])

/-- Witness (`geh_bereich` at work): two steps from 0 stay below 3. -/
theorem geh_bereich_zeuge : 2 < 3 :=
  geh_bereich kette3 3 0 (by decide)
    (randOk_gibt_hrand kette3 3 kette3_innen) 2 2 (by decide)

/-
   CUTS: what is not proved.
   - Proved here: the drawer principle (`schubladenSatz`); the walk bound
     (`kette_schranke`: `n + 1` positions in `n` slots stop or repeat, from
     an in-range start over in-range edges); pop preserves acyclicity
     (`kettePop_erhaelt_azyklisch` via the edge-subset simulation
     `kettePop_simuliert`). Witnesses: an ending walk, a repeating cycle
     and an escaping walk (`kette3_endet`, `ring2_wiederholt`,
     `flucht_ausserhalb`, `flucht_entweicht`); an acyclic chain, its pop
     and a detected cycle (`kette3_azyklisch`, `kette3_pop_azyklisch`,
     `ring2_zyklisch`).
   - Only stated: `ketteAzyklisch` with fuel `n` (cycle completeness past
     fuel `n` is not proved); `randOk` as the `hrand` shadow.
   - Not modelled: the projection `World -> (nxt, n)` is documented, not
     formalised (no simulation theorem between `Semantik.kette`/
     `Expr.reaches` and `ketteNext`/`geh`); the per-unit
     reaches-across-relink goals of PLAN 5.1 need the store model and are
     NOT closed by these two lemmas (see REPORT-04.md: no unit fully
     closed; `kette_schranke` closes only the termination/bound half of
     the `traverse` domains, `kettePop_erhaelt_azyklisch` only the
     edge-clearing acyclicity half).
   - No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere; every
     premise is used; no premise has type `Prop` itself. The classical
     `by_cases` on undecidable existentials is the standard
     `Classical.choice` (see `#print axioms`).
-/

#print axioms schubladenSatz
#print axioms kette_schranke
#print axioms ketteNext_mono
#print axioms kettePop_simuliert
#print axioms kettePop_erhaelt_azyklisch
#print axioms randOk_gibt_hrand
#print axioms kette_schranke_zeuge
#print axioms kettePop_erhaelt_azyklisch_zeuge
#print axioms schubladenSatz_zeuge

end Gabbro.Grammatik.GabbroV
