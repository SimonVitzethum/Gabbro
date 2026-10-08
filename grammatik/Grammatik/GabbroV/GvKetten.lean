/-
   File:      Grammatik/GabbroV/GvKetten.lean
   Subject:   Agent 04 follow-up-3: generic call chains (TODO 0f;
              `beispiele/147`, `148` `tick_runde`: 64 unrolled calls neither
              twelve `gabbro_calls` rounds nor three passes instantiate)
              and disjunctive callee posts (`beispiele/126`, 94 goals).

   (a) `rufKette_invariant`: one uniform contract per call, induction over
   the chain length -- no unrolling. `tick_runde_zeuge` runs it on the
   64-round shape. (b) `disjunkt_einmal`: a disjunctive callee post
   discharged by one case analysis, not per goal (the `sortiere` shape:
   five `ordne` calls branching on the comparator answer).

   Model: calls as data (`RufKette`: length, precondition map, step
   map) over an abstract state type `S` (`Nat` counters here, `Zahl`
   cell values and worlds in `GvStore`); bridging a concrete unit's
   stores to `vor`/`nach` is open, see CUTS). Agent 05's
   `GvSplits.lean` analysis is not in this clone (unmerged upstream,
   fetch forbidden), so (b) is built from the task text and `126` alone.
-/

namespace Gabbro.Grammatik.GabbroV

/-- A call chain as data: length, per-call precondition map, per-call
    step map over abstract states. `tick_runde` is `n = 64` with one
    uniform contract; V-04 instantiates `S` with cell values. -/
structure RufKette (S : Type) where
  n : Nat
  vor : Nat → S → Bool
  nach : Nat → S → S

/-- Run `fuel` calls from index `i` and state `s`. -/
def rufLauf {S : Type} (c : RufKette S) : Nat → Nat → S → S
  | 0, _, s => s
  | fuel + 1, i, s => rufLauf c fuel (i + 1) (c.nach i s)

/-- Generic call-chain invariant: one uniform contract per call --
    from every invariant state each call may run and keeps the
    invariant -- carries the invariant across `fuel` calls by induction
    on the chain, not by unrolling. One application replaces `fuel`
    `gabbro_calls` rounds. Polymorphic in the state type: `Nat`
    counters below, `World` cells and `Zahl` values in `GvStore`. -/
theorem rufKette_invariant {S : Type} (c : RufKette S) (inv : S → Bool)
    (herh : ∀ k s, k < c.n → inv s = true →
      c.vor k s = true ∧ inv (c.nach k s) = true)
    (fuel i : Nat) (s : S) (hi : i + fuel ≤ c.n) (hs : inv s = true) :
    inv (rufLauf c fuel i s) = true := by
  induction fuel generalizing i s with
  | zero =>
      simpa [rufLauf] using hs
  | succ fuel ih =>
      have hilt : i < c.n := by omega
      have hstep := herh i s hilt hs
      have hfu : i + 1 + fuel ≤ c.n := by omega
      exact ih (i + 1) (c.nach i s) hfu hstep.2

/-- Last step first: running `i + 1` calls from `j` is the first `i`
    calls followed by call `j + i`. Fuel arithmetic by `omega`. -/
theorem rufLauf_letzter {S : Type} (c : RufKette S) (i j : Nat) (s : S) :
    rufLauf c (i + 1) j s = c.nach (j + i) (rufLauf c i j s) := by
  induction i generalizing j s with
  | zero =>
      simp [rufLauf]
  | succ i ih =>
      have hstep : rufLauf c (i + 1 + 1) j s
          = rufLauf c (i + 1) (j + 1) (c.nach j s) := rfl
      rw [hstep, ih (j + 1) (c.nach j s)]
      have hX : rufLauf c (i + 1) j s = rufLauf c i (j + 1) (c.nach j s) := rfl
      have hix : j + 1 + i = j + (i + 1) := by omega
      rw [hix, hX]

/-! ## The tick-round shape: 64 uniform round ticks -/

/-- Precondition map of the round fixture: every round may run below 16. -/
def rundeVor : Nat → Nat → Bool
  | _, s => decide (s < 16)

/-- Step map of the round fixture: advance the round modulo 16. -/
def rundeNach : Nat → Nat → Nat
  | _, s => (s + 1) % 16

/-- Invariant of the round fixture: the round stays below 16. -/
def rundeInv : Nat → Bool
  | s => decide (s < 16)

/-- The uniform contract holds for all 64 rounds: from every round below
    16 each round may run and the next round stays below 16. -/
theorem runde_vertrag : ∀ k s, k < 64 → rundeInv s = true →
    rundeVor k s = true ∧ rundeInv (rundeNach k s) = true := by
  intro k s hk hs
  have hslt : s < 16 := by simpa [rundeInv] using hs
  constructor
  · simpa [rundeVor, rundeInv] using hs
  · simp only [rundeInv, rundeNach]
    have hmod : (s + 1) % 16 < 16 := by omega
    simp [hmod]

/-- Witness (`tick_runde` shape, non-degenerate): 64 uniform round ticks
    from round 0 keep the round below 16 -- one lemma application, not
    64 unrolled call goals. -/
theorem tick_runde_zeuge :
    rundeInv (rufLauf ⟨64, rundeVor, rundeNach⟩ 64 0 0) = true :=
  rufKette_invariant ⟨64, rundeVor, rundeNach⟩ rundeInv
    runde_vertrag 64 0 0 (by decide) (by decide)

/-- Planted failure: without the uniform contract the end-state guarantee
    is lost -- a chain that jumps out keeps jumping out. Checked equation,
    not a counterexample (`herh` fails here, so the lemma says nothing). -/
theorem tick_ohne_vertrag_bricht :
    rundeInv (rufLauf ⟨64, rundeVor, fun _ _ => 99⟩ 64 0 0) = false := by
  decide

/-! ## Disjunctive callee posts: one case analysis, not per goal -/

/-- One case analysis for a disjunctive callee post: the caller needs `r`
    whether the callee answers `true` (then `ra` establishes it) or
    `false` (then `rb` establishes it). Each premise is one implication
    as a `Bool`; the pipeline's per-goal splits become instances of this
    one lemma -- the `sortiere` shape (`126`: five `ordne` calls over the
    comparator answer). -/
theorem disjunkt_einmal (erg ra rb r : Bool)
    (ha : ((!erg) || ra) = true)
    (hb : (erg || rb) = true)
    (hra : ((!ra) || r) = true)
    (hrb : ((!rb) || r) = true) :
    r = true := by
  cases erg with
  | true =>
      have h1 : ra = true := by simpa using ha
      simpa [h1] using hra
  | false =>
      have h1 : rb = true := by simpa using hb
      simpa [h1] using hrb

/-- Instance on the comparator shape: the callee answers `false`
    (swap taken), the taken-branch establishes the post. -/
theorem disjunkt_vergleich : True :=
  let _ := disjunkt_einmal false false true true rfl rfl rfl rfl
  True.intro

/-
   CUTS (follow-up-3): proved `rufKette_invariant` (induction over the
   chain, any length), its `tick_runde_zeuge` (64 rounds) and failure
   witness, and `disjunkt_einmal` with the comparator instance. Only
   stated: the fixture maps. Not modelled: the `World`-to-`RufKette`
   bridge (a unit's `requires`/`ensures` to `vor`/`nach`); the
   `Grammatik.lean` import line (one edit at merge time);
   reconciliation with agent 05's `GvSplits.lean` (not in this clone).
   No `sorry` is used.
-/

#print axioms rufKette_invariant
#print axioms rufLauf_letzter
#print axioms disjunkt_einmal
#print axioms tick_runde_zeuge

end Gabbro.Grammatik.GabbroV
