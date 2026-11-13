module

public import Grammatik.Logik.Invarianten.Modell.World

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell

open Frag Elim Elim.Korrekt

variable {D : Deklaration}

/-- The same closure is reusable for a translated writer VC. Its observation
    support is computed from the matrix, including every free key exactly once. -/
def closedInvariant (formula : LProp (Observation D)) : LProp (Observation D) :=
  universalClosure formula.keys (stateValidity formula.keys formula)

theorem closedInvariant_closed (formula : LProp (Observation D)) :
    closedUnderB [] (closedInvariant formula) = true := by
  apply universalClosure_closedUnderB
  simp only [List.append_nil, stateValidity, closedUnderB, Bool.and_eq_true]
  exact ⟨observationBounds_closed formula.keys formula.keys (fun _ member => member),
    formula.keys_supported⟩

inductive InvariantRefusal where
  | translation (cause : Frag.Refusal)
  | decision (cause : Elim.Refusal)
  deriving DecidableEq, Repr

def InvariantRefusal.message : InvariantRefusal → String
  | .translation cause => cause.message
  | .decision cause => cause.message

/-- Translate, insert typed ranges, close ALL free observations, and decide.
    The default allowance is the proved sufficient budget. A smaller explicit
    allowance refuses the declaration before the metered run, never returning an
    unknown logical answer. The exact budget computation itself performs QE.
    Validity concerns all typed worlds, not just reachable program states. -/
def decideInvariant (carriers : List (D.Tab ⊕ D.Glob)) (expression : Expr D [] Λ .bool)
    (allowance : Option Nat := none) : Except InvariantRefusal Bool :=
  match uebersetzeB carriers expression with
  | .error cause => .error (.translation cause)
  | .ok formula =>
      let closed := closedInvariant formula
      let required := Budget closed
      let fuel := allowance.getD required
      if required ≤ fuel then
        match decideWithBudget closed fuel with
        | .ok answer => .ok answer
        | .error cause => .error (.decision cause)
      else .error (.decision (.budgetExceeded 0 required fuel))

/-- No caller supplies keys to the model-level extractor. The returned world is
    a typed memory snapshot with the base trace; reachability is a later VC duty. -/
def invariantCounterexample (base : World D) (carriers : List (D.Tab ⊕ D.Glob))
    (expression : Expr D [] Λ .bool) : Option (World D) :=
  match uebersetzeB carriers expression with
  | .error _ => none
  | .ok formula => stateCounterexample base formula.keys formula

theorem decideInvariant_at_budget (carriers : List (D.Tab ⊕ D.Glob))
    (expression : Expr D [] Λ .bool) (formula : LProp (Observation D))
    (translated : uebersetzeB carriers expression = .ok formula) (allowance : Option Nat)
    (enough : Budget (closedInvariant formula) ≤
      allowance.getD (Budget (closedInvariant formula))) :
    decideInvariant carriers expression allowance = .ok (decideB (closedInvariant formula)) := by
  have computed := budget_sufficient (closedInvariant formula) _
    (closedInvariant_closed formula) enough
  simp only [decideInvariant, translated, enough, ↓reduceIte, computed]

/-- Every admitted invariant has a Boolean answer at the default budget. -/
theorem decideInvariant_total (carriers : List (D.Tab ⊕ D.Glob))
    (expression : Expr D [] Λ .bool) (formula : LProp (Observation D))
    (translated : uebersetzeB carriers expression = .ok formula) :
    decideInvariant carriers expression = .ok (decideB (closedInvariant formula)) :=
  decideInvariant_at_budget carriers expression formula translated none (by simp)

theorem decideInvariant_over_budget (carriers : List (D.Tab ⊕ D.Glob))
    (expression : Expr D [] Λ .bool) (formula : LProp (Observation D))
    (translated : uebersetzeB carriers expression = .ok formula) (fuel : Nat)
    (overrun : fuel < Budget (closedInvariant formula)) :
    decideInvariant carriers expression (some fuel) =
      .error (.decision (.budgetExceeded 0 (Budget (closedInvariant formula)) fuel)) := by
  have insufficient : ¬ Budget (closedInvariant formula) ≤ fuel := by omega
  simp [decideInvariant, translated, insufficient]

private theorem decideInvariant_result (carriers : List (D.Tab ⊕ D.Glob))
    (expression : Expr D [] Λ .bool) (allowance : Option Nat) (answer : Bool)
    (success : decideInvariant carriers expression allowance = .ok answer) :
    ∃ formula : LProp (Observation D), uebersetzeB carriers expression = .ok formula ∧
      decideB (closedInvariant formula) = answer := by
  cases translated : uebersetzeB carriers expression with
  | error cause => simp [decideInvariant, translated] at success
  | ok formula =>
      refine ⟨formula, translated, ?_⟩
      by_cases enough : Budget (closedInvariant formula) ≤
          allowance.getD (Budget (closedInvariant formula))
      · have computed := decideInvariant_at_budget carriers expression formula translated allowance enough
        rw [computed] at success
        exact Except.ok.inj success
      · simp [decideInvariant, translated, enough] at success

/-- TRUE proves the canonical model invariant in EVERY typed world, without a
    hand-supplied support list or an additional range premise. -/
theorem decideInvariant_sound (carriers : List (D.Tab ⊕ D.Glob))
    (expression : Expr D [] Λ .bool) (allowance : Option Nat)
    (accepted : decideInvariant carriers expression allowance = .ok true) (world : World D) :
    eval world expression world .nil = true := by
  obtain ⟨formula, translated, answer⟩ := decideInvariant_result carriers expression allowance true accepted
  have closedValid := decideB_sound (closedInvariant formula) (closedInvariant_closed formula)
    answer (assignment world)
  have valid := universalClosure_specialize formula.keys (stateValidity formula.keys formula)
    (assignment world) closedValid
  have ranges := observationBounds_assignment formula.keys world
    (uebersetzeB_supported carriers expression formula translated)
  exact (uebersetzeB_sound carriers expression formula translated world).mpr (valid ranges)

/-- FALSE computes a concrete typed world and refutes the actual model
    invariant there. It makes no reachability claim about that snapshot. -/
theorem decideInvariant_complete (base : World D) (carriers : List (D.Tab ⊕ D.Glob))
    (expression : Expr D [] Λ .bool) (allowance : Option Nat)
    (rejected : decideInvariant carriers expression allowance = .ok false) :
    ∃ world : World D, invariantCounterexample base carriers expression = some world ∧
      eval world expression world .nil = false := by
  obtain ⟨formula, translated, answer⟩ := decideInvariant_result carriers expression allowance false rejected
  obtain ⟨world, reconstructed⟩ := stateCounterexample_complete base formula.keys formula answer
  refine ⟨world, ?_, ?_⟩
  · simp only [invariantCounterexample, translated, reconstructed]
  · exact invariant_counterexample_sound base formula.keys carriers expression formula translated
      formula.keys_supported world reconstructed

theorem invariantCounterexample_sound (base : World D) (carriers : List (D.Tab ⊕ D.Glob))
    (expression : Expr D [] Λ .bool) (world : World D)
    (success : invariantCounterexample base carriers expression = some world) :
    eval world expression world .nil = false := by
  cases translated : uebersetzeB carriers expression with
  | error cause => simp [invariantCounterexample, translated] at success
  | ok formula =>
      have reconstructed : stateCounterexample base formula.keys formula = some world := by
        simpa only [invariantCounterexample, translated] using success
      exact invariant_counterexample_sound base formula.keys carriers expression formula translated
        formula.keys_supported world reconstructed

end Gabbro.Grammatik.Invarianten.Modell
