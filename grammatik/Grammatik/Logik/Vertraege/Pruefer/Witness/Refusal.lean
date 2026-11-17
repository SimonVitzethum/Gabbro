module

public import Grammatik.Logik.Vertraege.Pruefer.Program

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.RefusalWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC Invarianten.Pruefer

/-- Successful collection means each actual member check succeeded, independently
    of the semantic proof stored in its result. -/
theorem collect_each {α : Type} (items : List α) (property : α → Prop)
    (check : ∀ item, Except Frag.Refusal (PLift (property item))) :
    (collect items property check).toOption.isSome = true →
    ∀ item ∈ items, (check item).toOption.isSome = true := by
  induction items with
  | nil => intro _ item member; cases member
  | cons head tail ih =>
      intro ready
      cases first : check head with
      | error cause =>
          simp only [collect, first, bind, Except.bind, Except.toOption,
            Option.isSome_none, Bool.false_eq_true] at ready
      | ok checked =>
          cases rest : collect tail property check with
          | error cause =>
              simp only [collect, first, rest, bind, Except.bind, Except.toOption,
                Option.isSome_none, Bool.false_eq_true] at ready
          | ok checkedTail =>
              intro item member
              rcases List.mem_cons.mp member with same | member
              · subst item
                rw [first]
                rfl
              · exact ih (by rw [rest]; rfl) item member

variable {D : Deklaration}

attribute [local implicit_reducible] Payload CheckedEnvironment CheckedExecution

/-- A refused post cannot be the literal truth accepted by the basic path. -/
theorem basic_none_of_current_refused (program : Programm D) (S : SperrInv D)
    (sources : LockSources S) (budget : VCBudget) (f : D.Fn)
    (rejected : (currentOnly (program.ensures f)).toOption.isSome = false) :
    checkBasicFunction program S sources budget f = none := by
  unfold checkBasicFunction
  split
  · rename_i _expression _before post
    have present : (currentOnly (program.ensures f)).toOption.isSome = true := by
      rw [post]
      rfl
    rw [present] at rejected
    cases rejected
  · rfl

/-- A source without a supported entry-observation plan is refused before compiling
    any parameter template; unreachable return paths cannot hide that syntax. -/
theorem execution_refused (program : Programm D) (S : SperrInv D)
    (sources : LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (f : D.Fn) (rejected : (Symbolic.snapshotPlan (program.ensures f)).toOption.isSome = false) :
    (checkExecution program S sources budget hint f).toOption.isSome = false := by
  cases checked : Symbolic.snapshotPlan (program.ensures f) with
  | error cause => unfold checkExecution; rw [checked]; rfl
  | ok proof => rw [checked] at rejected; cases rejected

/-- The existing basic path must be absent; both atomic replay outcomes then
    retain the actual failed execution check. -/
theorem function_refused (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (hint : Option (QF (Observation D))) (f : D.Fn)
    (basic : checkBasicFunction program S sources budget f = none)
    (rejected : (Symbolic.snapshotPlan (program.ensures f)).toOption.isSome = false) :
    (checkFunction program S sources budget hint f).toOption.isSome = false := by
  unfold checkFunction
  rw [basic]
  cases replay : Invarianten.Pruefer.atomicReplay? program f with
  | none => rfl
  | some certificate =>
      have refused := execution_refused program S sources budget hint f rejected
      cases executed : checkExecution program S sources budget hint f with
      | error cause => rfl
      | ok checked => rw [executed] at refused; cases refused

/-- A named function's actual post refusal propagates through the unchanged
    default-hint contract gate. No compiler body or structural gate is evaluated. -/
theorem contracts_refused (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (functions : List D.Fn) (f : D.Fn) (member : f ∈ functions)
    (basic : checkBasicFunction program S sources budget f = none)
    (rejected : (Symbolic.snapshotPlan (program.ensures f)).toOption.isSome = false) :
    KontrakteGeprueftB program S functions sources budget = false := by
  change (collect functions (ContractDuties program S)
    (fun g => checkFunction program S sources budget none g)).toOption.isSome = false
  cases collected : collect functions (ContractDuties program S)
      (fun g => checkFunction program S sources budget none g) with
  | error cause => rfl
  | ok checked =>
      have accepted := collect_each functions (ContractDuties program S)
        (fun g => checkFunction program S sources budget none g) (by rw [collected]; rfl) f member
      rw [function_refused program S sources budget none f basic rejected] at accepted
      cases accepted

end Gabbro.Grammatik.Vertraege.Pruefer.RefusalWitness
