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

/-- A failed current-state syntax check is an actual post-translation refusal. -/
theorem post_refused (program : Programm D) (f : D.Fn) (locals : Env D (D.params f))
    (value : ErgVal D (D.erg f))
    (rejected : (currentOnly (program.ensures f)).toOption.isSome = false) :
    (postFormula program f locals value).toOption.isSome = false := by
  cases result : currentOnly (program.ensures f) with
  | error cause => unfold postFormula; rw [result]; rfl
  | ok checked => rw [result] at rejected; cases rejected

/-- One typed result whose post is unsupported prevents successful environment
    checking. The complete result domain, not a sampled answer, supplies membership. -/
theorem environment_refused (program : Programm D) (S : SperrInv D) (policy : CallPolicy program)
    (sources : LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (f : D.Fn) (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (locals : Env D (D.params f)) (value : ErgVal D (D.erg f))
    (rejected : (postFormula program f locals value).toOption.isSome = false) :
    (checkEnvironment program S policy sources budget hint f invariants locals).toOption.isSome = false := by
  unfold checkEnvironment
  cases entry : translate (program.requires f) locals with
  | error cause => rfl
  | ok encoded =>
      dsimp only [bind, Except.bind]
      cases domainResult : results (D := D) budget.expansion (D.erg f) with
      | error cause => rfl
      | ok domain =>
          dsimp only [bind, Except.bind]
          cases posts : collect domain.values
              (fun result => ∃ formula, postFormula program f locals result = .ok formula)
              (checkPostFormula program f locals) with
          | error cause => rfl
          | ok checked =>
              obtain ⟨formula, translated⟩ := checked.down value (domain.complete value)
              rw [translated] at rejected
              cases rejected

/-- A typed parameter environment is a member of every successful complete
    enumeration. Its failed post check therefore prevents execution checking. -/
theorem execution_refused (program : Programm D) (S : SperrInv D) (policy : CallPolicy program)
    (sources : LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (f : D.Fn) (locals : Env D (D.params f)) (value : ErgVal D (D.erg f))
    (rejected : (postFormula program f locals value).toOption.isSome = false) :
    (checkExecution program S policy sources budget hint f).toOption.isSome = false := by
  unfold checkExecution
  cases invariantResult : invariantFormula program (D.invs.filter (schuldet f)) with
  | error cause => rfl
  | ok invariants =>
      dsimp only [bind, Except.bind]
      cases domainResult : environments (D := D) budget.expansion (D.params f) with
      | error cause => rfl
      | ok domain =>
          dsimp only [bind, Except.bind]
          split
          · rfl
          · dsimp only [bind, Except.bind, pure, Except.pure]
            cases checked : collect domain.values
                (fun args => CheckedEnvironment (S := S) policy f args)
                (checkEnvironment program S policy sources budget hint f invariants) with
            | error cause =>
                first
                | rfl
                | delta CheckedEnvironment at checked; rw [checked]; rfl
            | ok certificate =>
                have accepted := collect_each domain.values
                  (fun args => CheckedEnvironment (S := S) policy f args)
                  (checkEnvironment program S policy sources budget hint f invariants)
                  (by rw [checked]; rfl) locals (domain.complete locals)
                rw [environment_refused program S policy sources budget hint f invariants
                  locals value rejected] at accepted
                cases accepted

  /-- The existing basic path must be absent; both atomic replay outcomes then
      retain the actual failed execution check. -/
  theorem function_refused (program : Programm D) (S : SperrInv D) (sources : LockSources S)
      (budget : VCBudget) (hint : Option (QF (Observation D))) (f : D.Fn)
      (basic : checkBasicFunction program S sources budget f = none)
      (locals : Env D (D.params f)) (value : ErgVal D (D.erg f))
      (rejected : (postFormula program f locals value).toOption.isSome = false) :
      (checkFunction program S sources budget hint f).toOption.isSome = false := by
    unfold checkFunction
    rw [basic]
    cases replay : Invarianten.Pruefer.atomicReplay? program f with
    | none => rfl
    | some certificate =>
        have refused := execution_refused program S (requiresPolicy program) sources budget hint f locals value rejected
        cases executed : checkExecution program S (requiresPolicy program) sources budget hint f with
        | error cause => rfl
        | ok checked => rw [executed] at refused; cases refused

  /-- A named function's actual post refusal propagates through the unchanged
      default-hint contract gate. No compiler body or structural gate is evaluated. -/
  theorem contracts_refused (program : Programm D) (S : SperrInv D) (sources : LockSources S)
      (budget : VCBudget) (functions : List D.Fn) (f : D.Fn) (member : f ∈ functions)
      (basic : checkBasicFunction program S sources budget f = none)
      (locals : Env D (D.params f)) (value : ErgVal D (D.erg f))
      (rejected : (postFormula program f locals value).toOption.isSome = false) :
      KontrakteGeprueftB program S functions sources budget = false := by
    change (collect functions (ContractDuties program S)
      (fun g => checkFunction program S sources budget none g)).toOption.isSome = false
    cases collected : collect functions (ContractDuties program S)
        (fun g => checkFunction program S sources budget none g) with
    | error cause => rfl
    | ok checked =>
        have accepted := collect_each functions (ContractDuties program S)
          (fun g => checkFunction program S sources budget none g) (by rw [collected]; rfl) f member
        rw [function_refused program S sources budget none f basic locals value rejected] at accepted
        cases accepted

  end Gabbro.Grammatik.Vertraege.Pruefer.RefusalWitness
