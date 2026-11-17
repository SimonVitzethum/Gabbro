module

public import Grammatik.Logik.Vertraege.Pruefer.Program

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.SelectionWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC

variable {D : Deklaration}

/-- Compose successful proof-producing checks without normalizing their proofs. -/
theorem collect_success {α : Type} (items : List α) (property : α → Prop)
    (check : ∀ item, Except Frag.Refusal (PLift (property item)))
    (success : ∀ item, ∃ result, check item = .ok result) :
    ∃ result, Invarianten.Pruefer.collect items property check = .ok result := by
  induction items with
  | nil => exact ⟨_, rfl⟩
  | cons item items ih =>
      obtain ⟨head, hhead⟩ := success item
      obtain ⟨tail, htail⟩ := ih
      cases result : Invarianten.Pruefer.collect (item :: items) property check with
      | error cause =>
          simp only [Invarianten.Pruefer.collect, hhead, htail, bind, Except.bind,
            pure, Except.pure, reduceCtorEq] at result
      | ok out => exact ⟨out, rfl⟩

theorem success_of_isSome {α ε : Type} (result : Except ε α)
    (ready : result.toOption.isSome = true) : ∃ value, result = .ok value := by
  cases result with
  | error cause => cases ready
  | ok value => exact ⟨value, rfl⟩

open Invarianten.Frag.Symbolic Symbolic

/-- Off-path proof rule for the actual symbolic decision gate. The executable
    checker still computes the source translation, compiler and Cooper result. -/
theorem environment_success (program : Programm D) (S : SperrInv D)
    (symbols : SymEnv D Nat (D.params f)) (bounded : symbols.Bounded next)
    (policy : CallPolicy program (entryContext symbols bounded))
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (supported : (currentOnly (program.ensures f)).toOption.isSome = true)
    (entry : Encoding symbols .bool (fun world actual => eval world (program.requires f) world actual))
    (hentry : Invarianten.Frag.Symbolic.translate (program.requires f) symbols = .ok entry)
    (compiled : Symbolic.EndCondition (S := S) policy.semantic (program.rumpf f) symbols
      (contractGoals program f symbols bounded invariants))
    (hcompiled : ending policy (Invarianten.Pruefer.lockFormula S sources) budget hint budget.depth
      (program.rumpf f) symbols bounded (contractGoals program f symbols bounded invariants) = .ok compiled)
    (decided : decideB (close (lower (entryVC symbols entry.payload compiled.formula)))
      (close_closed _) = true) :
    (Vertraege.Pruefer.checkEnvironment program S symbols bounded policy sources budget hint invariants).toOption.isSome = true := by
  obtain ⟨support, hsupport⟩ := success_of_isSome _ supported
  unfold Vertraege.Pruefer.checkEnvironment
  rw [hsupport]
  dsimp only [bind, Except.bind]
  rw [hentry]
  dsimp only [bind, Except.bind]
  rw [hcompiled]
  dsimp only [bind, Except.bind]
  split
  · rfl
  · rename_i refused
    exact False.elim (refused decided)

/-- Compose a mathematically valid open VC with the actual Cooper gate.
    Witnesses need not normalize the decision procedure on their fixture. -/
theorem environment_success_of_valid (program : Programm D) (S : SperrInv D)
    (symbols : SymEnv D Nat (D.params f)) (bounded : symbols.Bounded next)
    (policy : CallPolicy program (entryContext symbols bounded))
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget) (hint : Option (QF (Observation D)))
    (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (supported : (currentOnly (program.ensures f)).toOption.isSome = true)
    (entry : Encoding symbols .bool (fun world actual => eval world (program.requires f) world actual))
    (hentry : Invarianten.Frag.Symbolic.translate (program.requires f) symbols = .ok entry)
    (compiled : Symbolic.EndCondition (S := S) policy.semantic (program.rumpf f) symbols
      (contractGoals program f symbols bounded invariants))
    (hcompiled : ending policy (Invarianten.Pruefer.lockFormula S sources) budget hint budget.depth
      (program.rumpf f) symbols bounded (contractGoals program f symbols bounded invariants) = .ok compiled)
    (valid : ∀ values, (entryVC symbols entry.payload compiled.formula).denote values) :
    (Vertraege.Pruefer.checkEnvironment program S symbols bounded policy sources budget hint invariants).toOption.isSome = true := by
  have decided : decideB (close (lower (entryVC symbols entry.payload compiled.formula))) (close_closed _) = true :=
    (close_decide_true_iff _).mpr (fun values => (lower_denote _ values).mpr (valid values))
  exact environment_success program S symbols bounded policy sources budget hint invariants
    supported entry hentry compiled hcompiled decided

theorem execution_success (program : Programm D) (S : SperrInv D)
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget)
    (hint : Option (QF (Observation D))) (f : D.Fn)
    (supported : (currentOnly (program.ensures f)).toOption.isSome = true)
    (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (hinvariants : invariantFormula program (D.invs.filter (schuldet f)) = .ok invariants)
    (domain : Parameters D 0 (D.params f))
    (hdomain : parameters (D := D) budget.expansion 0 (D.params f) = .ok domain)
    (withinBudget : argumentSpecializations budget.specializations (D.params f) *
      endSpecializations program (uniformPost program f) budget.expansion budget.specializations
        (program.rumpf f) ≤ budget.specializations)
    (ready : ∀ entry : { symbols // symbols ∈ domain.templates },
      (Vertraege.Pruefer.checkEnvironment program S entry.val (domain.bounded entry.val entry.property)
        (requiresPolicy program _) sources budget hint invariants).toOption.isSome = true) :
    (checkExecution program S sources budget hint f).toOption.isSome = true := by
  obtain ⟨support, hsupport⟩ := success_of_isSome _ supported
  obtain ⟨checked, hchecked⟩ := collect_success domain.templates.attach _
    (fun entry => Vertraege.Pruefer.checkEnvironment program S entry.val (domain.bounded entry.val entry.property)
      (requiresPolicy program _) sources budget hint invariants)
    (fun entry => success_of_isSome _ (ready entry))
  unfold checkExecution
  rw [hsupport]
  dsimp only [bind, Except.bind]
  rw [hinvariants]
  dsimp only [bind, Except.bind]
  rw [hdomain]
  dsimp only [bind, Except.bind]
  simp only [Nat.not_lt.mpr withinBudget, ↓reduceIte, pure, Except.pure, bind, Except.bind]
  rw [hchecked]
  rfl

/-- The actual function gate preserves its syntax certificate, atomic replay
    and checked strict execution; this is a proof rule, not a new gate path. -/
theorem function_success (program : Programm D) (S : SperrInv D)
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget)
    (hint : Option (QF (Observation D))) (f : D.Fn)
    (basic : checkBasicFunction program S sources budget f = none)
    (replay : (Invarianten.Pruefer.atomicReplay? program f).isSome = true)
    (execution : (checkExecution program S sources budget hint f).toOption.isSome = true) :
    (checkFunction program S sources budget hint f).toOption.isSome = true := by
  obtain ⟨checked, hchecked⟩ := success_of_isSome _ execution
  cases h : Invarianten.Pruefer.atomicReplay? program f with
  | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at replay
  | some certificate =>
      unfold checkFunction
      rw [basic, h, hchecked]
      rfl

/-- Compose successful function checks through the actual default-hint gate. -/
theorem contracts_success (program : Programm D) (S : SperrInv D)
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget) (functions : List D.Fn)
    (ready : ∀ f, (checkFunction program S sources budget none f).toOption.isSome = true) :
    KontrakteGeprueftB program S functions sources budget = true := by
  obtain ⟨checked, hchecked⟩ := collect_success functions (ContractDuties program S)
    (fun f => do
      let hint ← loopHint (fun _ => none) f
      checkFunction program S sources budget hint f) (by
        intro f
        dsimp only [loopHint, bind, Except.bind]
        exact success_of_isSome _ (ready f))
  unfold KontrakteGeprueftB checkContracts
  rw [hchecked]
  rfl

end Gabbro.Grammatik.Vertraege.Pruefer.SelectionWitness
