module

public import Core.Ast.LowLevel.Exec.Meaning

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

/-- The L4 skeleton forms have constructors but no spelling and no meaning:
    neither the exact production nor the elaboration accepts an occurrence. -/

@[expose] public def CpuCapsAbgelehntAussage : Prop :=
  (∀ scope feature, elaborateExec scope (ExecTree.cpuCaps feature) = none) ∧
  ∀ tokens feature, ¬ (ExecTree.cpuCaps feature).production tokens

theorem cpuCapsAbgelehnt : CpuCapsAbgelehntAussage := by
  refine ⟨?_, ?_⟩
  · intro scope feature
    rfl
  · intro tokens feature
    simp only [ExecTree.production]

@[expose] public def CpuCyclesAbgelehntAussage : Prop :=
  (∀ scope, elaborateExec scope (ExecTree.cpuCycles : ExecTree .cpuCycles) = none) ∧
  ∀ tokens, ¬ (ExecTree.cpuCycles : ExecTree .cpuCycles).production tokens

theorem cpuCyclesAbgelehnt : CpuCyclesAbgelehntAussage := by
  refine ⟨?_, ?_⟩
  · intro scope
    rfl
  · intro tokens
    simp only [ExecTree.production]

@[expose] public def SuspendSystemAbgelehntAussage : Prop :=
  (∀ scope resume arguments failure,
    elaborateExec scope (ExecTree.suspendSystem resume arguments failure) = none) ∧
  ∀ tokens resume arguments failure,
    ¬ (ExecTree.suspendSystem resume arguments failure).production tokens

theorem suspendSystemAbgelehnt : SuspendSystemAbgelehntAussage := by
  refine ⟨?_, ?_⟩
  · intro scope resume arguments failure
    rfl
  · intro tokens resume arguments failure
    simp only [ExecTree.production]

@[expose] public def SuspendCoreAbgelehntAussage : Prop :=
  (∀ scope resume, elaborateExec scope (ExecTree.suspendCore resume) = none) ∧
  ∀ tokens resume, ¬ (ExecTree.suspendCore resume).production tokens

theorem suspendCoreAbgelehnt : SuspendCoreAbgelehntAussage := by
  refine ⟨?_, ?_⟩
  · intro scope resume
    rfl
  · intro tokens resume
    simp only [ExecTree.production]

@[expose] public def ResumeArrivalAbgelehntAussage : Prop :=
  (∀ scope state, elaborateExec scope (ExecTree.resumeArrival state) = none) ∧
  ∀ tokens state, ¬ (ExecTree.resumeArrival state).production tokens

theorem resumeArrivalAbgelehnt : ResumeArrivalAbgelehntAussage := by
  refine ⟨?_, ?_⟩
  · intro scope state
    rfl
  · intro tokens state
    simp only [ExecTree.production]

end Gabbro.Core.Ast.LowLevel
