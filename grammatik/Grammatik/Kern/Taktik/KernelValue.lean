module

public import Grammatik.Kern.Taktik.KernelRfl
public meta import Lean.Meta.Tactic.Cbv

public section

open Lean Elab Tactic Meta in
/-- Normalize a candidate data value and retain kernel conversion as the equality check.
    Output metavariables receive the normalized data, so later phases share that value. -/
elab "kernel_value" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := type.eq? | throwError "kernel_value: the goal is not an equality"
  let computed ← Lean.Meta.Tactic.Cbv.cbvEntry lhs
  let value := computed.getResultExpr lhs
  unless ← withAssignableSyntheticOpaque (isDefEq rhs value) do
    throwError "kernel_value: the computed candidate does not match the requested result"
  evalTactic (← `(tactic| kernel_rfl))
