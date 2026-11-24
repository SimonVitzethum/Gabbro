module
public meta import Lean
public meta import Core.Waechter.Dependencies

open Lean Meta

namespace Gabbro.Core.Waechter

private meta def smallNatural (term : Expr) : MetaM Bool := do
  let mut term := term
  for successors in [:257] do
    term ← whnf term
    if let some value ← getNatValue? term then
      return value + successors ≤ 256
    let .app (.const ``Nat.succ _) inner := term | return false
    term := inner
  return false

private meta def smallEquality (type lhs rhs : Expr) : MetaM Bool := do
  let env ← getEnv
  let type ← whnf type
  let some typeName := type.getAppFn.constName? | return false
  if typeName == ``Nat then
    return (← smallNatural lhs) && (← smallNatural rhs)
  let some (.inductInfo info) := env.find? typeName | return false
  unless info.numParams == 0 && info.numIndices == 0 && info.ctors.length ≤ 16 do
    return false
  unless info.ctors.all (fun ctor => match env.find? ctor with
      | some (.ctorInfo c) => c.numFields == 0
      | _ => false) do
    return false
  let lhs ← whnf lhs
  let rhs ← whnf rhs
  return lhs.constName?.any info.ctors.contains && rhs.constName?.any info.ctors.contains

private meta def smallProposition (goal : Expr) : MetaM Bool := do
  if goal.hasLooseBVars || goal.hasFVar || goal.hasMVar then return false
  let mut pending := [goal]
  let mut parts := 0
  while let p :: rest := pending do
    pending := rest
    parts := parts + 1
    if parts > 128 then return false
    let p ← whnf p
    if let .forallE _ domain body _ := p then
      if body.hasLooseBVars then return false
      pending := domain :: body :: pending
      continue
    let args := p.getAppArgs
    match p.getAppFn.constName? with
    | some name =>
      if name == ``True || name == ``False then continue
      if name == ``And || name == ``Or || name == ``Iff then
        if let #[left, right] := args then
          pending := left :: right :: pending
          continue
      if name == ``Eq then
        if let #[type, lhs, rhs] := args then
          if ← smallEquality type lhs rhs then continue
      if name == ``Nat.le then
        if let #[lhs, rhs] := args then
          if (← smallNatural lhs) && (← smallNatural rhs) then continue
      return false
    | none => return false
  return true

private meta def checkGoal (goal : Expr) : MetaM Bool := do
  let start ← IO.getNumHeartbeats
  -- Budget the reduction that reveals the propositional structure independently for each goal.
  let small ← try
      withTheReader Core.Context (fun ctx =>
        { ctx with initHeartbeats := start, maxHeartbeats := 20000 }) <| smallProposition goal
    catch _ => pure false
  return small && (← IO.getNumHeartbeats) - start ≤ 20000

private meta def decisionGoals (body : Expr) : Array Expr := runST fun world => do
  let goals ← ST.mkRef (σ := world) (#[] : Array Expr)
  body.forEach' (ω := world) fun expr => do
    if let .app (.app (.app (.const name _) goal) _) _ := expr then
      if name == ``of_decide_eq_true then
        goals.modify (·.push goal)
    return true
  goals.get

/-- Checks retained decision proofs. Their elaborated goals must reduce, within a fixed budget, to closed
    Boolean combinations of equality on small enumerations or naturals and small natural inequalities.
    The declaration audit supplies only bodies whose declaration mentions the proof constant.
    The source scan checks tactic options separately and refuses anonymous decisions whose proofs are lost. -/
public meta def decisionErrors (bodies : Array (Name × Expr)) : MetaM (Array String) := do
  let mut errors := #[]
  let mut tested : Std.HashMap Expr Bool := {}
  for (name, body) in bodies do
    for goal in decisionGoals body do
      let allowed ← match tested[goal]? with
        | some result => pure result
        | none => do
          let result ← checkGoal goal
          tested := tested.insert goal result
          pure result
      unless allowed do
        errors := errors.push s!"decision proof in {name} has a goal outside the small finite fragment"
        break
  return errors

end Gabbro.Core.Waechter
