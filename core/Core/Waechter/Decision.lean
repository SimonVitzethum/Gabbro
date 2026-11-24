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

/-- Checks retained decision proofs. Their elaborated goals must reduce, within a fixed budget, to closed
    Boolean combinations of equality on small enumerations or naturals and small natural inequalities.
    The source scan checks decision tactic options separately. Discarded tactic alternatives have no
    retained proof to inspect and run within the package's elaboration budget. -/
public meta def decisionErrors (names : Array Name) : MetaM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  let tested ← IO.mkRef ({} : Std.HashMap Expr Bool)
  for name in names do
    let some info := env.find? name | continue
    let some body := info.value? true | continue
    unless (body.find? (·.isAppOfArity ``of_decide_eq_true 3)).isSome do continue
    let violation ← IO.mkRef none
    body.forEach' fun e => do
      if (← violation.get : Option Expr).isSome then return false
      if e.isAppOfArity ``of_decide_eq_true 3 then
        let goal := e.getAppArgs[0]!
        let allowed ← match (← tested.get)[goal]? with
          | some result => pure result
          | none => do
            let result ← checkGoal goal
            tested.modify (·.insert goal result)
            pure result
        unless allowed do violation.set (some goal)
      return true
    if let some _ ← violation.get then
      errors := errors.push s!"decision proof in {name} has a goal outside the small finite fragment"
  return errors

end Gabbro.Core.Waechter
