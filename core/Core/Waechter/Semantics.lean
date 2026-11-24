module
public meta import Lean
public meta import Core.Waechter.Dependencies
public meta import Core.Waechter.Source

open Lean

namespace Gabbro.Core.Waechter

public meta structure ClosedKinds where
  inductiveName : Name
  constructors : List Name

/-- M4 registers I and its outcome and hardware kind inductives. As rules and fundamental proofs arrive,
    register each entry point. The check follows their Core dependencies and reports a literal wildcard arm
    inside each declaration's source range. Macros and generated declarations without source ranges are
    outside the lexical test. For each catalogue-governed kind type, it compares the exact constructor list. -/
public meta def semanticsErrors (roots : Array Name) (kinds : Array ClosedKinds)
    (sources : Array (Source × SourceAudit)) : CoreM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  let mut modules : Std.HashMap Name (Source × SourceAudit) := {}
  for pair in sources do
    modules := modules.insert pair.1.moduleName pair
  for root in roots do
    if !isCoreConstant env root || (env.find? root).isNone then
      errors := errors.push s!"missing wildcard guard root {root}"
    else if (← findDeclarationRanges? root).isNone then
      errors := errors.push s!"missing source range for wildcard guard root {root}"
  for name in coreClosure env roots do
    let some idx := env.getModuleIdxFor? name | continue
    let some (source, scan) := modules[env.header.moduleNames[idx.toNat]!]? | continue
    if scan.wildcardArms.isEmpty then continue
    let some location ← findDeclarationRanges? name | continue
    for pos in scan.wildcardArms do
      let range := location.range
      if !pos.lt range.pos && pos.lt range.endPos then
        errors := errors.push s!"{source.path}:{pos.line}:{pos.column}: wildcard arm in {name}"
  for kind in kinds do
    match env.find? kind.inductiveName with
    | some (.inductInfo info) =>
      if !isCoreConstant env info.name || info.ctors != kind.constructors then
        errors := errors.push s!"unapproved kind constructors of {info.name}: {info.ctors}"
    | _ => errors := errors.push s!"missing catalogue-governed inductive {kind.inductiveName}"
  return errors

end Gabbro.Core.Waechter
