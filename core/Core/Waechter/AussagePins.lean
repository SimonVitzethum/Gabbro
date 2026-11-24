module
public meta import Lean
public meta import Core.Waechter.Dependencies

open Lean

namespace Gabbro.Core.Waechter

/-- Every Core proposition whose name ends in `Aussage` and that lives outside the guard namespace must
    be a pin root or reachable from one through Core dependencies. Otherwise an edit to its statement can
    pass unnoticed because no hash pin covers it. Report each uncovered declaration by its full name. -/
public meta def aussagePinErrors (env : Environment) (index : DependencyIndex)
    (pins : Array (Name × UInt64)) : Array String := Id.run do
  let mut covered : Std.HashSet Name := {}
  for (root, _) in pins do
    covered := covered.insert root
    for name in index.closure root do
      covered := covered.insert name
  let mut errors := #[]
  for name in coreDeclarations env do
    if let some moduleIdx := env.getModuleIdxFor? name then
      if (`Core.Waechter).isPrefixOf env.header.modules[moduleIdx.toNat]!.module then
        continue
    if !name.toString.endsWith "Aussage" then
      continue
    let some info := env.find? name | continue
    if !info.type.isProp then
      continue
    unless covered.contains name do
      errors := errors.push s!"unpinned Aussage declaration {name}"
  return errors

end Gabbro.Core.Waechter
