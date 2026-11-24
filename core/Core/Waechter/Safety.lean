module

public meta import Core.Waechter.Dependencies

open Lean

namespace Gabbro.Core.Waechter

/-- The machine shares some modules with the ideal meaning. Check their declaration names
    as well as the module boundaries, including the names of private Core helpers. -/
public meta def safetyErrors (env : Environment) (index : DependencyIndex) (roots : Array Name) : Array String := Id.run do
  let allowed := #[`Core.Sicherheit, `Core.Maschine, `Core.Speicher, `Core.Aussen, `Core.Katalog]
  let forbidden := #[`I, `Sim, `Verfeinert, `Akzeptiert]
  let mut errors := #[]
  for root in roots do
    unless isCoreConstant env root && (env.find? root).isSome do
      errors := errors.push s!"missing safety dependency root {root}"
    for name in index.closure root do
      if let some i := env.getModuleIdxFor? name then
        let mod := env.header.moduleNames[i.toNat]!
        if !allowed.any (·.isPrefixOf mod) || name.components.any (forbidden.contains ·) then
          errors := errors.push s!"safety dependency {root} -> {name} in {mod} is forbidden"
  return errors

end Gabbro.Core.Waechter
