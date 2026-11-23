module
public meta import Lean
public meta import Core.Waechter.Dependencies

open Lean

namespace Gabbro.Core.Waechter

public meta structure ClosingSpec where
  theoremName : Name
  shape : Name
  frame : Name
  frameType : Name
  frameConstructor : Name
  fieldBindings : Array Name
  trustedRoots : NameSet

/-- M12 configures the public theorem, the argument-free frame and the approved fields in constructor
    order. Its frame must also have an owner-approved hash pin. This checks the literal elaborated theorem
    type and frame field constants, visits the semantic closure of the frame, and rejects foreign leaves
    outside the explicit trusted roots. The exported theorem must use exactly the three standard axioms.
    It checks the configured bindings and roots. Approval of their intended meaning is external to Lean. -/
public meta def closingErrors (spec : ClosingSpec) (pins : Array (Name × UInt64))
    (exported : Environment) : CoreM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  let expected := mkApp (mkConst spec.shape) (mkConst spec.frame)
  match env.find? spec.theoremName with
  | some (.thmInfo proof) =>
    if proof.type != expected || (exported.find? spec.theoremName).isNone then
      errors := errors.push s!"closing theorem {spec.theoremName} does not export {spec.shape} {spec.frame}"
    let usedAxioms ← collectAxioms spec.theoremName
    if usedAxioms.size != 3 || usedAxioms.any (!standardAxioms.contains ·) then
      errors := errors.push s!"closing theorem {spec.theoremName} has axiom set {usedAxioms}"
  | _ => errors := errors.push s!"missing closing theorem {spec.theoremName}"
  let expectedFrame := mkAppN (mkConst spec.frameConstructor) (spec.fieldBindings.map (mkConst ·))
  unless (env.find? spec.frame).any (fun frame =>
      frame.type == mkConst spec.frameType && frame.value? true == some expectedFrame) do
    errors := errors.push s!"closing frame {spec.frame} does not use its approved field bindings"
  for root in #[spec.shape, spec.frame] do
    unless pins.any (fun pin => pin.1 == root) do
      errors := errors.push s!"closing root {root} lacks an approved hash pin"
  let mut seen : NameSet := {}
  let mut pending := [spec.shape, spec.frame]
  while let name :: rest := pending do
    pending := rest
    if seen.contains name || spec.trustedRoots.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      if isCoreConstant env name then
        pending := info.getUsedConstantsAsSet.toArray.toList ++ pending
      else
        errors := errors.push s!"closing dependency {name} is outside the trusted roots"
    else
      errors := errors.push s!"missing closing dependency {name}"
  return errors

end Gabbro.Core.Waechter
