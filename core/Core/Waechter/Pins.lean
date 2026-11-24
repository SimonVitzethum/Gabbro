module
public meta import Lean
public meta import Core.Waechter.Dependencies

open Lean

namespace Gabbro.Core.Waechter

private meta def declarationHash (info : ConstantInfo) : UInt64 := Id.run do
  let h := mixHash (hash info.name) (hash info.levelParams)
  let h := mixHash h info.type.hash
  let payload : UInt64 × UInt64 :=
    match info with
    | .axiomInfo _ => (1, 0)
    | .defnInfo d => (2, d.value.hash)
    | .thmInfo d => (3, d.value.hash)
    | .opaqueInfo d => (4, d.value.hash)
    | .quotInfo _ => (5, 0)
    | .inductInfo d => (6, hash d.ctors)
    | .ctorInfo d => (7, mixHash (hash d.induct) (hash d.cidx))
    | .recInfo d => (8, d.rules.foldl (fun r (rule : RecursorRule) =>
        mixHash r (mixHash (hash rule.ctor) rule.rhs.hash)) 0)
  return mixHash (mixHash h payload.1) payload.2


/-- Pins the structural type and value of each named declaration and its full Core dependency graph.
    Inductive constructor lists and constructor types are included. Lean and Mathlib are trusted interfaces.
    This hash detects structural edits under the pinned toolchain. Semantic equivalence requires a proof. -/
public meta def pinErrors (env : Environment) (index : DependencyIndex) (pins : Array (Name × UInt64)) : Array String := Id.run do
  let mut hashes : Std.HashMap Name UInt64 := {}
  let mut pinHashes : Std.HashMap Name UInt64 := {}
  let mut measured := #[]
  let mut errors := #[]
  for (root, expected) in pins do
    if !isCoreConstant env root || (env.find? root).isNone then
      errors := errors.push s!"missing hash pin root {root}"
    let actual ← match pinHashes[root]? with
      | some actual => pure actual
      | none => do
        let mut actual := 0
        for name in index.closure root do
          let declaration ← match hashes[name]? with
            | some declaration => pure declaration
            | none => do
              let declaration := (env.find? name).map declarationHash |>.getD 0
              hashes := hashes.insert name declaration
              pure declaration
          actual := mixHash actual declaration
        pinHashes := pinHashes.insert root actual
        pure actual
    measured := measured.push s!"(`{root}, {actual})"
    if actual != expected then
      errors := errors.push s!"hash mismatch for {root} (expected {expected}, measured {actual})"
  if !errors.isEmpty then
    errors := errors.push ("Measured pins (update after owner approval):\n#[" ++
      String.intercalate ",\n  " measured.toList ++ "]")
  return errors

end Gabbro.Core.Waechter
