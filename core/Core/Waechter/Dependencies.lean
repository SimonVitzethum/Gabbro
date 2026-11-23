module
public meta import Lean
public meta import Core.Waechter.Package
meta import all Lean.Util.CollectAxioms

open Lean

namespace Gabbro.Core.Waechter

/-- Enumerates the Core declarations referenced by types and bodies, including proofs, private helpers,
    constructors of referenced inductives and owners of recursors. Foreign library interfaces are leaves. -/
public meta def coreClosure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut pending := roots.toList
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    if let some info := env.find? name then
      seen := seen.insert name
      for dep in info.getUsedConstantsAsSet do
        if isCoreConstant env dep then
          pending := dep :: pending
  return seen

public meta def standardAxioms : NameSet :=
  .ofList [`propext, `Classical.choice, `Quot.sound]

/-- Reuses Lean's serialized axiom summaries without running library initializers a second time.
    This bridge uses the axiom extension of the pinned Lean toolchain. -/
public meta def withAxiomSummaries (env : Environment) : Environment :=
  let entries := env.header.modules.mapIdx fun i _ => exportedAxiomsExt.getModuleEntries env i
  exportedAxiomsExt.setState env { importedModuleEntries := entries }

private meta def isNativeReduction (name : Name) : Bool :=
  name == `Lean.ofReduceBool

private meta def hasCheckedRecursion (env : Environment) (info : ConstantInfo) : Bool :=
  (Compiler.isUnsafeRecName? info.name).any fun original =>
    env.isSafeDefinition original &&
    env.getModuleIdxFor? original == env.getModuleIdxFor? info.name &&
    (env.find? original).any (·.type == info.type)

public meta def coreDeclarations (env : Environment) : Array Name := Id.run do
  let mut names := #[]
  for (imp, data) in env.header.modules.zip env.header.moduleData do
    if isCoreModule imp.module then
      names := names ++ data.constNames
  return names.qsort Name.lt

/-- Audits public and private Core declarations for unsafe and partial definitions,
    forbidden names, direct native reduction references and all transitive axioms. Lean records transitive
    axiom information for imported library interfaces. Lean's generated recursion code is checked against its
    safe original. The source guard covers tokens erased by elaboration. -/
public meta def declarationErrors (names : Array Name) : CoreM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  for name in names do
    let some info := env.find? name | continue
    let shortName := name.toString
    if shortName.endsWith "_zeuge" then
      errors := errors.push s!"{name} has a forbidden declaration suffix"
    if (info.isPartial || info.isUnsafe) && !hasCheckedRecursion env info then
      errors := errors.push s!"{name} has forbidden declaration safety"
    if info.getUsedConstantsAsSet.toArray.any isNativeReduction then
      errors := errors.push s!"{name} depends on Lean.ofReduceBool"
    for ax in ← collectAxioms name do
      unless standardAxioms.contains ax do
        errors := errors.push s!"{name} depends on forbidden axiom {ax}"
  return errors

public meta structure AcceptanceSpec where
  acceptance : Array Name := #[]
  ideal : Array Name := #[]
  syntaxModules : Array Name := #[]
  idealModules : Array Name := #[]
  catalogueModules : Array Name := #[]

/-- M4 lists the ideal entry points and their module prefixes. M5 lists every acceptance definition
    (including its three components) and the syntax and catalogue module prefixes. The forward traversal
    checks each Core dependency, including helpers behind allowed definitions. The reverse traversal checks
    the ideal entry points for every acceptance definition. Review the placement and meaning of definitions
    in the approved modules. Lean cannot infer semantic layers from their expressions alone. -/
public meta def acceptanceErrors (env : Environment) (spec : AcceptanceSpec) : Array String := Id.run do
  let mut errors := #[]
  let allowedModules := spec.syntaxModules ++ spec.idealModules ++ spec.catalogueModules
  for name in spec.acceptance ++ spec.ideal do
    unless isCoreConstant env name && (env.find? name).isSome do
      errors := errors.push s!"acceptance boundary names missing Core declaration {name}"
  for modulePrefix in allowedModules do
    unless modulePrefix != `Core && isCoreModule modulePrefix &&
        env.header.moduleNames.any (modulePrefix.isPrefixOf ·) do
      errors := errors.push s!"invalid acceptance module prefix {modulePrefix}"
  let isAcceptance := fun name =>
    spec.acceptance.any fun root =>
      root.isPrefixOf name && env.getModuleIdxFor? root == env.getModuleIdxFor? name
  for root in spec.acceptance do
    for name in coreClosure env #[root] do
      if isAcceptance name then continue
      if let some idx := env.getModuleIdxFor? name then
        let mod := env.header.moduleNames[idx.toNat]!
        unless allowedModules.any (·.isPrefixOf mod) do
          errors := errors.push s!"acceptance dependency {root} -> {name} in {mod} is outside the whitelist"
  for root in spec.ideal do
    for name in coreClosure env #[root] do
      if isAcceptance name then
        errors := errors.push s!"ideal dependency {root} -> {name} reaches acceptance"
  return errors

end Gabbro.Core.Waechter
