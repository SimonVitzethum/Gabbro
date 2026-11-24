module
public meta import Lean
public meta import Core.Waechter.Package
meta import all Lean.Util.CollectAxioms

open Lean

namespace Gabbro.Core.Waechter

private meta structure DirectDependencies where
  core : Array Name
  all : Array Name
  isCore : Bool

public meta structure DependencyIndex where
  closures : Std.HashMap Name (Array Name)
  closingErrors : Array String

/-- Index the direct edges once and keep the closures of the actual guard
    roots, so declarations deep in the graph do not each need their own transitive set. The closing
    guard uses the same edges but stops at the explicitly trusted roots, even if they are in Core. -/
public meta def indexDependencies (env : Environment) (roots closingRoots : Array Name)
    (trusted : NameSet) : DependencyIndex := Id.run do
  let mut direct : Std.HashMap Name (Option DirectDependencies) := {}
  let mut closures : Std.HashMap Name (Array Name) := {}
  let mut closingErrors := #[]
  let rootGroups := roots.map (fun root => (some root, #[root])) ++ #[(none, closingRoots)]
  for (root, start) in rootGroups do
    if root.any closures.contains then continue
    let closing := root.isNone
    let mut seen : Std.HashSet Name := {}
    let mut pending := start.toList
    let mut reachable := #[]
    while let name :: rest := pending do
      pending := rest
      if seen.contains name || (closing && trusted.contains name) then continue
      seen := seen.insert name
      if !closing then
        if let some closure := closures[name]? then
          -- A previously checked root contributes its whole closure.
          for dep in closure do
            if dep == name || !seen.contains dep then
              seen := seen.insert dep
              reachable := reachable.push dep
          continue
      let edges ← match direct[name]? with
        | some edges => pure edges
        | none => do
          let edges := (env.find? name).map fun info =>
            let all := info.getUsedConstantsAsSet.toArray
            ⟨all.filter (isCoreConstant env), all, isCoreConstant env name⟩
          direct := direct.insert name edges
          pure edges
      if let some edges := edges then
        if !closing || edges.isCore then
          reachable := reachable.push name
          pending := (if closing then edges.all else edges.core).toList ++ pending
        else
          closingErrors := closingErrors.push s!"closing dependency {name} is outside the trusted roots"
      else if closing then
        closingErrors := closingErrors.push s!"missing closing dependency {name}"
    if let some root := root then
      closures := closures.insert root (reachable.qsort Name.lt)
  return ⟨closures, closingErrors⟩

public meta def DependencyIndex.closure (index : DependencyIndex) (root : Name) : Array Name :=
  index.closures[root]?.getD #[]


public meta def standardAxioms : NameSet :=
  .ofList [`propext, `Classical.choice, `Quot.sound]

/-- Reuses Lean's serialized axiom summaries without running library initializers a second time.
    This bridge uses the axiom extension of the pinned Lean toolchain. -/
public meta def withAxiomSummaries (env : Environment) : Environment :=
  let entries := env.header.modules.mapIdx fun i _ => exportedAxiomsExt.getModuleEntries env i
  exportedAxiomsExt.setState env { importedModuleEntries := entries }

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
public meta def declarationAudit (names : Array Name) : CoreM (Array String × Array (Name × Expr)) := do
  let env ← getEnv
  let mut errors := #[]
  let mut decisionBodies := #[]
  for name in names do
    let some info := env.find? name | continue
    let shortName := name.toString
    if shortName.endsWith "_zeuge" then
      errors := errors.push s!"{name} has a forbidden declaration suffix"
    if (info.isPartial || info.isUnsafe) && !hasCheckedRecursion env info then
      errors := errors.push s!"{name} has forbidden declaration safety"
    let used := info.getUsedConstantsAsSet
    if used.contains `Lean.ofReduceBool then
      errors := errors.push s!"{name} depends on Lean.ofReduceBool"
    if used.contains ``of_decide_eq_true then
      if let some body := info.value? true then
        decisionBodies := decisionBodies.push (name, body)
    for ax in ← collectAxioms name do
      unless standardAxioms.contains ax do
        errors := errors.push s!"{name} depends on forbidden axiom {ax}"
  return (errors, decisionBodies)

public meta structure AcceptanceSpec where
  acceptance : Array Name := #[]
  ideal : Array Name := #[]
  syntaxModules : Array Name := #[]
  idealModules : Array Name := #[]
  catalogueModules : Array Name := #[]
  forbidden : Array Name := #[]
  forbiddenModules : Array Name := #[]

/-- M4 lists the ideal entry points and their module prefixes. M5 lists every acceptance definition
    (including its three components) and the syntax and catalogue module prefixes. The forward traversal
    checks each Core dependency, including helpers behind allowed definitions. Forbidden declaration and
    module prefixes take priority over the allowed modules. The reverse traversal checks the ideal entry
    points for every acceptance definition. Review the placement and meaning of definitions in the approved
    modules. Lean cannot infer semantic layers from their expressions alone. -/
public meta def acceptanceErrors (env : Environment) (index : DependencyIndex) (spec : AcceptanceSpec) : Array String := Id.run do
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
  let mut violations : Std.HashMap Name (Option (Name × String)) := {}
  for root in spec.acceptance do
    for name in index.closure root do
      let violation ← match violations[name]? with
        | some cached => pure cached
        | none => do
          let violation := (env.getModuleIdxFor? name).bind fun idx =>
            let mod := env.header.modules[idx.toNat]!.module
            if spec.forbidden.any (·.isPrefixOf name) || spec.forbiddenModules.any (·.isPrefixOf mod) then
              some (mod, "is forbidden")
            else if !allowedModules.any (·.isPrefixOf mod) && !isAcceptance name then
              some (mod, "is outside the whitelist")
            else none
          violations := violations.insert name violation
          pure violation
      if let some (mod, reason) := violation then
        errors := errors.push s!"acceptance dependency {root} -> {name} in {mod} {reason}"
  for root in spec.ideal do
    for name in index.closure root do
      if isAcceptance name then
        errors := errors.push s!"ideal dependency {root} -> {name} reaches acceptance"
  return errors

end Gabbro.Core.Waechter
