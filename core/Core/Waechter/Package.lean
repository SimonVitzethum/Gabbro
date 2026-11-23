module
public meta import Lean
public meta import Lean.Elab.ParseImportsFast

open Lean System

namespace Gabbro.Core.Waechter

public meta structure Source where
  moduleName : Name
  path : FilePath
  input : String
  header : ModuleHeader

public meta def isCoreModule (name : Name) : Bool :=
  name.getRoot == `Core

private meta def libraryRoots : List Name :=
  [`Mathlib, `Init, `Std, `Lean, `Batteries, `Aesop, `Qq, `Plausible,
    `ProofWidgets, `ImportGraph, `LeanSearchClient]

private meta def allowedImport (mod : Name) : Bool :=
  isCoreModule mod || libraryRoots.contains mod.getRoot

private meta def readSource (moduleName : Name) (path : FilePath) : IO Source := do
  let input ← IO.FS.readFile path
  return ⟨moduleName, path, input, ← parseImports' input path.toString⟩

/-- Reads the package checkout alongside the root being elaborated. The inventory includes unimported files.
    It rejects symlinks below the source directory so the inventory cannot escape the checkout. -/
public meta def readCoreSources (root : FilePath) : IO (Array Source × Array String) := do
  let mut sources := #[← readSource `Core root]
  let mut errors := #[]
  let mut pending := [(`Core, root.withExtension "")]
  while let (mod, dir) :: rest := pending do
    pending := rest
    if (← dir.symlinkMetadata).type != .dir then
      throw <| IO.userError s!"expected a real source directory at {dir}"
    let entries ← dir.readDir
    if entries.size > 20 then
      errors := errors.push s!"{dir} has {entries.size} entries (limit 20)"
    for entry in entries.qsort (fun a b => a.fileName < b.fileName) do
      match (← entry.path.symlinkMetadata).type with
      | .dir => pending := (Name.str mod entry.fileName, entry.path) :: pending
      | .symlink => errors := errors.push s!"symbolic link in the source tree: {entry.path}"
      | .file =>
        if entry.path.extension == some "lean" then
          let name := Name.str mod (entry.fileName.dropEnd 5).toString
          sources := sources.push (← readSource name entry.path)
      | .other => pure ()
  return (sources, errors)

/-- Checks module headers, line counts, package import boundaries and reachability from Core, including
    private source imports. It runs whenever Lean elaborates Core.lean. Lake may reuse the root's artifact
    when an orphan is the only filesystem change, so that case requires a fresh root elaboration. -/
public meta def packageErrors (sources : Array Source) : Array String × NameSet := Id.run do
  let mut errors := #[]
  let mut graph : Std.HashMap Name (Array Import) := {}
  for source in sources do
    graph := graph.insert source.moduleName source.header.imports
    unless source.header.isModule do
      errors := errors.push s!"{source.path} does not use the module system"
    let lines := (source.input.splitOn "\n").length - (if source.input.endsWith "\n" then 1 else 0)
    if lines >= 500 then
      errors := errors.push s!"{source.path} has {lines} lines (must be below 500)"
    for imp in source.header.imports do
      unless allowedImport imp.module do
        errors := errors.push s!"{source.moduleName} imports {imp.module}, outside the package boundary"
  let mut reached : NameSet := {}
  let mut pending : List Name := [`Core]
  while let name :: rest := pending do
    pending := rest
    unless reached.contains name do
      reached := reached.insert name
      if let some imports := graph[name]? then
        for imp in imports do
          if isCoreModule imp.module then
            pending := imp.module :: pending
      else
        errors := errors.push s!"imported module {name} has no source in this package"
  for source in sources do
    unless reached.contains source.moduleName do
      errors := errors.push s!"unreachable module {source.moduleName} in {source.path}"
  return (errors, reached)

/-- An audit view of Core's compiled modules. Importing each one with its private data exposes hidden bodies
    and auxiliaries. External libraries stay at their ordinary interfaces. -/
public meta def auditEnvironment (sources : Array Source) : IO Environment := do
  let imports := sources.filterMap fun source =>
    if source.moduleName == `Core then none
    else some ({ module := source.moduleName, importAll := true } : Import)
  importModules imports {} (level := .exported)

/-- Checks the direct imports serialized by each Core module. Allowed libraries manage their internal
    import graph. In particular, Mathlib's ImportGraph dependency uses Lake's own modules. -/
public meta def compiledImportErrors (env : Environment) : Array String := Id.run do
  let mut errors := #[]
  for (moduleInfo, data) in env.header.modules.zip env.header.moduleData do
    if isCoreModule moduleInfo.module then
      for imp in data.imports do
        unless allowedImport imp.module do
          errors := errors.push s!"compiled module {moduleInfo.module} imports {imp.module} outside the package boundary"
  return errors

public meta def isCoreConstant (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some index => isCoreModule env.header.moduleNames[index.toNat]!
  | none => false

end Gabbro.Core.Waechter
