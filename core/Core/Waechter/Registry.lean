module
public meta import Lean
public meta import Core.Waechter.Dependencies

open Lean Meta

namespace Gabbro.Core.Waechter

public inductive RegistryOrigin where
  | surface
  | core

public inductive OriginStatements : RegistryOrigin → Type where
  | surface (parse elaboration occurrence : Prop) : OriginStatements .surface
  | core (origin : Prop) : OriginStatements .core

public inductive OriginProofs : {origin : RegistryOrigin} → OriginStatements origin → Type where
  | surface {P E O : Prop} (parse : P) (elaboration : E) (occurrence : O) :
      OriginProofs (.surface P E O)
  | core {P : Prop} (origin : P) : OriginProofs (.core P)

public structure RegistryStatements (_constructor : Name) (origin : RegistryOrigin) where
  realization : OriginStatements origin
  acceptanceRule : Prop
  idealRule : Prop
  unitsAndCommutation : Prop
  implementationRule : Prop
  preservation : Prop
  jointlySatisfiable : Prop

public structure RegistrySchema (constructor : Name) where
  origin : RegistryOrigin
  statements : RegistryStatements constructor origin

public structure RegistryEntry (constructor : Name) (schema : RegistrySchema constructor) where
  realization : OriginProofs schema.statements.realization
  acceptanceRule : schema.statements.acceptanceRule
  idealRule : schema.statements.idealRule
  unitsAndCommutation : schema.statements.unitsAndCommutation
  implementationRule : schema.statements.implementationRule
  preservation : schema.statements.preservation
  jointlySatisfiable : schema.statements.jointlySatisfiable

/-- Evidence for the complete pinned packet of a constructor or an auxiliary form. -/
public structure RegistryPacketProof (_form : Name) (packet : Prop) : Prop where
  proof : packet

/-- A scoped constructor must carry the standard schema and every pinned packet obligation. -/
public structure RegistryPacketEntry (constructor : Name) (schema : RegistrySchema constructor)
    (packet : Prop) where
  entry : RegistryEntry constructor schema
  packetProof : packet

public meta structure RegistryPacket where
  form : Name
  statement : Name
  proof : Option Name := none

public meta structure RegistryFamily where
  inductiveName : Name
  schema : Name
  entries : Array (Name × Name)
  openEntries : Array (Name × Name) := #[]

private meta def packetErrors (row : RegistryPacket) (pinNames : Array Name)
    (closing : Bool) (expected : Expr) : MetaM (Array String) := do
  let env ← getEnv
  let valid := match env.find? row.statement with
    | some (.defnInfo info) =>
      isCoreConstant env row.statement && pinNames.contains row.statement && info.type.isProp
    | _ => false
  unless valid do
    return #[s!"registry form {row.form} lacks a pinned proposition {row.statement}"]
  if let some proof := row.proof then
    if let some info := env.find? proof then
      if isCoreConstant env proof && (← isDefEq info.type expected) then
        return #[]
    return #[s!"registry entry {proof} lacks the required typed proofs for {row.form} ({row.statement})"]
  if closing then
    return #[s!"open registry form {row.form} still requires proofs for {row.statement}"]
  logInfo m!"open registry form {row.form} requires proofs for {row.statement}"
  return #[]

/-- Auxiliary forms carry their own pinned propositions. For configured inductives
    the guard can also compare their rows with the actual constructors. -/
public meta def auxiliaryRegistryErrors (rows : Array RegistryPacket) (pinNames : Array Name)
    (closing : Bool) (families : Array Name) : MetaM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  let mut supplied : NameSet := {}
  for row in rows do
    if supplied.contains row.form then
      errors := errors.push s!"duplicate auxiliary registry entry for {row.form}"
    else
      supplied := supplied.insert row.form
      unless isCoreConstant env row.form do
        errors := errors.push s!"unknown auxiliary registry form {row.form}"
      let expected := mkApp2 (mkConst ``RegistryPacketProof) (toExpr row.form) (mkConst row.statement)
      errors := errors ++ (← packetErrors row pinNames closing expected)
  for family in families do
    let some (.inductInfo info) := env.find? family |
      errors := errors.push s!"expected an inductive for auxiliary registry family {family}"
      continue
    unless isCoreConstant env family do
      errors := errors.push s!"auxiliary registry family {family} is outside Core"
    for ctor in info.ctors do
      unless supplied.contains ctor do
        errors := errors.push s!"missing auxiliary registry entry for {ctor}"
  return errors

/-- Compares configured families with Lean's actual constructor lists. Each constructor must have one
    Core declaration of type `RegistryEntry constructor (schema constructor)`. The schema selects source
    or internal origin per constructor and is fixed by the language definitions. This guard checks coverage
    and typing. The intended meaning and non-degeneracy of the propositions require review and pins. -/
public meta def registryErrors (families : Array RegistryFamily) (packetEntries : Array RegistryPacket)
    (pinNames : Array Name) (closing : Bool) : MetaM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  let mut registered : NameSet := {}
  let mut constructors : NameSet := {}
  for family in families do
    if registered.contains family.inductiveName then
      errors := errors.push s!"duplicate registry family {family.inductiveName}"
    registered := registered.insert family.inductiveName
    let some (.inductInfo info) := env.find? family.inductiveName |
      errors := errors.push s!"expected an inductive for registry family {family.inductiveName}"
      continue
    for ctor in info.ctors do
      constructors := constructors.insert ctor
    unless isCoreConstant env info.name do
      errors := errors.push s!"registry family {info.name} is outside Core"
    let schemaType := mkForall `constructor .default (mkConst ``Name)
      (mkApp (mkConst ``RegistrySchema) (mkBVar 0))
    let schemaOK ← match env.find? family.schema with
      | some schema =>
        if isCoreConstant env schema.name then isDefEq schema.type schemaType else pure false
      | none => pure false
    unless schemaOK do
      errors := errors.push s!"invalid registry schema function {family.schema}"
    let mut supplied : NameSet := {}
    for (ctor, entry) in family.entries do
      if !info.ctors.contains ctor then
        errors := errors.push s!"unknown registry constructor {ctor} for {info.name}"
        continue
      if supplied.contains ctor then
        errors := errors.push s!"duplicate registry entry for {ctor}"
      supplied := supplied.insert ctor
      let some value := env.find? entry |
        errors := errors.push s!"registry entry declaration {entry} is missing"
        continue
      let index := toExpr ctor
      let expected := mkApp2 (mkConst ``RegistryEntry) index (mkApp (mkConst family.schema) index)
      if !isCoreConstant env entry || !schemaOK || !(← isDefEq value.type expected) then
        errors := errors.push s!"registry entry {entry} lacks the required typed proofs for {ctor}"
    let packetRows := (packetEntries.filter fun row => info.ctors.contains row.form) ++
      family.openEntries.map (fun (form, packet) => ⟨form, packet, none⟩)
    for row in packetRows do
      let ctor := row.form
      if !info.ctors.contains ctor then
        errors := errors.push s!"unknown registry constructor {ctor} for {info.name}"
        continue
      if supplied.contains ctor then
        errors := errors.push s!"duplicate registry entry for {ctor}"
      supplied := supplied.insert ctor
      if schemaOK then
        let index := toExpr ctor
        let expected := mkApp3 (mkConst ``RegistryPacketEntry) index (mkApp (mkConst family.schema) index)
          (mkConst row.statement)
        errors := errors ++ (← packetErrors row pinNames closing expected)
    for ctor in info.ctors do
      unless supplied.contains ctor do
        errors := errors.push s!"missing registry entry for {ctor}"
  for row in packetEntries do
    unless constructors.contains row.form do
      errors := errors.push s!"unknown packet registry constructor {row.form}"
  return errors

end Gabbro.Core.Waechter
