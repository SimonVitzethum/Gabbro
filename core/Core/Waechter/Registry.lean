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

public meta structure RegistryFamily where
  inductiveName : Name
  schema : Name
  entries : Array (Name × Name)
  openEntries : Array (Name × Name) := #[]

/-- Open proof packets have an actual proposition pinned by the guard. -/
public meta def openRegistryErrors (packets : Array (Name × Name)) (pinNames : Array Name)
    (closing : Bool) : MetaM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  for (form, packet) in packets do
    let valid ← match env.find? packet with
      | some (.defnInfo info) =>
        pure (isCoreConstant env packet && pinNames.contains packet && info.type.isProp)
      | _ => pure false
    if !valid then
      errors := errors.push s!"open registry form {form} lacks a pinned proposition {packet}"
    else if closing then
      errors := errors.push s!"open registry form {form} still requires proofs for {packet}"
    else
      logInfo m!"open registry form {form} requires proofs for {packet}"
  return errors

/-- Compares configured families with Lean's actual constructor lists. Each constructor must have one
    Core declaration of type `RegistryEntry constructor (schema constructor)`. The schema selects source
    or internal origin per constructor and is fixed by the language definitions. This guard checks coverage
    and typing. The intended meaning and non-degeneracy of the propositions require review and pins. -/
public meta def registryErrors (families : Array RegistryFamily) (pinNames : Array Name)
    (closing : Bool) : MetaM (Array String) := do
  let env ← getEnv
  let mut errors := #[]
  let mut registered : NameSet := {}
  for family in families do
    if registered.contains family.inductiveName then
      errors := errors.push s!"duplicate registry family {family.inductiveName}"
    registered := registered.insert family.inductiveName
    let some (.inductInfo info) := env.find? family.inductiveName |
      errors := errors.push s!"expected an inductive for registry family {family.inductiveName}"
      continue
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
    for (ctor, _) in family.openEntries do
      if !info.ctors.contains ctor then
        errors := errors.push s!"unknown open registry constructor {ctor} for {info.name}"
        continue
      if supplied.contains ctor then
        errors := errors.push s!"duplicate registry entry for {ctor}"
      supplied := supplied.insert ctor
    errors := errors ++ (← openRegistryErrors family.openEntries pinNames closing)
    for ctor in info.ctors do
      unless supplied.contains ctor do
        errors := errors.push s!"missing registry entry for {ctor}"
  return errors

end Gabbro.Core.Waechter
