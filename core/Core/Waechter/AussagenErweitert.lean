module
public meta import Lean
public meta import Core.Waechter.Dependencies
public meta import Core.Waechter.Binder

open Lean Meta

namespace Gabbro.Core.Waechter

/-- Regel S, allow-list of `(structure, field)` pairs whose Prop-valued field the review has tied to a
    model definition. An entry needs a comment naming the binding definition. The list starts empty:
    Regel S first only measures, every candidate is reported as information. -/
public meta def strukturPropErlaubt : Array (Name × Name) := #[]

private meta def modulName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some idx => (env.header.modules[idx.toNat]!.module).toString
  | none => "unknown module"

/-- True when `type` ends in `Prop` after stripping binders (shape only, no unfolding). -/
private meta def endetInProp : Expr → Bool
  | .forallE _ _ b _ => endetInProp b
  | e => e.isProp

/-- True when `type` contains a function into `Prop` anywhere: a Prop-valued field itself, a function
    field returning `Prop`, or a container of predicates such as `List (Zustand → Prop)`. -/
private meta def enthaeltPropFunktion : Expr → Bool
  | .forallE _ d b _ => endetInProp b || enthaeltPropFunktion d || enthaeltPropFunktion b
  | .lam _ d b _ => enthaeltPropFunktion d || enthaeltPropFunktion b
  | .letE _ t v b _ => enthaeltPropFunktion t || enthaeltPropFunktion v || enthaeltPropFunktion b
  | .app f a => enthaeltPropFunktion f || enthaeltPropFunktion a
  | .mdata _ b => enthaeltPropFunktion b
  | .proj _ _ b => enthaeltPropFunktion b
  | _ => false

/-- Every constant any Core proof (`theorem`) refers to. A Prop-valued field or an unnamed
    proposition that a proof mentions carries statement content, even when no pin or goal closure
    reaches it: the proof is what uses it as a statement. One pure pass, like the declaration audit. -/
private meta def beweisVerwendung (env : Environment) : Std.HashSet Name := Id.run do
  let mut used : Std.HashSet Name := {}
  for name in coreDeclarations env do
    match env.find? name with
    | some cinfo@(.thmInfo _) =>
      for dep in cinfo.getUsedConstantsAsSet.toArray do
        used := used.insert dep
    | _ => pure ()
  return used

/-- The `(field, type)` pairs of a structure, from its single constructor, without its parameters. -/
private meta def strukturFeldTypen (env : Environment) (s : Name) :
    MetaM (Array (Name × Expr)) := do
  let some (.inductInfo ival) := env.find? s
    | throwError "not an inductive type"
  unless ival.ctors.length == 1 do throwError "not a single-constructor type"
  let some (.ctorInfo cval) := env.find? ival.ctors[0]!
    | throwError "missing constructor"
  forallTelescope cval.type fun xs _ => do
    let mut out := #[]
    for i in [ival.numParams:xs.size] do
      let decl ← xs[i]!.fvarId!.getDecl
      out := out.push (decl.userName, decl.type)
    return out

/-- Scan one structure for Prop-valued fields, with its own heartbeat budget. `grund` names why
    the structure is in scope. -/
private meta def strukturScan (env : Environment) (erlaubt : Std.HashSet (Name × Name))
    (s : Name) (grund : String) : MetaM (Array String) := do
  try
    Core.withCurrHeartbeats do
      let mut found : Array String := #[]
      for (f, t) in (← strukturFeldTypen env s) do
        if enthaeltPropFunktion t && !erlaubt.contains (s, f) then
          found := found.push
            s!"Regel S: structure {s} in module {modulName env s} has the Prop-valued field {f} with no recorded model binding{grund}"
      return found
  catch _ => return #[s!"Regel S: structure {s} in module {modulName env s} could not be scanned within the heartbeat budget"]

/-- Regel S: every structure in the closure of the pin roots whose fields are Prop-valued or functions
    into `Prop` is reported as information (name, module, reason), unless the field is allow-listed.
    Whether a Prop field is bound to a model definition is a review judgement recorded in
    `strukturPropErlaubt`; the guard lists every candidate so the review measures first. -/
public meta def strukturPropInfos (env : Environment) (index : DependencyIndex)
    (pinRoots : Array Name) : MetaM (Array String) := do
  let mut union : Std.HashSet Name := {}
  for root in pinRoots do
    for name in index.closure root do
      union := union.insert name
  let mut erlaubt : Std.HashSet (Name × Name) := {}
  for entry in strukturPropErlaubt do
    erlaubt := erlaubt.insert entry
  let mut infos := #[]
  for s in union.toArray.qsort Name.lt do
    unless Lean.isStructure env s do continue
    infos := infos ++ (← strukturScan env erlaubt s "")
  return infos

/-- Regel S, orphan clause: a structure outside every pin closure whose fields are Prop-valued still
    carries statement content when a proof refers to it (measured examples: `UnitMitInvarianten`,
    whose predicates no pin closure reaches, and the `EffektSicht` records). It is reported with the
    same shape and reason, marked as outside the closures. -/
public meta def strukturPropWaisenInfos (env : Environment) (abgedeckt : Name → Bool) :
    MetaM (Array String) := do
  let verwendung := beweisVerwendung env
  let mut erlaubt : Std.HashSet (Name × Name) := {}
  for entry in strukturPropErlaubt do
    erlaubt := erlaubt.insert entry
  let mut infos := #[]
  for s in coreDeclarations env do
    if abgedeckt s || !verwendung.contains s then continue
    unless Lean.isStructure env s do continue
    infos := infos ++ (← strukturScan env erlaubt s " (outside every pin closure, used by a proof)")
  return infos

/-- A definition type that is `Prop` or a family into `Prop` (shape only, like the binder guard). -/
private meta def istAussagenTyp : Expr → Bool
  | .forallE _ _ b _ => istAussagenTyp b
  | e => e.isProp

/-- Regel N: every `def … : Prop` or Prop-valued family in the closure of the goal statements that does
    not end in `Aussage` is treated like a statement — pin coverage and the binder scan — independent of
    its name. The same holds outside the goal closure for a definition that is used as a statement:
    one with `…erfuellbar`, `…nichtTrivial` or `…beweis` companions, or one a proof refers to (measured
    example: `PegelNISatz`, reached by no closure, whose proof still uses it as a statement). Everything is
    reported as information (name, module, reason); no existing statement is changed. -/
public meta def namenloseAussageInfos (env : Environment) (index : DependencyIndex)
    (zielRoots : Array Name) (pinned : Name → Bool) : MetaM (Array String) := do
  let mut ziel : Std.HashSet Name := {}
  for root in zielRoots do
    for name in index.closure root do
      ziel := ziel.insert name
  let verwendung := beweisVerwendung env
  let mut imZiel : Array Name := #[]
  for name in ziel.toArray.qsort Name.lt do
    if endsWithAussage name then continue
    let some (.defnInfo info) := env.find? name | continue
    unless istAussagenTyp info.type do continue
    imZiel := imZiel.push name
  let mut waisen : Array (Name × String) := #[]
  for name in coreDeclarations env do
    if ziel.contains name || endsWithAussage name then continue
    let some (.defnInfo info) := env.find? name | continue
    unless istAussagenTyp info.type do continue
    let begleiter := env.contains (name ++ `erfuellbar) || env.contains (name ++ `nichtTrivial) ||
      env.contains (name ++ `beweis)
    let beweis := verwendung.contains name
    if begleiter && beweis then
      waisen := waisen.push (name, "has statement companions and is referenced by a proof")
    else if begleiter then
      waisen := waisen.push (name, "has statement companions")
    else if beweis then
      waisen := waisen.push (name, "is referenced by a proof")
    else continue
  let mut infos := #[]
  for name in imZiel do
    unless pinned name do
      infos := infos.push
        s!"Regel N: unnamed statement {name} in module {modulName env name} is used in the goal closure but is not pinned"
    let some (.defnInfo info) := env.find? name | continue
    infos := infos ++ (← statementScan name info true)
  for (name, grund) in waisen.qsort fun a b => a.1.lt b.1 do
    unless pinned name do
      infos := infos.push
        s!"Regel N: unnamed statement {name} in module {modulName env name} is used as a statement outside the goal closure ({grund}) but is not pinned"
    let some (.defnInfo info) := env.find? name | continue
    infos := infos ++ (← statementScan name info true)
  return infos

end Gabbro.Core.Waechter
