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
    let scanned ← try
        Core.withCurrHeartbeats do
          let mut found : Array String := #[]
          for (f, t) in (← strukturFeldTypen env s) do
            if enthaeltPropFunktion t && !erlaubt.contains (s, f) then
              found := found.push
                s!"Regel S: structure {s} in module {modulName env s} has the Prop-valued field {f} with no recorded model binding"
          return found
      catch _ => pure #[s!"Regel S: structure {s} in module {modulName env s} could not be scanned within the heartbeat budget"]
    infos := infos ++ scanned
  return infos

/-- A definition type that is `Prop` or a family into `Prop` (shape only, like the binder guard). -/
private meta def istAussagenTyp : Expr → Bool
  | .forallE _ _ b _ => istAussagenTyp b
  | e => e.isProp

/-- Regel N: every `def … : Prop` or Prop-valued family in the closure of the goal statements that does
    not end in `Aussage` is treated like a statement — pin coverage and the binder scan — independent of
    its name. The same holds for a statement-shaped definition outside the goal closure: one that is used
    as a statement, recognised by its `…erfuellbar`, `…nichtTrivial` or `…beweis` companion. Everything is
    reported as information (name, module, reason); no existing statement is changed. -/
public meta def namenloseAussageInfos (env : Environment) (index : DependencyIndex)
    (zielRoots : Array Name) (pinned : Name → Bool) : MetaM (Array String) := do
  let mut ziel : Std.HashSet Name := {}
  for root in zielRoots do
    for name in index.closure root do
      ziel := ziel.insert name
  let mut imZiel : Array Name := #[]
  for name in ziel.toArray.qsort Name.lt do
    if endsWithAussage name then continue
    let some (.defnInfo info) := env.find? name | continue
    unless istAussagenTyp info.type do continue
    imZiel := imZiel.push name
  let mut mitBegleitern : Array Name := #[]
  for name in coreDeclarations env do
    if ziel.contains name || endsWithAussage name then continue
    let some (.defnInfo info) := env.find? name | continue
    unless istAussagenTyp info.type do continue
    unless env.contains (name ++ `erfuellbar) || env.contains (name ++ `nichtTrivial) ||
      env.contains (name ++ `beweis) do continue
    mitBegleitern := mitBegleitern.push name
  let mut infos := #[]
  for name in imZiel ++ mitBegleitern.qsort Name.lt do
    let inZiel := ziel.contains name
    let grund := if inZiel then "used in the goal closure"
      else "used as a statement (has statement companions)"
    unless pinned name do
      infos := infos.push
        s!"Regel N: unnamed statement {name} in module {modulName env name} is {grund} but is not pinned"
    let some (.defnInfo info) := env.find? name | continue
    infos := infos ++ (← statementScan name info true)
  return infos

end Gabbro.Core.Waechter
