module

public import Grammatik.Parser.Spec.Contract

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec

/-- A spec head is a declaration, not a body or a lock-transfer interface. -/
def checkGroup (items : List SItemTief) (g : Group) : Except String Unit := do
  if g.types.isEmpty || !uniqueNames (g.types ++ g.effects) then
    throw "spec.parameters"
  if !uniqueNames (g.functions.map (·.name)) then throw "spec.function.duplicate"
  let specs := items.filterMap fun | .specT s p => some (s.name, s.params.map Prod.fst, p) | _ => none
  for s in g.functions do
    if !uniqueNames (s.params.map Prod.fst) then throw "spec.signature.parameters"
    if !(s.klauseln.all fun
        | .needs _ | .gives _ | .effs _ | .cost _ => true
        | _ => false) then throw "spec.clause"
    if (s.klauseln.filter fun | .effs _ => true | _ => false).length != 1 then
      throw "spec.effects.required"
    if (cost items s).isNone then throw "spec.cost.required"
    if (predicates specs false [] s ++ predicates specs true [] s).any hasHeld then
      throw "spec.held"

/-- The six independent conformance checks after substituting the instance. -/
def checkFunction (items : List SItemTief) (gs : List Group) (ins : List Instance)
    (g : Group) (i : Instance) (abstract concrete : FnSig) : Except String Unit := do
  let env := g.types.zip i.types
  if abstract.params.length != concrete.params.length ||
      !beqSTypList (abstract.params.map fun p => substituteType env p.2)
        (concrete.params.map Prod.snd) ||
      !beqSTypOpt (abstract.res.map (substituteType env)) concrete.res ||
      !beqOptWort abstract.fehler concrete.fehler then
    throw "spec.signature"
  if !uniqueNames (concrete.params.map Prod.fst) then throw "spec.signature.parameters"
  let rename := (concrete.params.map Prod.fst).zip (abstract.params.map fun p => SExpr.variable p.1)
  let specs := items.filterMap fun | .specT s p => some (s.name, s.params.map Prod.fst, p) | _ => none
  if !predicateSubset (predicates specs false rename concrete) (predicates specs false [] abstract) then
    throw "spec.requires"
  if !predicateSubset (predicates specs true [] abstract) (predicates specs true rename concrete) then
    throw "spec.ensures"
  if (concrete.klauseln.any fun | .refs _ => true | _ => false) then
    throw "spec.implementation.refines"
  if (concrete.klauseln.filter fun | .effs _ => true | _ => false).length != 1 then
    throw "spec.effects.required"
  let promised ← expandEffects gs ins env (g.effects.zip i.effects) 1000 (functionEffects abstract)
  let actual ← expandEffects gs ins [] [] 1000 (functionEffects concrete)
  if !(actual.map (renameEffect rename)).all (fun e => promised.any (beqSEffekt e)) then
    throw "spec.effects"
  match cost items concrete, cost items abstract with
  | some a, some b => if a > b then throw "spec.cost"
  | _, _ => throw "spec.cost.required"

/-- A group instance implements exactly its abstract functions and no other item. -/
def checkInstance (items : List SItemTief) (gs : List Group) (ins : List Instance)
    (i : Instance) : Except String Unit := do
  let some g := gs.find? (fun g => strEq g.name i.group)
    | throw ("spec.unknown: " ++ i.group)
  if g.types.length != i.types.length || g.effects.length != i.effects.length then
    throw "spec.arguments"
  -- Effect arguments are concrete: unbound parameters and unknown/cyclic instances refuse here too.
  for es in i.effects do
    let _ ← expandEffects gs ins [] [] 1000 es
  let fs ← i.functions.mapM fun
    | .fnT s _ => pure s
    | _ => throw "spec.implementation.item"
  if !uniqueNames (fs.map (·.name)) then throw "spec.function.duplicate"
  for s in g.functions do
    let some impl := fs.find? (fun t => strEq t.name s.name)
      | throw ("spec.function.missing: " ++ s.name)
    checkFunction items gs ins g i s impl
  if fs.any (fun t => !(g.functions.any fun s => strEq s.name t.name)) then
    throw "spec.function.extra"

/-- The decidable front-end conformance gate; machine G and `Akzeptiert` are unchanged. -/
def check (items : List SItemTief) : Except String Unit := do
  let gs := groups items
  let ins := instances items
  if !uniqueNames (gs.map (·.name)) then throw "spec.duplicate"
  for g in gs do checkGroup items g
  for i in ins do
    if (ins.filter fun j => strEq j.group i.group && beqSTypList j.types i.types).length != 1 then
      throw "spec.implementation.duplicate"
    checkInstance items gs ins i

/-- Conformance is computable as a Bool; named refusals remain available through `check`. -/
def conforms (items : List SItemTief) : Bool := (check items).toOption.isSome

end Gabbro.Grammatik.Parser.Spec
