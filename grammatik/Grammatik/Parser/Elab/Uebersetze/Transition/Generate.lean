module

public import Grammatik.Parser.Elab.Uebersetze.Transition.Elaborate

public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- A generated function never admits duplicate or potentially aliasing
    targets without an agreement proof. Distinct fields/globals are separate. -/
@[expose] def uTransitionDisjoint : UTransitionPlace → UTransitionPlace → Bool
  | .glob a, .glob b => a != b
  | .glob _, .slot .. | .slot .., .glob _ => true
  | .slot a f i, .slot b g j =>
    a != b || f != g || match i, j with
      | .lit i, .lit j => i != j
      | _, _ => false
  | _, _ => false

/-- The private captured parameters of the write at `position`. -/
@[expose] def uTransitionIndexName (position : Nat) : String := "#index" ++ toString position
@[expose] def uTransitionSourceName (position : Nat) : String := "#source" ++ toString position
@[expose] def uTransitionTargetName (position : Nat) : String := "#target" ++ toString position

/-- The caller-side provenance of the captured parameters: each equals the
    expression it snapshots at entry. A constant edge captures only its index. -/
@[expose] def uTransitionProvenance (position : Nat) (shift : Bool) (w : UTransitionWrite) :
    List UEns :=
  let endpoints := if shift then [] else
    [UEns.cmp "==" (.param (uTransitionSourceName position)) w.source,
     UEns.cmp "==" (.param (uTransitionTargetName position)) w.target]
  match w.place with
  | .slot _ _ (.param "#transitionIndex") => endpoints
  | .slot _ _ (.lit n) => .cmp "==" (.param (uTransitionIndexName position)) (.lit n) :: endpoints
  | .slot _ _ (.param n) => .cmp "==" (.param (uTransitionIndexName position)) (.param n) :: endpoints
  | _ => endpoints

/-- Relative indices of one declaration agree. -/
@[expose] def uTransitionSameIndex (writes : List UTransitionWrite) : List UEns :=
  match ((List.range writes.length).zip writes).filterMap (fun (j, w) =>
      match w.place with
      | .slot _ _ (.param "#transitionIndex") => some (uTransitionIndexName j)
      | _ => none) with
  | [] => []
  | first :: rest => rest.map (fun index => UEns.cmp "==" (.param index) (.param first))

/-- The caller duties the typed expansion lowers with the ordinary predicate
    reader: the declaration clause, relative-index agreement and the capture
    provenance. The source-stage equalities are the typed expansion's own. -/
@[expose] def uTransitionAssumptions (tr : UTransition) : List UEns :=
  tr.clause :: (uTransitionSameIndex tr.writes ++
    ((List.range tr.writes.length).zip tr.writes).flatMap
      (fun (j, w) => uTransitionProvenance j (uTransitionShift tr) w))

/-- Exact fields of one generated function, accumulated in source order. -/
structure UTransitionFragment where
  params : List (String × Ty)
  kinds : List UParamArt
  sourceEq : List UEns
  gives : List UEns
  body : List UStmt
  deriving DecidableEq, Repr

/-- Use the same declared numeric field/global range as ordinary lowering. -/
@[expose] def uTransitionRange (tabs : List UTab) (globs : List UGlob) :
    UTransitionPlace → Except String (Int × Int)
  | .glob name =>
    match globs.find? (fun g => strEq g.name name) with
    | none => .error ("transition global unknown: " ++ name)
    | some g => match g.ty with
      | .int lo hi => .ok (lo, hi)
      | _ => .error "transition endpoints require an integer global"
  | .slot table field _ =>
    match tabs.find? (fun t => strEq t.name table) with
    | none => .error ("transition table unknown: " ++ table)
    | some t =>
      if t.bools.any (strEq · field) || t.opts.any (fun p => strEq p.1 field) ||
          t.werte.any (fun p => strEq p.1 field) || t.sumNamen.any (fun p => strEq p.1 field) then
        .error "transition endpoints require an integer field"
      else match t.cols.find? (fun p => strEq p.1 field) with
        | some (_, range) => .ok range
        | none => .error ("transition field unknown: " ++ field)
  | .relative _ => .error "transition target scope unresolved"

/-- Capture parameters carry declared ranges. Requires binds them to the
    entry expressions, so an ordinary caller cannot fabricate endpoint values.
    Ensures refers only to parameters, never body locals. A constant edge keeps
    its literals and ends in the primitive shift of its governing state. -/
@[expose] def uTransitionFragment (tabs : List UTab) (globs : List UGlob) (state : String)
    (shift : Bool) (position : Nat) (write : UTransitionWrite) :
    Except String UTransitionFragment := do
  let range ← uTransitionRange tabs globs write.place
  let source := uTransitionSourceName position
  let target := uTransitionTargetName position
  let endpoints := [(source, Ty.int range.1 range.2), (target, Ty.int range.1 range.2)]
  match write.place with
  | .relative _ => throw "transition target scope unresolved"
  | .glob global =>
    pure { params := endpoints, kinds := [.int, .int],
      sourceEq := [.cmp "==" (.glob global) (.param source)],
      gives := [.cmp "==" (.glob global) (.param target)],
      body := [.assignGlob global (.param target)] }
  | .slot table field _ =>
    let numbered ← uTabNr tabs table
    let index := uTransitionIndexName position
    let frozen := UIdx.param index
    if shift then
      (match write.source, write.target with
      | .lit a, .lit b =>
        pure { params := [(index, Ty.index numbered.2)], kinds := [.index numbered.1],
          sourceEq := [.cmp "==" (.tab table field frozen) (.lit a)],
          gives := [.cmp "==" (.tab table field frozen) (.lit b)],
          body := [.shiftTab table field frozen state a b] }
      | _, _ => throw "constant transition edge expected")
    else
      pure { params := (index, Ty.index numbered.2) :: endpoints,
        kinds := .index numbered.1 :: [.int, .int],
        sourceEq := [.cmp "==" (.tab table field frozen) (.param source)],
        gives := [.cmp "==" (.tab table field frozen) (.param target)],
        body := [.assignTab table field frozen (.param target)] }

/-- Generate the ordinary function of a declaration. The typed lowering
    (`lowTransitionAt`) accepts a function of this name only if it is exactly
    this value, and builds its requires, ensures and body as the expansion. -/
@[expose] def uGenerateTransition (tabs : List UTab) (globs : List UGlob) (state : String)
    (tr : UTransition) : Except String UFn := do
  if ¬ (tr.writes.map (·.place)).Pairwise (fun a b => uTransitionDisjoint a b = true) then
    throw "transition targets alias or lack an equal-result agreement proof"
  let fragments ← uSeq (((List.range tr.writes.length).zip tr.writes).map fun (j, w) =>
    uTransitionFragment tabs globs state (uTransitionShift tr) j w)
  pure { name := uTransitionFunction state tr.name,
    params := fragments.flatMap (·.params), kinds := fragments.flatMap (·.kinds), res := none,
    held := tr.held, puts := tr.puts, gputs := tr.gputs,
    needs := uTransitionAssumptions tr ++ fragments.flatMap (·.sourceEq),
    gives := fragments.flatMap (·.gives),
    body := fragments.flatMap (·.body), ret := .empty }

/-- Every nonprimitive declaration gets its own function, including an
    unused declaration. No reachable support function is omitted by demand. -/
@[expose] def uGenerateTransitions (tabs : List UTab) (globs : List UGlob)
    (states : List UZustand) : Except String (List UFn) := do
  let functions ← uSeq (states.flatMap fun state => state.transitions.filterMap fun tr =>
    if tr.primitive then none else some (uGenerateTransition tabs globs state.name tr))
  if (uEindeutig (functions.map (·.name))).length != functions.length then
    throw "duplicate generated transition function identity"
  pure functions

end Gabbro.Grammatik.Parser.Uebersetze
