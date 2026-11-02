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

/-- Exact fields of one generated function, accumulated in source order. -/
structure UTransitionFragment where
  params : List (String × Ty)
  kinds : List UParamArt
  arguments : List UArg
  needs : List UEns
  gives : List UEns
  body : List UStmt
  deriving DecidableEq, Repr

/-- Use the same declared numeric field/global range as ordinary lowering. -/
@[expose] def uTransitionRange (ctx : UCtx) : UTransitionPlace → Except String (Int × Int)
  | .glob name =>
    match ctx.globs.find? (fun g => strEq g.name name) with
    | none => .error ("transition global unknown: " ++ name)
    | some g => match g.ty with
      | .int lo hi => .ok (lo, hi)
      | _ => .error "transition endpoints require an integer global"
  | .slot table field _ =>
    match ctx.tabs.find? (fun t => strEq t.name table) with
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
    Ensures refers only to parameters, never body locals. -/
@[expose] def uTransitionFragment (ctx : UCtx) (position : Nat) (write : UTransitionWrite) :
    Except String UTransitionFragment := do
  let range ← uTransitionRange ctx write.place
  let source := "#source" ++ toString position
  let target := "#target" ++ toString position
  let endpoints := [(source, Ty.int range.1 range.2), (target, Ty.int range.1 range.2)]
  let provenance := [UEns.cmp "==" (.param source) write.source,
    UEns.cmp "==" (.param target) write.target]
  let args := [UArg.val write.source, UArg.val write.target]
  match write.place with
  | .relative _ => throw "transition target scope unresolved"
  | .glob global =>
    pure { params := endpoints, kinds := [.int, .int], arguments := args,
      needs := provenance ++ [.cmp "==" (.glob global) (.param source)],
      gives := [.cmp "==" (.glob global) (.param target)],
      body := [.assignGlob global (.param target)] }
  | .slot table field original =>
    let (number, count) ← uTabNr ctx.tabs table
    let index := "#index" ++ toString position
    let frozen := UIdx.param index
    let provenance := match original with
      | .param "#transitionIndex" => provenance
      | .lit n => .cmp "==" (.param index) (.lit n) :: provenance
      | .param n => .cmp "==" (.param index) (.param n) :: provenance
    pure { params := (index, Ty.index count) :: endpoints,
      kinds := .index number :: [.int, .int],
      arguments := UArg.val (match original with | .lit n => .lit n | .param n => .param n) :: args,
      needs := provenance ++ [.cmp "==" (.tab table field frozen) (.param source)],
      gives := [.cmp "==" (.tab table field frozen) (.param target)],
      body := [.assignTab table field frozen (.param target)] }

/-- Generate a candidate ordinary function. The normal function lowerer
    still checks ranges, guards, resources, calls, footprints and contracts.
    Source admission additionally requires the expansion certificate. -/
@[expose] def uGenerateTransition (ctx : UCtx) (state : String) (tr : UTransition) : Except String UFn := do
  if ¬ (tr.writes.map (·.place)).Pairwise (fun a b => uTransitionDisjoint a b = true) then
    throw "transition targets alias or lack an equal-result agreement proof"
  let fragments ← uSeq ((List.range tr.writes.length).zip tr.writes |>.map fun (j, w) =>
    uTransitionFragment ctx j w)
  let relativeIndices := (List.range tr.writes.length).zip tr.writes |>.filterMap fun (j, w) =>
    match w.place with
    | .slot _ _ (.param "#transitionIndex") => some ("#index" ++ toString j)
    | _ => none
  let sameIndex := match relativeIndices with
    | [] => []
    | first :: rest => rest.map (fun index => UEns.cmp "==" (.param index) (.param first))
  pure { name := uTransitionFunction state tr.name,
    params := fragments.flatMap (·.params), kinds := fragments.flatMap (·.kinds), res := none,
    held := tr.held, puts := tr.puts, gputs := tr.gputs,
    needs := tr.clause :: (sameIndex ++ fragments.flatMap (·.needs)), gives := fragments.flatMap (·.gives),
    body := fragments.flatMap (·.body), ret := .empty }

/-- Every nonprimitive declaration gets its own function, including an
    unused declaration. No reachable support function is omitted by demand. -/
@[expose] def uGenerateTransitions (ctx : UCtx) (states : List UZustand) : Except String (List UFn) := do
  let functions ← uSeq (states.flatMap fun state => state.transitions.filterMap fun tr =>
    if tr.primitive then none else some (uGenerateTransition ctx state.name tr))
  if (uEindeutig (functions.map (·.name))).length != functions.length then
    throw "duplicate generated transition function identity"
  pure functions

/-- Candidate generation alone cannot discharge the generic source-to-G
    expansion theorem. Keep this named refusal until that certificate is
    constructed by ordinary lowering; never mark the package accepted from
    tests or from a body-only semantic theorem. -/
@[expose] def uTransitionExportGate (states : List UZustand) : Except String Unit :=
  if states.any (fun state => state.transitions.any (fun tr => !tr.primitive)) then
    .error "source transition expansion lacks a checked source-to-G certificate"
  else .ok ()

end Gabbro.Grammatik.Parser.Uebersetze
