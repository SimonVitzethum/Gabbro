module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Substitution

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Typed value paths consist of a name and ordinary record projections.
    Their types come from the lexical declaration and its record schema. -/
def uSpecValuePath : SExpr → Bool
  | .variable _ => true
  | .field base _ => uSpecValuePath base
  | _ => false

/-- Compare full value types, including the record identity, element type,
    array length and string bound. Only paths have a type independently of
    later dependent checking of constructed values. -/
def uSpecValueArgument (ctx : UCtx) (expected : Ty) (argument : SExpr) : Except String Unit := do
  if !uSpecValuePath argument then throw "spec value argument must be a typed place"
  let side ← uWertBody ctx argument
  if uValueType ctx side = some expected then pure ()
  else throw "spec value argument does not have the declared type"

theorem uSpecValueArgument_exact {ctx : UCtx} {expected : Ty} {argument : SExpr}
    (accepted : uSpecValueArgument ctx expected argument = .ok ()) :
    uSpecValuePath argument = true ∧ ∃ side,
      uWertBody ctx argument = .ok side ∧ uValueType ctx side = some expected := by
  cases path : uSpecValuePath argument with
  | false => simp [uSpecValueArgument, path, bind, Except.bind] at accepted
  | true =>
    cases read : uWertBody ctx argument with
    | error err => simp [uSpecValueArgument, path, read, bind, Except.bind] at accepted
    | ok side =>
      by_cases typeMatches : uValueType ctx side = some expected
      · exact ⟨rfl, side, rfl, typeMatches⟩
      · simp [uSpecValueArgument, path, read, typeMatches, bind, Except.bind] at accepted

theorem specValueArgument_erfuellbar (ctx : UCtx) (name : String) (expected : Ty)
    (read : uWertBody ctx (.variable name) = .ok (.param name))
    (typeMatches : uValueType ctx (.param name) = some expected) :
    uSpecValueArgument ctx expected (.variable name) = .ok () := by
  simp [uSpecValueArgument, uSpecValuePath, read, typeMatches, bind, Except.bind, pure, Except.pure]

/-- Reuse annotated local elaboration and the existing integer interval calculation.
    Structured and floating values use their exact declared path types. -/
def uSpecArgument (ctx : UCtx) (g : String) (i : Nat) (ty : STyp) (arg : SExpr) :
    Except String Unit :=
  let checked : Except String Unit := do
    let expected ← uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner ty
    match expected with
    | .bool =>
      let _ ← uBool ctx arg
      pure ()
    | .int .. =>
      let (statement, _) ← uBindWertAllg ctx false "#spec-argument" (some ty) arg
      let .bind _ (some (lo, hi)) value := statement
        | throw "spec argument is not an annotated integer binding"
      let some range := foldRangeWithIndexCheck ctx true value
        | throw "spec argument interval is unresolved"
      if lo ≤ range.1 ∧ range.2 ≤ hi then pure ()
      else throw "spec argument is outside its annotated range"
    | .prod .. | .arr .. | .str .. | .fl .. =>
      uSpecValueArgument ctx expected arg
    | _ => throw "spec parameter type is unsupported"
  match checked with
  | .ok () => .ok ()
  | .error _ => .error ("spec " ++ g ++ ": argument " ++ toString i ++
      " does not fit its parameter type")

/-- Check every original call before inlining, including calls brought by a helper's body.
    Argument expressions use the caller's scope; quantifiers extend it with their real domain.
    Exhausted expansion refuses instead of allowing an unchecked recursive helper. -/
def uSpecArgs : Nat → UCtx → SExpr → Except String Unit
  | 0, _, _ => .error "spec argument checking exceeded its expansion depth"
  | n + 1, ctx, e => do
    match e with
    | .call g args =>
      for arg in args do uSpecArgs n ctx arg
      match ctx.specs.find? (fun p => strEq p.1 g) with
      | some (_, _, body) =>
        for (arg, i) in args.zipIdx do
          if specArgumentCaptures body (uSpecEin ctx.specs n arg) then
            throw ("spec " ++ g ++ ": argument " ++ toString (i + 1) ++
              " names a binder of the predicate")
      | none => pure ()
      match ctx.specTypen.find? (fun p => strEq p.1 g) with
      | some (_, types) =>
        if args.length != types.length then
          throw ("spec " ++ g ++ ": argument " ++ toString (min args.length types.length + 1) ++
            " does not fit its parameter type")
        for ((ty, arg), i) in (types.zip args).zipIdx do
          uSpecArgument ctx g (i + 1) ty (uSpecEin ctx.specs n arg)
      | none => pure ()
      match ctx.specs.find? (fun p => strEq p.1 g) with
      | some (_, names, body) =>
        if names.length == args.length then
          uSpecArgs n ctx (sErsetze (names.zip args) 1000 body)
        else throw ("spec " ++ g ++ ": argument count does not fit its parameter type")
      | none => pure ()
    | .field a _ | .arrow a _ | .un _ a | .old a => uSpecArgs n ctx a
    | .index a b | .bin _ a b =>
      uSpecArgs n ctx a
      uSpecArgs n ctx b
    | .ext k [binder, domain] [subject, body] =>
      if k == .all || k == .any || k == .count then
        uSpecArgs n ctx subject
        -- Read the predicate domain directly: array quantifiers need no traversal carrier.
        let inner ← if domain == "elems" then do
            let (_, _, count) ← uArrayDomain ctx subject
            pure (uMitLokal ctx binder .int (Ty.index count) ctx.muts)
          else do
            let (_, inner, _) ← uLoopExport ctx binder none domain subject "unvisited" "" none
            pure inner
        uSpecArgs n inner body
      else
        uSpecArgs n ctx subject
        uSpecArgs n ctx body
    | .built _ args | .ext _ _ args =>
      for arg in args do uSpecArgs n ctx arg
    | _ => pure ()

end Gabbro.Grammatik.Parser.Uebersetze
