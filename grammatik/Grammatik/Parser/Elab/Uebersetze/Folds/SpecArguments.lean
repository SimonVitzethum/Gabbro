module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Substitution

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Reuse annotated local elaboration and the existing integer interval calculation.
    A discarded binding is never emitted; unresolved ranges and non-scalar types refuse. -/
def uSpecArgument (ctx : UCtx) (g : String) (i : Nat) (ty : STyp) (arg : SExpr) :
    Except String Unit :=
  let checked : Except String Unit := do
    match ty with
    | .atom "bool" =>
      let _ ← uBool ctx arg
      pure ()
    | .atom _ | .range .. =>
      let .int _ _ ← uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner ty
        | throw "spec parameter is not an integer range"
      let (statement, _) ← uBindWertAllg ctx false "#spec-argument" (some ty) arg
      let .bind _ (some (lo, hi)) value := statement
        | throw "spec argument is not an annotated integer binding"
      let some range := foldRangeWithIndexCheck ctx true value
        | throw "spec argument interval is unresolved"
      if lo ≤ range.1 ∧ range.2 ≤ hi then pure ()
      else throw "spec argument is outside its annotated range"
    | _ => throw "spec parameter is not a scalar type"
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
