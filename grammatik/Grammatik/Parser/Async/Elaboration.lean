module

public import Grammatik.Parser.Async.Surface
public import Grammatik.Nebenlaeufigkeit.Async.Regeln

namespace Gabbro.Grammatik.Parser.AsyncSource
open Gabbro.Grammatik.Async

/-! This resolves the finite direct-style source layer, not canonical G
    expressions. An analysis annotation is never a resource/cost certificate.
    The complete source signature stays available for the later G checker. -/

mutual
@[expose] public def hasAwait : SExpr → Bool
  | .field value name => name == "await" || hasAwait value
  | .arrow value _ | .un _ value | .old value => hasAwait value
  | .index left right | .bin _ left right => hasAwait left || hasAwait right
  | .call _ args | .built _ args | .ext _ _ args => argumentsAwait args
  | _ => false
@[expose] public def argumentsAwait : List SExpr → Bool
  | [] => false
  | value :: rest => hasAwait value || argumentsAwait rest
end

/-- `async::join(a(), b())` owns two lazy children. Ordinary calls keep
    their nominal declaration identity. Nested suspension in arguments is
    refused rather than being evaluated as an ordinary record projection. -/
@[expose] public def elaborateFuture : SExpr → Except String FutureExpr
  | .call name args =>
    if name == "async::join" then
      match args with
      | [left, right] => do
        let left ← elaborateFuture left
        let right ← elaborateFuture right
        pure (.join left right)
      | _ => .error "async: join needs two futures"
    else if argumentsAwait args then .error "async: await inside a child argument"
    else .ok (.call name args)
  | _ => .error "async: expected a lazy async call or async::join"

/-- Bounds and authority annotations come from the segment analysis pass.
    They are checked for outer-layer consistency here; G elaboration must
    still discharge canonical typing, HeldB, ownership and cost obligations. -/
public structure Analysis where
  cost : SExpr → Nat
  boundary : Nat → Boundary

@[expose] public def elaborateCommand (analysis : Analysis) (position : Nat) :
    SAnw → Except String ((String × STyp) × Command)
  | .bind false name (some type) value => do
    let command ← match value with
      | .field future "await" => do
        let future ← elaborateFuture future
        pure (.await name future (analysis.boundary position))
      | _ =>
        if hasAwait value then throw "async: nested await needs control-flow expansion"
        else pure (.bind name value (analysis.cost value))
    pure ((name, type), command)
  | .bind _ _ none _ => .error "async: local result type must be explicit"
  | .bind true _ _ _ => .error "async: mutable local needs control-flow expansion"
  | _ => .error "async: only straight-line bindings are modelled across suspension"

@[expose] public def elaborateCommands (analysis : Analysis) : Nat → List SAnw →
    Except String (List (String × STyp) × List Command)
  | _, [] => pure ([], [])
  | position, statement :: rest => do
    let (field, command) ← elaborateCommand analysis position statement
    let (fields, commands) ← elaborateCommands analysis (position + 1) rest
    pure (field :: fields, command :: commands)

/-- Parser blocks keep their terminal return separately. Also accept the
    equivalent manually constructed AST with a last return statement. -/
@[expose] public def splitBody : SAnw → Except String (List SAnw × SExpr)
  | .block statements (some (.ret (some result))) => pure (statements, result)
  | .block statements none =>
    match statements.reverse with
    | .ret (some result) :: rest => pure (rest.reverse, result)
    | _ => .error "async: explicit terminal return required"
  | _ => .error "async: explicit terminal return required"

/-- A checked outer AST retains the original complete source declaration.
    This does not certify the source contracts or grant entry into machine G. -/
public structure Elaborated (source : Function) where
  function : AsyncFn
  checked : AsyncOk function
  name : function.name = source.signature.name
  params : function.params = source.signature.params

@[expose] public def elaborate (analysis : Analysis) (source : Function) :
    Except String (Elaborated source) := do
  if source.signature.generics.isEmpty = false then
    throw "async: instantiate generic declarations before async expansion"
  if source.signature.fehler.isSome then
    throw "async: fallible return needs a modelled result sum"
  let type ← match source.signature.res with
    | some type => pure type
    | none => throw "async: explicit result type required"
  let (statements, result) ← splitBody source.body
  -- `$` cannot occur in a source identifier. The ordinary duplicate-field
  -- check also protects callers supplying manually constructed surface ASTs.
  let (statements, result) := match result with
    | .field future "await" =>
      (statements ++ [.bind false "$async$return" (some type) (.field future "await")],
        .variable "$async$return")
    | _ => (statements, result)
  if hasAwait result then throw "async: bind the awaited result before returning"
  let (fields, commands) ← elaborateCommands analysis 0 statements
  let function : AsyncFn := {
    name := source.signature.name, params := source.signature.params,
    resultType := type, fields := fields, body := commands, result := result,
    returnCostBound := analysis.cost result }
  if checked : asyncCheck function = true then
    pure ⟨function, checked, rfl, rfl⟩
  else throw "async: duplicate storage, missing saved local, held lock or ownership mismatch"

/-- Every successful source-layer elaboration uses the existing generic
    transformation theorem; it creates no per-program implementation. -/
public theorem elaborated_refines (source : Function) (result : Elaborated source)
    (model : Model Value Child) {before after : State Value Child}
    {event : Event Value} {cost : Nat}
    (run : MachinePoll model (asyncExpand model result.function) before event after cost) :
    DirectPoll model result.function (decode result.function before) event
      (decode result.function after) cost :=
  asyncOk_refines model result.function result.checked run

end Gabbro.Grammatik.Parser.AsyncSource
