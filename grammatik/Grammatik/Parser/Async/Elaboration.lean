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

/-- Generated operands carry their source occurrence. The parser cannot
    construct these reserved builtin names from a source identifier. -/
@[expose] public def segmentValue (position : Nat) (source : SExpr) : SExpr :=
  .built "#async-value" [.lit position, source]

@[expose] public def segmentArgument (position : Nat) (callee : String) (index : Nat)
    (source : SExpr) : SExpr :=
  .built "#async-argument" [.lit position, .lit index, .call callee [source]]

@[expose] public def segmentValueSource : SExpr → SExpr
  | .built "#async-value" [.lit _, source] => source
  | source => source

public theorem segmentValue_names (position : Nat) (source : SExpr) :
    expressionNames (segmentValue position source) = expressionNames source := by
  simp only [segmentValue, expressionNames, argumentNames, List.nil_append, List.append_nil]

public theorem segmentArgument_names (position : Nat) (callee : String) (index : Nat) (source : SExpr) :
    expressionNames (segmentArgument position callee index source) = expressionNames source := by
  simp only [segmentArgument, expressionNames, argumentNames, List.nil_append, List.append_nil]

@[expose] public def tagArguments (position : Nat) (callee : String) : Nat → List SExpr → List SExpr
  | _, [] => []
  | index, source :: rest =>
    segmentArgument position callee index source :: tagArguments position callee (index + 1) rest

@[expose] public def tagFuture (position : Nat) : FutureExpr → FutureExpr
  | .call name args => .call name (tagArguments position name 0 args)
  | .join left right => .join (tagFuture position left) (tagFuture position right)

public theorem tagArguments_names (position : Nat) (callee : String) (index : Nat) (args : List SExpr) :
    argumentNames (tagArguments position callee index args) = argumentNames args := by
  induction args generalizing index with
  | nil => rfl
  | cons source rest ih =>
    simp only [tagArguments, argumentNames, segmentArgument_names, ih]

public theorem tagFuture_names (position : Nat) (future : FutureExpr) :
    futureNames (tagFuture position future) = futureNames future := by
  induction future with
  | call name args => exact tagArguments_names position name 0 args
  | join left right ihLeft ihRight => simp only [tagFuture, futureNames, ihLeft, ihRight]

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
        pure (.await name (tagFuture position future) (analysis.boundary position))
      | _ =>
        if hasAwait value then throw "async: nested await needs control-flow expansion"
        else pure (.bind name (segmentValue position value) (analysis.cost value))
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

/-- Compute the exact fields, commands and terminal expression of the source body. -/
@[expose] public def elaborateBody (analysis : Analysis) (type : STyp)
    (parameters : List (String × STyp)) (body : SAnw) :
    Except String (List (String × STyp) × List Command × SExpr) := do
  let (statements, result) ← splitBody body
  -- `$` cannot occur in a source identifier. The ordinary duplicate-field
  -- check also protects callers supplying manually constructed surface ASTs.
  let (statements, result) := match result with
    | .field future "await" =>
      (statements ++ [.bind false "$async$return" (some type) (.field future "await")],
        .variable "$async$return")
    | _ => (statements, result)
  if hasAwait result then throw "async: bind the awaited result before returning"
  let (fields, commands) ← elaborateCommands analysis 0 statements
  let returned := segmentValue commands.length result
  pure (fields, inferSaved returned (parameters.map Prod.fst) commands, returned)

/-- A checked outer AST retains the complete source signature and its exact body derivation. -/
public structure Elaborated (analysis : Analysis) (source : Function) where
  function : AsyncFn
  checked : AsyncOk function
  name : function.name = source.signature.name
  params : function.params = source.signature.params
  resultType : source.signature.res = some function.resultType
  body : elaborateBody analysis function.resultType source.signature.params source.body =
    .ok (function.fields, function.body, function.result)

@[expose] public def elaborate (analysis : Analysis) (source : Function) :
    Except String (Elaborated analysis source) := do
  if source.signature.generics.isEmpty = false then
    throw "async: instantiate generic declarations before async expansion"
  if source.signature.fehler.isSome then
    throw "async: fallible return needs a modelled result sum"
  match resultType : source.signature.res with
  | none => throw "async: explicit result type required"
  | some type =>
    match body : elaborateBody analysis type source.signature.params source.body with
    | .error error => .error error
    | .ok (fields, commands, result) =>
      let function : AsyncFn := {
        name := source.signature.name
        params := source.signature.params
        resultType := type
        fields := fields
        body := commands
        result := result
        returnCostBound := analysis.cost (segmentValueSource result) }
      if checked : asyncCheck function = true then
        .ok ⟨function, checked, rfl, rfl, resultType, body⟩
      else .error "async: duplicate storage, missing saved local, held lock or ownership mismatch"

/-- Every successful source-layer elaboration uses the existing generic
    transformation theorem; it creates no per-program implementation. -/
public theorem elaborated_refines {analysis : Analysis} (source : Function)
    (result : Elaborated analysis source)
    (model : Model Value Child W) {before after : State Value Child}
    {beforeWorld afterWorld : W} {event : Event Value} {cost : Nat}
    (run : MachinePoll model (asyncExpand model result.function) before beforeWorld event after afterWorld cost) :
    DirectPoll model result.function (decode result.function before) beforeWorld event
      (decode result.function after) afterWorld cost :=
  poll_refines_with_unused_asyncOk model result.function result.checked run

end Gabbro.Grammatik.Parser.AsyncSource
