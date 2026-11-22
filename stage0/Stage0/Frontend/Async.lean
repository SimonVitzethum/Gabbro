module

public import Grammatik.Parser.Async.Elaboration
public import Grammatik.Nebenlaeufigkeit.Async.Layout
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Elaboration

namespace Gabbro.Stage0.Frontend.Async
open Gabbro.Grammatik Gabbro.Grammatik.Async
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Async.Segment

/-- The declaration used to generate a layout comes from this position in the
    canonical outer parse. The complete ordinary signature stays attached. -/
public structure SourceFunction (text : String) (position : Nat)
    (analysis : AsyncSource.Analysis) where
  tokens : List Token
  items : List AsyncSource.Item
  declaration : AsyncSource.Function
  lexed : lex text = .ok tokens
  parsed : AsyncSource.parse tokens = .ok items
  selected : items[position]? = some (.asynchronous declaration)
  elaborated : AsyncSource.Elaborated analysis declaration

@[expose] public def sourceFunction (text : String) (position : Nat)
    (analysis : AsyncSource.Analysis) : Except String (SourceFunction text position analysis) :=
  match lexed : lex text with
  | .error _ => .error "async: lex"
  | .ok tokens =>
    match parsed : AsyncSource.parse tokens with
    | .error error => .error error
    | .ok items =>
      match selected : items[position]? with
      | some (.asynchronous declaration) => do
        let result ← AsyncSource.elaborate analysis declaration
        pure ⟨tokens, items, declaration, lexed, parsed, selected, result⟩
      | _ => .error "async: expected a top-level async declaration"

/-- These are exactly the source types used to lay out one function's frame
    and completed result. Child signatures have their own layout derivations. -/
@[expose] public def layoutTypes (function : AsyncFn) : List STyp :=
  function.resultType :: (function.params ++ function.fields).map Prod.snd

/-- The ordinary fields of a generated layout are resolved by the same
    function and scope as record fields in the ordinary frontend. -/
public structure LayoutResolution (function : AsyncFn) (scope : UTypeScope)
    (aliases : List (String × (Int × Int))) (tables : List UTab) (owner spaces : List String) where
  types : TypeResolution
  resolved : ∀ source ∈ layoutTypes function,
    uRecordFeldTyp scope aliases tables owner spaces source = .ok (types.ordinary source)

@[expose] public def resolveLayout (function : AsyncFn) (scope : UTypeScope)
    (aliases : List (String × (Int × Int))) (tables : List UTab) (owner spaces : List String)
    (recordName : List Nat → Nat) (namesUnique : ∀ a b, recordName a = recordName b → a = b)
    (childState childResult : String → Ty) :
    Except String (LayoutResolution function scope aliases tables owner spaces) :=
  let resolve := uRecordFeldTyp scope aliases tables owner spaces
  let ordinary := fun source => (resolve source).toOption.getD Ty.bool
  if checked : (layoutTypes function).all (fun source => (resolve source).isOk) then
    .ok ⟨⟨recordName, namesUnique, ordinary, childState, childResult⟩, by
      intro source used
      have found := List.all_eq_true.mp checked source used
      cases outcome : resolve source with
      | error error => simp only [outcome, Except.isOk, Except.toBool, Bool.false_eq_true] at found
      | ok type =>
        change resolve source = .ok (ordinary source)
        simp only [ordinary, outcome, Except.toOption, Option.getD_some]⟩
  else .error "async: unresolved frame or result type"

/-- The layout type of each saved slot has a canonical source typing derivation. -/
public theorem LayoutResolution.frameField {function : AsyncFn} {scope : UTypeScope}
    {aliases : List (String × (Int × Int))} {tables : List UTab} {owner spaces : List String}
    (resolution : LayoutResolution function scope aliases tables owner spaces) (name : String) (type : STyp)
    (used : (name, type) ∈ function.params ++ function.fields) :
    uRecordFeldTyp scope aliases tables owner spaces type = .ok (resolution.types.ordinary type) :=
  resolution.resolved type (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨(name, type), used, rfl⟩))

/-- Only referenced names from the function's declared frame participate
    in the expression scope. Other names use the ordinary unit scope. -/
@[expose] public def expressionBindings (function : AsyncFn) (source : SExpr) :
    List (String × STyp) :=
  (function.params ++ function.fields).filter (fun entry => (expressionNames source).contains entry.1)

@[expose] public def expressionParameters (ctx : UCtx) (function : AsyncFn) (source : SExpr) :
    Except String (List (String × Ty × UParamArt)) :=
  (expressionBindings function source).mapM
    (uParam ctx.alias ctx.tabs ctx.sums ctx.whys ctx.zeiger ctx.zeigerBasis ctx.spaces ctx.namedTypes ctx.eigner)

@[expose] public def FrameLocals (parameters : List (String × Ty × UParamArt)) : List (String × Ty) :=
  parameters.map fun parameter => (parameter.1, parameter.2.1)

@[expose] public def expressionContext (ctx : UCtx) (function : AsyncFn) (source : SExpr)
    (parameters : List (String × Ty × UParamArt)) : UCtx :=
  { ctx with names := parameters.map Prod.fst
             kinds := parameters.map (·.2.2)
             types := parameters.map (·.2.1)
             bits := (expressionBindings function source).map (fun binding => uBindingBreite ctx binding.2)
             fname := function.name
             muts := []
             unknownRanges := []
             lookupMemo := ULookupMemo.empty }

@[expose] public def expressionFunction (fn : UFn)
    (parameters : List (String × Ty × UParamArt)) : UFn :=
  { fn with params := FrameLocals parameters, kinds := parameters.map (·.2.2) }

/-- A resolved segment expression records the actual two ordinary
    elaboration steps on its original syntax and its exact frame locals. -/
public structure CanonicalExpression (u : UProg) (Λ : List (Res (declOf u))) (ctx : UCtx) (fn : UFn)
    (function : AsyncFn) (source : SExpr) where
  parameters : List (String × Ty × UParamArt)
  side : USide
  value : LowWert u ((FrameLocals parameters).map Prod.snd) Λ
  resolved : expressionParameters ctx function source = .ok parameters
  read : uWertBody (expressionContext ctx function source parameters) source = .ok side
  lowered : lowWertE u ((FrameLocals parameters).map Prod.snd) Λ
    (expressionFunction fn parameters) none side = .ok value

@[expose] public def resolveExpression (u : UProg) (Λ : List (Res (declOf u))) (ctx : UCtx) (fn : UFn)
    (function : AsyncFn) (source : SExpr) : Except String (CanonicalExpression u Λ ctx fn function source) :=
  match resolved : expressionParameters ctx function source with
  | .error failure => .error failure
  | .ok parameters =>
    match read : uWertBody (expressionContext ctx function source parameters) source with
    | .error failure => .error failure
    | .ok side =>
      match lowered : lowWertE u ((FrameLocals parameters).map Prod.snd) Λ
          (expressionFunction fn parameters) none side with
      | .error failure => .error failure
      | .ok value => .ok ⟨parameters, side, value, resolved, read, lowered⟩

@[expose] public def CanonicalExpression.bound {u : UProg} {Λ : List (Res (declOf u))}
    {ctx : UCtx} {fn : UFn} {function : AsyncFn} {source : SExpr}
    (resolved : CanonicalExpression u Λ ctx fn function source) : BoundExpression (declOf u) Λ :=
  BoundExpression.ofExpr (FrameLocals resolved.parameters) resolved.value.term

/-- Literal return expressions need no incoming frame slot. This
    inhabits the ordinary source-to-segment elaboration premises. -/
public theorem resolveExpression_literal_erfuellbar (u : UProg) (Λ : List (Res (declOf u)))
    (ctx : UCtx) (fn : UFn) (function : AsyncFn) (value : Int) :
    ∃ resolved : CanonicalExpression u Λ ctx fn function (.lit value),
      resolveExpression u Λ ctx fn function (.lit value) = .ok resolved ∧
      resolved.bound.locals = [] ∧ resolved.bound.result = .int value value := by
  have noBindings : expressionBindings function (.lit value) = [] := by
    simp only [expressionBindings, expressionNames, List.contains_nil, List.filter_false]
  simp only [resolveExpression, expressionParameters, noBindings, List.mapM_nil, pure, Except.pure]
  simp only [uWertBody, uRechne, uWertBlatt, lowWertE, LowSide.wert, FrameLocals, List.map_nil,
    CanonicalExpression.bound, BoundExpression.ofExpr]
  exact ⟨_, rfl, rfl, rfl⟩

end Gabbro.Stage0.Frontend.Async
