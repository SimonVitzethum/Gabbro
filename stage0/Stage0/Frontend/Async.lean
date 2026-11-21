module

public import Grammatik.Parser.Async.Elaboration
public import Grammatik.Nebenlaeufigkeit.Async.Layout
public import Grammatik.Parser.Elab.Uebersetze.Records.Records

namespace Gabbro.Stage0.Frontend.Async
open Gabbro.Grammatik Gabbro.Grammatik.Async
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

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

end Gabbro.Stage0.Frontend.Async
