module

public import Grammatik.Parser.Async.Elaboration
public import Grammatik.Nebenlaeufigkeit.Async.Layout
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil3
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Elaboration
public import Grammatik.Nebenlaeufigkeit.Async.Creation
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Check
public import Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedPoll
public import Grammatik.Nebenlaeufigkeit.Async.PollFunction
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1
public import Mathlib.Data.Nat.Pairing

namespace Gabbro.Stage0.Frontend.Async
open Gabbro.Grammatik Gabbro.Grammatik.Async
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Async.Segment
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Async.Representation

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

/-- The first identity beyond all source record declarations. -/
@[expose] public def recordCeiling : List URecord → Nat
  | [] => 0
  | head :: rest => max (head.identity + 1) (recordCeiling rest)

public theorem record_lt_ceiling {records : List URecord} {record : URecord} (present : record ∈ records) :
    record.identity < recordCeiling records := by
  induction records with
  | nil => cases present
  | cons head rest ih =>
    rcases List.mem_cons.mp present with rfl | contained
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left ..)
    · exact Nat.lt_of_lt_of_le (ih contained) (Nat.le_max_right ..)

@[expose] public def recordPath : List Nat → Nat
  | [] => 0
  | head :: tail => Nat.pair head (recordPath tail) + 1

public theorem recordPath_injective : Function.Injective recordPath := by
  intro first
  induction first with
  | nil =>
    intro second same
    cases second with
    | nil => rfl
    | cons head tail => cases same
  | cons head tail ih =>
    intro second same
    cases second with
    | nil => cases same
    | cons other rest =>
      have paired := Nat.succ.inj same
      obtain ⟨rfl, equal⟩ := Nat.pair_eq_pair.mp paired
      exact congrArg (List.cons head) (ih equal)

@[expose] public def generatedRecordName (source : UTypeScope) (declaration : Nat)
    (path : List Nat) : Nat :=
  recordCeiling source.records + Nat.pair declaration (recordPath path)

public theorem generatedRecordName_exact {source : UTypeScope} {first second : Nat} {path other : List Nat}
    (same : generatedRecordName source first path = generatedRecordName source second other) :
    first = second ∧ path = other := by
  obtain ⟨declaration, place⟩ := Nat.pair_eq_pair.mp (Nat.add_left_cancel same)
  exact ⟨declaration, recordPath_injective place⟩

public theorem generatedRecordName_fresh {source : UTypeScope} {record : URecord}
    (present : record ∈ source.records) (declaration : Nat) (path : List Nat) :
    record.identity < generatedRecordName source declaration path :=
  (record_lt_ceiling present).trans_le (Nat.le_add_right _ _)

/-- Generated frame, state and join records occupy disjoint identities
    across all original declarations and their internal paths. -/
@[expose] public def resolveUnitLayout (function : AsyncFn) (identity : Nat) (scope : UTypeScope)
    (aliases : List (String × (Int × Int))) (tables : List UTab) (owner spaces : List String)
    (childState childResult : String → Ty) :
    Except String (LayoutResolution function scope aliases tables owner spaces) :=
  resolveLayout function scope aliases tables owner spaces (generatedRecordName scope identity)
    (fun _ _ same => (generatedRecordName_exact same).2) childState childResult

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

@[expose] public def lowerExpression (u : UProg) (Λ : List (Res (declOf u))) (fn : UFn)
    (parameters : List (String × Ty × UParamArt)) (expected : Option Ty) (side : USide) :
    Except String (LowWert u ((FrameLocals parameters).map Prod.snd) Λ) :=
  match expected with
  | none => lowWertE u _ Λ (expressionFunction fn parameters) none side
  | some type => (lowWertAtE u _ Λ (expressionFunction fn parameters) none type side).map (LowWert.mk type)

/-- A resolved segment expression records the actual two ordinary
    elaboration steps on its original syntax and its exact frame locals. -/
public structure CanonicalExpression (u : UProg) (Λ : List (Res (declOf u))) (ctx : UCtx) (fn : UFn)
    (function : AsyncFn) (source : SExpr) (expected : Option Ty := none) where
  parameters : List (String × Ty × UParamArt)
  side : USide
  value : LowWert u ((FrameLocals parameters).map Prod.snd) Λ
  resolved : expressionParameters ctx function source = .ok parameters
  read : uWertBody (expressionContext ctx function source parameters) source = .ok side
  lowered : lowerExpression u Λ fn parameters expected side = .ok value

@[expose] public def resolveExpression (u : UProg) (Λ : List (Res (declOf u))) (ctx : UCtx) (fn : UFn)
    (function : AsyncFn) (source : SExpr) (expected : Option Ty := none) :
    Except String (CanonicalExpression u Λ ctx fn function source expected) :=
  match resolved : expressionParameters ctx function source with
  | .error failure => .error failure
  | .ok parameters =>
    match read : uWertBody (expressionContext ctx function source parameters) source with
    | .error failure => .error failure
    | .ok side =>
      match lowered : lowerExpression u Λ fn parameters expected side with
      | .error failure => .error failure
      | .ok value => .ok ⟨parameters, side, value, resolved, read, lowered⟩

@[expose] public def CanonicalExpression.bound {u : UProg} {Λ : List (Res (declOf u))}
    {ctx : UCtx} {fn : UFn} {function : AsyncFn} {source : SExpr} {expected : Option Ty}
    (resolved : CanonicalExpression u Λ ctx fn function source expected) : BoundExpression (declOf u) Λ :=
  BoundExpression.ofExpr (FrameLocals resolved.parameters) resolved.value.term

/-- Literal return expressions need no incoming frame slot. This
    inhabits the ordinary source-to-segment elaboration premises. -/
public theorem resolveExpression_literal_erfuellbar (u : UProg) (Λ : List (Res (declOf u)))
    (ctx : UCtx) (fn : UFn) (function : AsyncFn) (value : Nat) :
    ∃ resolved : CanonicalExpression u Λ ctx fn function (.lit value),
      resolveExpression u Λ ctx fn function (.lit value) = .ok resolved ∧
      resolved.bound.locals = [] ∧ resolved.bound.result = .int value value := by
  have noBindings : expressionBindings function (.lit value) = [] := by
    simp only [expressionBindings, expressionNames, List.contains_nil, List.filter_eq_nil_iff,
      Bool.false_eq_true, not_false_eq_true, implies_true]
  have parameters : expressionParameters ctx function (.lit value) = .ok [] := by
    simp only [expressionParameters, noBindings, List.mapM_nil, pure, Except.pure]
  have read : uWertBody (expressionContext ctx function (.lit value) []) (.lit value) =
      .ok (.lit (Int.ofNat value)) := by
    simp only [uWertBody, uRechne, uWertBlatt]
  let term : LowWert u [] Λ := ⟨.int value value, .lit value⟩
  have lowered : lowerExpression u Λ fn [] none (.lit value) = .ok term := by
    rfl
  let resolved : CanonicalExpression u Λ ctx fn function (.lit value) :=
    ⟨[], .lit value, term, parameters, read, lowered⟩
  refine ⟨resolved, ?_, rfl, rfl⟩
  unfold resolveExpression
  split
  · rename_i error impossible
    rw [parameters] at impossible
    cases impossible
  · rename_i actual found
    have same := Except.ok.inj (found.symm.trans parameters)
    subst actual
    split
    · rename_i error impossible
      rw [read] at impossible
      cases impossible
    · rename_i actual found
      have same := Except.ok.inj (found.symm.trans read)
      subst actual
      split
      · rename_i error impossible
        change lowWertE u [] Λ (expressionFunction fn []) none (.lit (Int.ofNat value)) =
          .error error at impossible
        have mismatch := lowered.symm.trans impossible
        cases mismatch
      · rename_i actual found
        change lowWertE u [] Λ (expressionFunction fn []) none (.lit (Int.ofNat value)) =
          .ok actual at found
        have same := Except.ok.inj (found.symm.trans lowered)
        subst actual
        rfl

/-- The poll entry is private to the expansion and cannot collide with
    any source identifier. The same name is used by all child-call sites. -/
@[expose] public def pollName (child : String) : String :=
  "$async$poll$" ++ child

public structure ResolvedPoll (u : UProg) (V : Vertrag (declOf u)) (Λ : List (Res (declOf u)))
    (types : TypeResolution) (child : String) where
  callee : AwaitedCall (declOf u) V Λ types child
  found : fnNr u (pollName child) = .ok callee.poll

/-- Check the actual generated poll signature with the same finite call
    checker as ordinary G. Construction code has already been typed
    against the generated child's initial record. -/
@[expose] public def resolvePoll (u : UProg) (V : Vertrag (declOf u)) (Λ : List (Res (declOf u)))
    (types : TypeResolution) (child : String) (parameters : List Ty)
    (construct : Expr (declOf u) parameters Λ (types.childState child)) :
    Except String (ResolvedPoll u V Λ types child) :=
  match found : fnNr u (pollName child) with
  | .error failure => .error failure
  | .ok poll =>
    if args : (declOf u).params poll = [types.childState child] then
      if result : (declOf u).erg poll =
          some (.sum [some (types.childResult child), some (types.childState child)]) then
        if admitted : rufPasstB u V ((declOf u).signatur poll) Λ = true then
          if reasons : (declOf u).gruende poll = 0 then
            if inventory : nach (declOf u) poll Λ = Λ then
              .ok ⟨⟨parameters, construct, poll, args, result, rufPasstB_ok admitted, reasons, inventory⟩, found⟩
            else .error "async: poll changes the resource index"
          else .error "async: poll has an unchecked reason channel"
        else .error "async: poll violates the ordinary call contract"
      else .error "async: poll result differs from Ready/Pending"
    else .error "async: poll takes a different state record"

/-- Use the constructor of the resolved child declaration at each await
    site. The site's layout must select the same state and result types. -/
@[expose] public def resolveChild (u : UProg) (V : Vertrag (declOf u)) {Λ : List (Res (declOf u))}
    (types : TypeResolution) {childTypes : TypeResolution} {child : AsyncFn}
    {inventory : Inventory (declOf u)} (constructor : Constructor childTypes child inventory Λ) :
    Except String (ResolvedPoll u V Λ types child.name) :=
  if state : stateType childTypes child = types.childState child.name then
    if childTypes.ordinary child.resultType = types.childResult child.name then
      resolvePoll u V Λ types child.name (parameterTypes childTypes child.params) (state ▸ constructor.code)
    else .error "async: selected child result does not match its declared type"
  else .error "async: selected child layout does not match its constructor"

/-- Check every declaration in the original body using the ordinary
    expression reader and the actual named child-poll resolver.
    A generated occurrence sees only preceding bindings and is checked
    in the type of its declared destination. -/
@[expose] public def expressionAtSite (u : UProg) (Λ : List (Res (declOf u))) (ctx : UCtx) (fn : UFn)
    (function : AsyncFn) (types : TypeResolution)
    (arguments : String → Option (List Ty)) : SExpr → Option (BoundExpression (declOf u) Λ)
  | .built "#async-value" [.lit position, source] => do
    let sourceType ← if position = function.body.length then
      some function.resultType
    else do
      let some (.bind name _ _) := function.body[position]? | none
      function.fields.lookup name
    let visible := { function with fields := function.fields.take position }
    let typed ← (resolveExpression u Λ ctx fn visible source (some (types.ordinary sourceType))).toOption
    some typed.bound
  | .built "#async-argument" [.lit position, .lit index, .call callee [source]] => do
    let some (.await ..) := function.body[position]? | none
    let types ← arguments callee
    let expected ← types[index]?
    let visible := { function with fields := function.fields.take position }
    let typed ← (resolveExpression u Λ ctx fn visible source (some expected)).toOption
    some typed.bound
  | source => (resolveExpression u Λ ctx fn function source).toOption.map CanonicalExpression.bound

@[expose] public def checkFunctionElaboration (u : UProg) (V : Vertrag (declOf u))
    (Λ : List (Res (declOf u))) (ctx : UCtx) (fn : UFn) (function : AsyncFn) (types : TypeResolution)
    (children : (name : String) → Option (ResolvedPoll u V Λ types name)) :
    Except String (Elaboration (declOf u) V Λ types function) :=
  checkElaboration types function
    (expressionAtSite u Λ ctx fn function types (fun name => (children name).map (·.callee.parameters)))
    (fun name => (children name).map ResolvedPoll.callee)

/-- This connects the actual source declaration and its canonical typed
    scope to the exact generated dispatch table. -/
public structure ResolvedFunction (u : UProg) (V : Vertrag (declOf u)) (Λ : List (Res (declOf u)))
    (ctx : UCtx) (fn : UFn) (function : AsyncFn) (types : TypeResolution)
    (children : (name : String) → Option (ResolvedPoll u V Λ types name)) where
  elaboration : Elaboration (declOf u) V Λ types function
  elaborated : checkFunctionElaboration u V Λ ctx fn function types children = .ok elaboration
  phases : (index : Fin (phases function).length) → PhasePlan elaboration ((phases function).get index)
  checked : checkPhaseTable elaboration = .ok phases

@[expose] public def resolveFunction (u : UProg) (V : Vertrag (declOf u)) (Λ : List (Res (declOf u)))
    (ctx : UCtx) (fn : UFn) (function : AsyncFn) (types : TypeResolution)
    (children : (name : String) → Option (ResolvedPoll u V Λ types name)) :
    Except String (ResolvedFunction u V Λ ctx fn function types children) :=
  match elaborated : checkFunctionElaboration u V Λ ctx fn function types children with
  | .error failure => .error failure
  | .ok elaboration =>
    match checked : checkPhaseTable elaboration with
    | .error failure => .error failure
    | .ok phases => .ok ⟨elaboration, elaborated, phases, checked⟩

public structure NamedPoll (u : UProg) (ctx : UCtx) (function : AsyncFn) (types : TypeResolution)
    (children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)) where
  poll : (declOf u).Fn
  selected : fnNr u (pollName function.name) = .ok poll
  input : (declOf u).params poll = [stateType types function]
  result : (verOf u poll).erg = some (pollResultType types function)
  inventory : (resOf u poll).Perm (verOf u poll).ende
  expanded : ResolvedFunction u (verOf u poll) (resOf u poll) ctx (u.fns.get poll)
    function types (children poll)

/-- The body to install has the exact type of the actual selected
    declaration slot in the canonical program. -/
@[expose] public def NamedPoll.body {u : UProg} {ctx : UCtx} {function : AsyncFn} {types : TypeResolution}
    {children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)}
    (resolved : NamedPoll u ctx function types children) :
    Endblock (declOf u) (vertragVon (declOf u) resolved.poll) false
      ((declOf u).params resolved.poll) (Signatur.anfang (declOf u) ((declOf u).signatur resolved.poll)) :=
  resolved.input.symm ▸ pollFunction resolved.expanded.phases resolved.result resolved.inventory

/-- Resolve the private declaration, compare its ordinary call
    signature, and lower the canonically parsed body into that exact slot. -/
@[expose] public def lowerNamedPoll (u : UProg) (ctx : UCtx) (function : AsyncFn) (types : TypeResolution)
    (children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)) :
    Except String (NamedPoll u ctx function types children) :=
  match selected : fnNr u (pollName function.name) with
  | .error failure => .error failure
  | .ok poll =>
    if input : (declOf u).params poll = [stateType types function] then
      if result : (verOf u poll).erg = some (pollResultType types function) then
        if inventory : decide ((resOf u poll).Perm (verOf u poll).ende) = true then
          if (verOf u poll).gruende = 0 then
            (resolveFunction u (verOf u poll) (resOf u poll) ctx (u.fns.get poll) function types
              (children poll)).map fun expanded =>
                ⟨poll, selected, input, result, of_decide_eq_true inventory, expanded⟩
          else .error "async: generated poll signature has a reason channel"
        else .error "async: generated poll signature does not restore its resource index"
      else .error "async: generated poll signature has another result type"
    else .error "async: generated poll signature has another state parameter"

end Gabbro.Stage0.Frontend.Async
