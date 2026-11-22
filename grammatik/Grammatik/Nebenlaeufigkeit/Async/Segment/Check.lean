module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Elaboration
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {types : TypeResolution} {f : AsyncFn}

/-- Resolve exactly the supplied argument expressions in order. The
    dependent result remembers the origin of every typed expression. -/
@[expose] public def resolveExpressions (resolve : Parser.SExpr → Option (BoundExpression D Λ)) :
    (sources : List Parser.SExpr) →
    Option {expressions : List (BoundExpression D Λ) // ExpressionsResolved resolve sources expressions}
  | [] => some ⟨[], .nil⟩
  | source :: rest =>
    match found : resolve source with
    | none => none
    | some expression => (resolveExpressions resolve rest).map (fun tail =>
      ⟨expression :: tail.val, .cons found tail.property⟩)

@[expose] public def bindingType (resolve : Parser.SExpr → Option (BoundExpression D Λ))
    (types : TypeResolution) (f : AsyncFn) (name : String) (source : Parser.SExpr) : Bool :=
  match resolve source, (f.params ++ f.fields).lookup name with
  | some expression, some sourceType => decide (expression.result = types.ordinary sourceType)
  | _, _ => false

public theorem bindingType_sound (resolve : Parser.SExpr → Option (BoundExpression D Λ))
    (types : TypeResolution) (f : AsyncFn) (name : String) (source : Parser.SExpr)
    (accepted : bindingType resolve types f name source = true) :
    ∃ expression sourceType, resolve source = some expression ∧
      (f.params ++ f.fields).lookup name = some sourceType ∧
      expression.result = types.ordinary sourceType := by
  cases resolved : resolve source with
  | none => simp only [bindingType, resolved, Bool.false_eq_true] at accepted
  | some expression =>
    cases declared : (f.params ++ f.fields).lookup name with
    | none => simp only [bindingType, resolved, declared, Bool.false_eq_true] at accepted
    | some sourceType =>
      simp only [bindingType, resolved, declared, decide_eq_true_eq] at accepted
      exact ⟨expression, sourceType, rfl, rfl, accepted⟩

@[expose] public def callsType (resolve : Parser.SExpr → Option (BoundExpression D Λ))
    (callee : (name : String) → Option (AwaitedCall D V Λ types name)) : FutureExpr → Bool
  | .call name args =>
    match callee name, resolveExpressions resolve args with
    | some declaration, some expressions => decide (expressions.val.map BoundExpression.result = declaration.parameters)
    | _, _ => false
  | .join .. => true

public theorem callsType_sound (resolve : Parser.SExpr → Option (BoundExpression D Λ))
    (callee : (name : String) → Option (AwaitedCall D V Λ types name))
    (name : String) (args : List Parser.SExpr) (accepted : callsType resolve callee (.call name args) = true) :
    ∃ declaration expressions, callee name = some declaration ∧
      ExpressionsResolved resolve args expressions ∧
      expressions.map BoundExpression.result = declaration.parameters := by
  cases selected : callee name with
  | none => simp only [callsType, selected, Bool.false_eq_true] at accepted
  | some declaration =>
    cases resolved : resolveExpressions resolve args with
    | none => simp only [callsType, selected, resolved, Bool.false_eq_true] at accepted
    | some expressions =>
      simp only [callsType, selected, resolved, decide_eq_true_eq] at accepted
      exact ⟨declaration, expressions.val, rfl, expressions.property, accepted⟩

@[expose] public def awaitResultType (types : TypeResolution) (f : AsyncFn) (tag : Nat) : Bool :=
  match f.body.drop tag with
  | .await name future _ :: _ =>
    match (f.params ++ f.fields).lookup name with
    | some target => decide (taskResultType types [tag] future = types.ordinary target)
    | none => false
  | _ => true

public theorem awaitResultType_sound (types : TypeResolution) (f : AsyncFn)
    (tag : Nat) (name : String) (future : FutureExpr) (boundary : Boundary) (rest : List Command)
    (atTag : f.body.drop tag = .await name future boundary :: rest)
    (accepted : awaitResultType types f tag = true) :
    ∃ target, (f.params ++ f.fields).lookup name = some target ∧
      taskResultType types [tag] future = types.ordinary target := by
  cases declared : (f.params ++ f.fields).lookup name with
  | none => simp only [awaitResultType, atTag, declared, Bool.false_eq_true] at accepted
  | some target =>
    simp only [awaitResultType, atTag, declared, decide_eq_true_eq] at accepted
    exact ⟨target, rfl, accepted⟩

/-- Decide all coverage premises over the finite body and its nested
    calls. The production elaborator can pass the ordinary expression
    reader and its resolved child table directly to this checker. -/
@[expose] public def checkElaboration (types : TypeResolution) (f : AsyncFn)
    (resolve : Parser.SExpr → Option (BoundExpression D Λ))
    (callee : (name : String) → Option (AwaitedCall D V Λ types name)) :
    Except String (Elaboration D V Λ types f) :=
  match found : resolve f.result with
  | none => .error "async: no resolved return expression"
  | some result =>
    if returned : result.result = types.ordinary f.resultType then
      if bindings : f.body.all (fun command => match command with
        | .bind name source _ => bindingType resolve types f name source
        | .await .. => true) = true then
        if calls : (f.body.flatMap fun command => match command with
          | .bind .. => []
          | .await _ future _ => callsIn future).all (callsType resolve callee) = true then
          if waits : (List.finRange f.body.length).all (fun tag => awaitResultType types f tag.val) = true then
            .ok {
              expression := resolve
              callee := callee
              bound := fun name source count used =>
                bindingType_sound resolve types f name source (List.all_eq_true.mp bindings
                  (.bind name source count) used)
              returned := ⟨result, found, returned⟩
              arguments := fun name args used =>
                callsType_sound resolve callee name args (List.all_eq_true.mp calls (.call name args) used)
              awaited := fun tag name future boundary rest atTag => by
                have size := congrArg List.length atTag
                simp only [List.length_drop, List.length_cons] at size
                let index : Fin f.body.length := ⟨tag, by omega⟩
                have accepted := List.all_eq_true.mp waits index (List.mem_finRange index)
                exact awaitResultType_sound types f tag name future boundary rest atTag accepted }
          else .error "async: an awaited result does not fit its declared slot"
        else .error "async: a child call does not match its resolved declaration"
      else .error "async: a binding does not fit its declared slot"
    else .error "async: the ordinary return expression has another type"

end Gabbro.Grammatik.Async.Segment
