module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Resume
import Grammatik.Nebenlaeufigkeit.Async.Segment.Renaming

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {f : AsyncFn}
  {V : Vertrag D} {l : Bool} {Λ : List (Res D)}

/-- The dispatcher adds its destination and current frame to the exact
    context from ordinary elaboration. No new source variables are bound. -/
@[expose] public def bindingExpression (types : TypeResolution) (f : AsyncFn)
    (resolved : BoundExpression D Λ) (sourceType : Parser.STyp)
    (same : resolved.result = types.ordinary sourceType) :
    Expr D (stateType types f :: frameType types f :: resolved.locals.map Prod.snd) Λ (types.ordinary sourceType) :=
  same ▸ resolved.expression.ren (fun x => .there (.there x))

/-- The binding update uses the actual ordinary elaboration term, in
    the context restored from the semantic frame. -/
@[expose] public def resolvedBindingBlock (types : TypeResolution) (f : AsyncFn)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (resolved : BoundExpression D Λ) (same : resolved.result = types.ordinary sourceType) :
    Block D V l (stateType types f :: frameType types f :: resolved.locals.map Prod.snd) Λ Λ :=
  lowerRunningBinding types f tag within destination sourceType binding (.there .here) .here
    (bindingExpression types f resolved sourceType same)

private theorem evaluateBinding_cast {Γ : Ctx} {first second : Ty} (same : first = second)
    (expression : Expr D Γ Λ first) (world : World D) (env : Env D Γ) :
    let source := evaluateExpression expression world env
    let target := evaluateExpression (same ▸ expression : Expr D Γ Λ second) world env
    Value.typed second target.1 = Value.typed first source.1 ∧ target.2 = source.2 := by
  cases same
  exact ⟨rfl, rfl⟩

/-- Running the resolved binding agrees with the semantic command on
    the exact source value, read trace and canonical successor record. -/
public theorem resolvedBindingBlock_rep (elaboration : Elaboration D V Λ types f)
    (inventory : Inventory D) (tag : Nat) (within : tag + 1 ≤ f.body.length)
    (destination : String) (source : Parser.SExpr) (cost : Nat) (rest : List Command)
    (command : f.body.drop tag = Command.bind destination source cost :: rest)
    (resolved : BoundExpression D Λ) (known : elaboration.expression source = some resolved)
    (sourceType : Parser.STyp) (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (same : resolved.result = types.ordinary sourceType)
    (world : World D) (frame : Frame (Value D))
    (locals : Env D (resolved.locals.map Prod.snd)) (restored : localsEnv D resolved.locals frame = some locals)
    (saved : Wert D (frameType types f)) (previous : Wert D (stateType types f))
    (represented : FrameRep D types f (.running tag) frame saved)
    (marks : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.running tag))
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :
    let result := evaluateBound elaboration source frame world
    let resumed := State.running (Child := Child D types) (tag + 1) (save frame destination result.1)
    ∃ value, execBlock oracle passes calls
        (resolvedBindingBlock (V := V) (l := l) types f tag within destination sourceType binding resolved same)
          world (.cons previous (.cons saved locals)) = .ok result.2.1 (.cons value (.cons saved locals)) ∧
      Inv f types inventory resumed value ∧ encode D types f resumed = some value := by
  intro result resumed
  let extended : Env D (stateType types f :: frameType types f :: resolved.locals.map Prod.snd) :=
    .cons previous (.cons saved locals)
  let rename : ∀ {τ : Ty}, Var (resolved.locals.map Prod.snd) τ →
      Var (stateType types f :: frameType types f :: resolved.locals.map Prod.snd) τ :=
    fun x => .there (.there x)
  let lifted := bindingExpression types f resolved sourceType same
  let ordinary := evaluateExpression resolved.expression world locals
  have preserved := resolved.expression.ren_sound rename
  have reads : (resolved.expression.ren rename).orte = resolved.expression.orte := preserved.1
  have measured : evaluateExpression (resolved.expression.ren rename) world extended = ordinary := by
    simp only [evaluateExpression, ordinary, reads, preserved.2.1]
    rw [preserved.2.2 _ _ locals extended (fun _ => rfl)]
  have converted := evaluateBinding_cast same (resolved.expression.ren rename) world extended
  change Value.typed (types.ordinary sourceType) (evaluateExpression lifted world extended).1 =
      Value.typed resolved.result (evaluateExpression (resolved.expression.ren rename) world extended).1 ∧
    (evaluateExpression lifted world extended).2 = (evaluateExpression (resolved.expression.ren rename) world extended).2
    at converted
  rw [measured] at converted
  have sourceResult : result = (Value.typed resolved.result ordinary.1, ordinary.2) :=
    evaluateBound_resolved elaboration source resolved known frame locals restored world
  have actual : (Value.typed (types.ordinary sourceType) (evaluateExpression lifted world extended).1,
      (evaluateExpression lifted world extended).2) = result := by
    rw [sourceResult, converted.1, converted.2]
  obtain ⟨value, executed, invariant, encoded⟩ := lowerRunningBinding_rep (V := V) (l := l) inventory tag within
    destination source cost rest command sourceType binding (.there .here) .here lifted oracle passes calls
    world extended frame represented marks sameInventory
  have exactValue := congrArg Prod.fst actual
  have exactWorld := congrArg (fun answer : Value D × World D × Nat => answer.2.1) actual
  simp only [Prod.fst, Prod.snd] at exactValue exactWorld
  refine ⟨value, ?_, ?_, ?_⟩
  · rw [exactWorld] at executed
    exact executed
  · rw [exactValue] at invariant
    exact invariant
  · rw [exactValue] at encoded
    exact encoded

end Gabbro.Grammatik.Async.Representation
