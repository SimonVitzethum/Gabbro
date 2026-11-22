module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Resume
public import Grammatik.Nebenlaeufigkeit.Async.Representation.Restore

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {f : AsyncFn}
  {V : Vertrag D} {l : Bool} {Λ : List (Res D)}

/-- The dispatcher adds its destination and current frame to the exact
    context from ordinary elaboration. No new source variables are bound. -/
@[expose] public def bindingExpression (types : TypeResolution) (f : AsyncFn)
    (resolved : BoundExpression D Λ) (sourceType : Parser.STyp)
    (same : resolved.result = types.ordinary sourceType) :
    Expr D (resolved.locals.map Prod.snd ++ [stateType types f, frameType types f]) Λ (types.ordinary sourceType) :=
  same ▸ resolved.expression.ren (keepLocal [stateType types f, frameType types f])

/-- The binding update uses the actual ordinary elaboration term, in
    the context restored from the semantic frame. -/
@[expose] public def resolvedBindingBlock (types : TypeResolution) (f : AsyncFn)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (resolved : BoundExpression D Λ) (same : resolved.result = types.ordinary sourceType) :
    Block D V l (resolved.locals.map Prod.snd ++ [stateType types f, frameType types f]) Λ Λ :=
  let scope := resolved.locals.map Prod.snd
  lowerRunningBinding types f tag within destination sourceType binding
    (prependLocal (.there .here) scope) (prependLocal .here scope)
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
          world (appendLocals locals (.cons previous (.cons saved .nil))) =
          .ok result.2.1 (appendLocals locals (.cons value (.cons saved .nil))) ∧
      Inv f types inventory resumed value ∧ encode D types f resumed = some value := by
  intro result resumed
  let outside : Env D [stateType types f, frameType types f] := .cons previous (.cons saved .nil)
  let extended : Env D (resolved.locals.map Prod.snd ++ [stateType types f, frameType types f]) :=
    appendLocals locals outside
  let rename : ∀ {τ : Ty}, Var (resolved.locals.map Prod.snd) τ →
      Var (resolved.locals.map Prod.snd ++ [stateType types f, frameType types f]) τ :=
    keepLocal [stateType types f, frameType types f]
  let lifted := bindingExpression types f resolved sourceType same
  let ordinary := evaluateExpression resolved.expression world locals
  have preserved := resolved.expression.ren_sound rename
  have reads : (resolved.expression.ren rename).orte = resolved.expression.orte := preserved.1
  have measured : evaluateExpression (resolved.expression.ren rename) world extended = ordinary := by
    simp only [evaluateExpression, ordinary, reads, preserved.2.1]
    rw [preserved.2.2 _ _ locals extended (get_keepLocal outside locals)]
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
  let savedVar := prependLocal (Γ := [stateType types f, frameType types f]) (.there .here)
    (resolved.locals.map Prod.snd)
  let stateVar := prependLocal (Γ := [stateType types f, frameType types f]) .here (resolved.locals.map Prod.snd)
  have inFrame : FrameRep D types f (.running tag) frame (extended.get savedVar) := by
    change FrameRep D types f (.running tag) frame
      ((appendLocals locals outside).get (prependLocal (.there .here) (resolved.locals.map Prod.snd)))
    rw [get_prependLocal]
    exact represented
  obtain ⟨value, executed, invariant, encoded⟩ := lowerRunningBinding_rep (V := V) (l := l) inventory tag within
    destination source cost rest command sourceType binding savedVar stateVar lifted oracle passes calls
    world extended frame inFrame marks sameInventory
  have exactValue := congrArg Prod.fst actual
  have exactWorld := congrArg (fun answer : Value D × World D × Nat => answer.2.1) actual
  simp only [Prod.fst, Prod.snd] at exactValue exactWorld
  refine ⟨value, ?_, ?_, ?_⟩
  · rw [exactWorld] at executed
    have updated : extended.set stateVar value = appendLocals locals (.cons value (.cons saved .nil)) :=
      set_prependLocal .here outside value locals
    rw [updated] at executed
    exact executed
  · rw [exactValue] at invariant
    exact invariant
  · rw [exactValue] at encoded
    exact encoded

/-- A running dispatcher arm restores its lexical context from the
    saved frame, evaluates the resolved term and installs the next tag. -/
@[expose] public def restoredBindingBlock (types : TypeResolution) (f : AsyncFn)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (resolved : BoundExpression D Λ) (same : resolved.result = types.ordinary sourceType)
    (plan : RestorePlan types f resolved.locals) :
    Block D V l [stateType types f, frameType types f] Λ Λ :=
  restoreFrameBlock plan (.there .here)
    (resolvedBindingBlock types f tag within destination sourceType binding resolved same)

/-- The whole generated binding arm reaches the modeled continuation
    from its saved frame. Restored lexical locals are scoped to the arm. -/
public theorem restoredBindingBlock_rep (elaboration : Elaboration D V Λ types f)
    (inventory : Inventory D) (tag : Nat) (within : tag + 1 ≤ f.body.length)
    (destination : String) (source : Parser.SExpr) (cost : Nat) (rest : List Command)
    (command : f.body.drop tag = Command.bind destination source cost :: rest)
    (resolved : BoundExpression D Λ) (known : elaboration.expression source = some resolved)
    (sourceType : Parser.STyp) (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (same : resolved.result = types.ordinary sourceType)
    (plan : RestorePlan types f resolved.locals)
    (live : ∀ entry ∈ resolved.locals, entry.1 ∈ liveAt f (.running tag))
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
        (restoredBindingBlock (V := V) (l := l) types f tag within destination sourceType binding resolved same plan)
          world (.cons previous (.cons saved .nil)) = .ok result.2.1 (.cons value (.cons saved .nil)) ∧
      Inv f types inventory resumed value ∧ encode D types f resumed = some value := by
  intro result resumed
  obtain ⟨value, evaluated, invariant, encoded⟩ := resolvedBindingBlock_rep (l := l) elaboration inventory tag within
    destination source cost rest command resolved known sourceType binding same world frame locals restored
    saved previous represented marks sameInventory oracle passes calls
  let outer : Env D [stateType types f, frameType types f] := .cons previous (.cons saved .nil)
  let block := resolvedBindingBlock (V := V) (l := l) types f tag within destination sourceType binding resolved same
  have inFrame : FrameRep D types f (.running tag) frame (outer.get (.there .here)) := represented
  have installed := restoreFrameBlock_rep plan (.there .here) oracle passes calls world outer frame (.running tag)
    inFrame block locals live restored
  change execBlock oracle passes calls
    (restoredBindingBlock (V := V) (l := l) types f tag within destination sourceType binding resolved same plan) world outer =
    removeLocals (resolved.locals.map Prod.snd) (execBlock oracle passes calls block world (appendLocals locals outer))
    at installed
  rw [show execBlock oracle passes calls block world (appendLocals locals outer) =
    .ok result.2.1 (appendLocals locals (.cons value (.cons saved .nil))) from evaluated, removeLocals_ok] at installed
  exact ⟨value, installed, invariant, encoded⟩

end Gabbro.Grammatik.Async.Representation
