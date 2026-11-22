module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Resume
public import Grammatik.Nebenlaeufigkeit.Async.Representation.Restore
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {f : AsyncFn}
  {V : Vertrag D} {l : Bool} {Λ : List (Res D)} {Γ : Ctx}

/-- The dispatcher adds its destination and current frame to the exact
    context from ordinary elaboration. No new source variables are bound. -/
@[expose] public def bindingExpression (types : TypeResolution)
    (resolved : BoundExpression D Λ) (sourceType : Parser.STyp)
    (same : resolved.result = types.ordinary sourceType) :
    Expr D (resolved.locals.map Prod.snd ++ Γ) Λ (types.ordinary sourceType) :=
  same ▸ resolved.expression.ren (keepLocal Γ)

/-- The binding update uses the actual ordinary elaboration term, in
    the context restored from the semantic frame. -/
@[expose] public def resolvedBindingBlock (types : TypeResolution) (f : AsyncFn)
    (tag : Nat) (within : tag + 1 ≤ f.body.length) (destination : String) (sourceType : Parser.STyp)
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (resolved : BoundExpression D Λ) (same : resolved.result = types.ordinary sourceType)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f)) :
    Block D V l (resolved.locals.map Prod.snd ++ Γ) Λ Λ :=
  let scope := resolved.locals.map Prod.snd
  lowerRunningBinding types f tag within destination sourceType binding
    (prependLocal saved scope) (prependLocal state scope)
    (bindingExpression types resolved sourceType same)

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
    (outer : Env D Γ) (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (represented : FrameRep D types f (.running tag) frame (outer.get saved))
    (marks : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.running tag))
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :
    let result := evaluateBound elaboration source frame world
    let resumed := State.running (Child := Child D types) (tag + 1) (save frame destination result.1)
    ∃ value, execBlock oracle passes calls
        (resolvedBindingBlock (V := V) (l := l) types f tag within destination sourceType binding resolved same saved state)
          world (appendLocals locals outer) = .ok result.2.1 (appendLocals locals (outer.set state value)) ∧
      Inv f types inventory resumed value ∧ encode D types f resumed = some value := by
  intro result resumed
  let extended : Env D (resolved.locals.map Prod.snd ++ Γ) := appendLocals locals outer
  let rename : ∀ {τ : Ty}, Var (resolved.locals.map Prod.snd) τ →
      Var (resolved.locals.map Prod.snd ++ Γ) τ := keepLocal Γ
  let lifted := bindingExpression (Γ := Γ) types resolved sourceType same
  let ordinary := evaluateExpression resolved.expression world locals
  have preserved := resolved.expression.ren_sound rename
  have reads : (resolved.expression.ren rename).orte = resolved.expression.orte := preserved.1
  have measured : evaluateExpression (resolved.expression.ren rename) world extended = ordinary := by
    simp only [evaluateExpression, ordinary, reads, preserved.2.1]
    rw [preserved.2.2 _ _ locals extended (get_keepLocal outer locals)]
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
  let savedVar := prependLocal saved (resolved.locals.map Prod.snd)
  let stateVar := prependLocal state (resolved.locals.map Prod.snd)
  have inFrame : FrameRep D types f (.running tag) frame (extended.get savedVar) := by
    change FrameRep D types f (.running tag) frame
      ((appendLocals locals outer).get (prependLocal saved (resolved.locals.map Prod.snd)))
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
    have updated : extended.set stateVar value = appendLocals locals (outer.set state value) :=
      set_prependLocal state outer value locals
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
    (plan : RestorePlan types f resolved.locals)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f)) :
    Block D V l Γ Λ Λ :=
  restoreFrameBlock plan saved (resolvedBindingBlock types f tag within destination sourceType binding resolved same saved state)

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
    (outer : Env D Γ) (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (represented : FrameRep D types f (.running tag) frame (outer.get saved))
    (marks : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.running tag))
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :
    let result := evaluateBound elaboration source frame world
    let resumed := State.running (Child := Child D types) (tag + 1) (save frame destination result.1)
    ∃ value, execBlock oracle passes calls
        (restoredBindingBlock (V := V) (l := l) types f tag within destination sourceType binding resolved same plan saved state)
          world outer = .ok result.2.1 (outer.set state value) ∧
      Inv f types inventory resumed value ∧ encode D types f resumed = some value := by
  intro result resumed
  obtain ⟨locals, restored⟩ := plan.locals_defined (.running tag) frame (outer.get saved) represented live
  obtain ⟨value, evaluated, invariant, encoded⟩ := resolvedBindingBlock_rep (l := l) elaboration inventory tag within
    destination source cost rest command resolved known sourceType binding same world frame locals restored
    outer saved state represented marks sameInventory oracle passes calls
  let block := resolvedBindingBlock (V := V) (l := l) types f tag within destination sourceType binding resolved same saved state
  have installed := restoreFrameBlock_rep plan saved oracle passes calls world outer frame (.running tag)
    represented block locals live restored
  change execBlock oracle passes calls
    (restoredBindingBlock (V := V) (l := l) types f tag within destination sourceType binding resolved same plan saved state)
      world outer =
    removeLocals (resolved.locals.map Prod.snd) (execBlock oracle passes calls block world (appendLocals locals outer))
    at installed
  rw [show execBlock oracle passes calls block world (appendLocals locals outer) =
    .ok result.2.1 (appendLocals locals (outer.set state value)) from evaluated, removeLocals_ok] at installed
  exact ⟨value, installed, invariant, encoded⟩

/-- The selected ordinary binding is pinned to the actual command, its
    elaborated expression and the live indices of the generated frame. -/
public structure CheckedBinding (elaboration : Elaboration D V Λ types f) (tag : Nat) where
  destination : String
  source : Parser.SExpr
  cost : Nat
  rest : List Command
  command : f.body.drop tag = Command.bind destination source cost :: rest
  within : tag + 1 ≤ f.body.length
  resolved : BoundExpression D Λ
  known : elaboration.expression source = some resolved
  sourceType : Parser.STyp
  binding : (f.params ++ f.fields).lookup destination = some sourceType
  sameType : resolved.result = types.ordinary sourceType
  restore : RestorePlan types f resolved.locals
  live : ∀ entry ∈ resolved.locals, entry.1 ∈ liveAt f (.running tag)

@[expose] public def checkBindingAt (elaboration : Elaboration D V Λ types f) (tag : Nat) :
    Except String (CheckedBinding elaboration tag) := do
  match atTag : f.body.drop tag with
  | .bind destination source cost :: rest =>
    match found : elaboration.expression source with
    | none => throw "async: unresolved binding expression"
    | some expression =>
      match binding : (f.params ++ f.fields).lookup destination with
      | none => throw "async: missing binding declaration"
      | some sourceType =>
        if sameType : expression.result = types.ordinary sourceType then
          if localsLive : expression.locals.all (fun entry => decide (entry.1 ∈ liveAt f (.running tag))) = true then
            let plan ← restorePlanFor types f expression.locals
            have within : tag + 1 ≤ f.body.length := by
              have length := congrArg List.length atTag
              simp only [List.length_drop, List.length_cons] at length
              omega
            return ⟨destination, source, cost, rest, atTag, within, expression, found, sourceType, binding, sameType,
              plan, fun entry member => of_decide_eq_true (List.all_eq_true.mp localsLive entry member)⟩
          else throw "async: binding expression uses an unavailable local"
        else throw "async: binding expression result disagrees with its declaration"
  | _ => throw "async: position is not an ordinary binding"

@[expose] public def CheckedBinding.block {elaboration : Elaboration D V Λ types f} {tag : Nat}
    (checked : CheckedBinding elaboration tag) (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f)) :
    Block D V l Γ Λ Λ :=
  restoredBindingBlock types f tag checked.within checked.destination checked.sourceType checked.binding
    checked.resolved checked.sameType checked.restore saved state

/-- The compiler's checked binding arm executes from canonical storage
    using the exact modeled expression result and source world. -/
public theorem CheckedBinding.block_rep {elaboration : Elaboration D V Λ types f} {tag : Nat}
    (checked : CheckedBinding elaboration tag) (inventory : Inventory D) (frame : Frame (Value D))
    (before : World D) (outer : Env D Γ) (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (represented : FrameRep D types f (.running tag) frame (outer.get saved))
    (marks : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (unchanged : inventory.owned (.running (tag + 1)) = inventory.owned (.running tag))
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) :
    let result := evaluateBound elaboration checked.source frame before
    let resumed := State.running (Child := Child D types) (tag + 1) (save frame checked.destination result.1)
    ∃ value, execBlock oracle passes calls (checked.block (l := l) saved state) before outer =
        .ok result.2.1 (outer.set state value) ∧
      Inv f types inventory resumed value ∧ encode D types f resumed = some value :=
  restoredBindingBlock_rep (l := l) elaboration inventory tag checked.within checked.destination checked.source
    checked.cost checked.rest checked.command checked.resolved checked.known checked.sourceType checked.binding
    checked.sameType checked.restore checked.live before frame outer saved state represented marks unchanged oracle passes calls

end Gabbro.Grammatik.Async.Representation
