module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedAwait
public import Grammatik.Nebenlaeufigkeit.Async.Representation.BindLowering
public import Grammatik.Nebenlaeufigkeit.Async.Representation.Completion
public import Grammatik.Parser.Elab.UebersetzeAllg3.Memo
import Grammatik.Parser.Elab.Uebersetze.Kontext.SyntaxEquality

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

deriving instance DecidableEq for FutureExpr

/-- The final running arm restores only the actual expression's live
    locals. Its type is exactly the function's declared result type. -/
public structure CheckedFinal (elaboration : Elaboration D V Λ types f) where
  resolved : BoundExpression D Λ
  known : elaboration.expression f.result = some resolved
  result : resolved.result = types.ordinary f.resultType
  restore : RestorePlan types f resolved.locals
  live : ∀ entry ∈ resolved.locals, entry.1 ∈ liveAt f (.running f.body.length)

@[expose] public def checkFinal (elaboration : Elaboration D V Λ types f) :
    Except String (CheckedFinal elaboration) := do
  match found : elaboration.expression f.result with
  | none => throw "async: unresolved result expression"
  | some resolved =>
    if result : resolved.result = types.ordinary f.resultType then
      if live : resolved.locals.all (fun entry => decide (entry.1 ∈ liveAt f (.running f.body.length))) = true then
        let restore ← restorePlanFor types f resolved.locals
        pure ⟨resolved, found, result, restore, fun entry used =>
          of_decide_eq_true (List.all_eq_true.mp live entry used)⟩
      else throw "async: result expression uses an unavailable local"
    else throw "async: result expression disagrees with the declared result type"

@[expose] public def CheckedFinal.inner {elaboration : Elaboration D V Λ types f}
    (checked : CheckedFinal elaboration) (state : Var Γ (stateType types f)) (finished : Var Γ .bool) :
    Block D V l (checked.resolved.locals.map Prod.snd ++ Γ) Λ Λ :=
  let scope := checked.resolved.locals.map Prod.snd
  .bind (bindingExpression types checked.resolved f.resultType checked.result)
    (.cons (.assignVar (.there (prependLocal state scope)) (completedExpr (.var .here)))
      (.cons (.assignVar (.there (prependLocal finished scope)) .tru) .nil))

@[expose] public def CheckedFinal.block {elaboration : Elaboration D V Λ types f}
    (checked : CheckedFinal elaboration) (saved : Var Γ (frameType types f))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) : Block D V l Γ Λ Λ :=
  restoreFrameBlock checked.restore saved (checked.inner state finished)

private theorem castExpression {input output : Ty} (same : input = output) (e : Expr D Γ Λ input)
    (entry world : World D) (env : Env D Γ) :
    ((same ▸ e : Expr D Γ Λ output).orte = e.orte) ∧
      eval entry (same ▸ e : Expr D Γ Λ output) world env = (same ▸ eval entry e world env) := by
  cases same
  exact ⟨rfl, rfl⟩

public theorem CheckedFinal.inner_exec {elaboration : Elaboration D V Λ types f}
    (checked : CheckedFinal elaboration) (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (outer : Env D Γ) (locals : Env D (checked.resolved.locals.map Prod.snd)) :
    let result := evaluateExpression checked.resolved.expression world locals
    let completed := completedValue D types f (checked.result ▸ result.1)
    execBlock oracle passes calls (checked.inner (l := l) state finished) world (appendLocals locals outer) =
      .ok result.2.1 (appendLocals locals ((outer.set state completed).set finished true)) := by
  intro result completed
  let scope := checked.resolved.locals.map Prod.snd
  let env := appendLocals locals outer
  let term := checked.resolved.expression
  let renamed := term.ren (keepLocal Γ)
  let expr := bindingExpression (Γ := Γ) types checked.resolved f.resultType checked.result
  have layout := term.ren_sound (keepLocal Γ)
  have reads : expr.orte = term.orte :=
    (castExpression checked.result renamed world world env).1.trans layout.1
  let read := world.lese Λ term.orte
  have value : eval read expr read env = (checked.result ▸ result.1) := by
    change eval read (checked.result ▸ renamed : Expr D (scope ++ Γ) Λ (types.ordinary f.resultType)) read env = _
    rw [(castExpression checked.result renamed read read env).2,
      layout.2.2 read read locals env (get_keepLocal outer locals)]
    rfl
  change Ausgang.ok (world.lese Λ expr.orte)
    ((env.set (prependLocal state scope) (completedValue D types f
      (eval (world.lese Λ expr.orte) expr (world.lese Λ expr.orte) env))).set
        (prependLocal finished scope) true) = _
  rw [reads, show world.lese Λ term.orte = read from rfl, value]
  change Ausgang.ok read (((appendLocals locals outer).set (prependLocal state scope) completed).set
    (prependLocal finished scope) true) = _
  have setState := set_prependLocal state outer completed locals
  have setFinished := set_prependLocal finished (outer.set state completed) true locals
  exact congrArg (Ausgang.ok read)
    ((congrArg (fun environment => environment.set (prependLocal finished scope) true) setState).trans setFinished)

/-- The actual final arm restores the source locals, observes its
    precise read trace and publishes the completed record and stop flag. -/
public theorem CheckedFinal.block_simulates {elaboration : Elaboration D V Λ types f}
    (checked : CheckedFinal elaboration) (inventory : Inventory D) (empty : inventory.owned Phase.completed = [])
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (outer : Env D Γ) (frame : Frame (Value D))
    (represented : FrameRep D types f (.running f.body.length) frame (outer.get saved)) :
    let result := evaluateBound elaboration f.result frame world
    let target := State.completed (Child := Child D types) result.1 ⟨[], []⟩
    ∃ record, execBlock oracle passes calls (checked.block (l := l) saved state finished) world outer =
        .ok result.2.1 ((outer.set state record).set finished true) ∧
      Inv f types inventory target record ∧ encode D types f target = some record := by
  intro result target
  obtain ⟨locals, restored⟩ := checked.restore.locals_defined (.running f.body.length) frame
    (outer.get saved) represented checked.live
  let evaluated := evaluateExpression checked.resolved.expression world locals
  have exactResult : result = (Value.typed checked.resolved.result evaluated.1, evaluated.2) :=
    evaluateBound_resolved elaboration f.result checked.resolved checked.known frame locals restored world
  let record := completedValue D types f (checked.result ▸ evaluated.1)
  have typedValue {source expected : Ty} (same : source = expected) (payload : Wert D source) :
      valueAt D expected (Value.typed source payload) = some (same ▸ payload) := by
    cases same
    exact valueAt_typed D source payload
  have resultTyped : valueAt D (types.ordinary f.resultType) result.1 = some (checked.result ▸ evaluated.1) := by
    rw [exactResult]
    exact typedValue checked.result evaluated.1
  have invariant : Inv f types inventory target record := completed_inv inventory result.1 _ resultTyped empty
  have restore := restoreFrameBlock_rep checked.restore saved oracle passes calls world outer frame
    (.running f.body.length) represented (checked.inner (l := l) state finished) locals checked.live restored
  unfold CheckedFinal.block
  refine ⟨record, ?_, invariant, inv_encoded f types inventory target record invariant⟩
  rw [restore, checked.inner_exec state finished oracle passes calls world outer locals, removeLocals_ok]
  rw [exactResult]


/-- An admitted arm contains the checked command for its exact phase.
    In particular a Waiting tag keeps the same callee plan as its await
    and only the last Running tag can use the result expression. -/
public inductive PhasePlan (elaboration : Elaboration D V Λ types f) : Phase → Type where
  | cancelled : PhasePlan elaboration .cancelled
  | completed : PhasePlan elaboration .completed
  | bind {tag} (checked : CheckedBinding elaboration tag) : PhasePlan elaboration (.running tag)
  | start {tag} (checked : CheckedAwait elaboration tag) : PhasePlan elaboration (.running tag)
  | poll {tag} (checked : CheckedAwait elaboration tag) : PhasePlan elaboration (.waiting tag checked.future)
  | final (checked : CheckedFinal elaboration) : PhasePlan elaboration (.running f.body.length)

@[expose] public def checkPhase (elaboration : Elaboration D V Λ types f) :
    (phase : Phase) → Except String (PhasePlan elaboration phase)
  | .cancelled => .ok .cancelled
  | .completed => .ok .completed
  | .running tag =>
    match f.body.drop tag with
    | .bind .. :: _ => (checkBindingAt elaboration tag).map .bind
    | .await .. :: _ => (checkAwaitAt elaboration tag).map .start
    | [] => do
      if final : tag = f.body.length then
        let checked ← checkFinal elaboration
        pure (final.symm ▸ PhasePlan.final checked)
      else throw "async: running tag is outside the declaration"
  | .waiting tag future => do
    let checked ← checkAwaitAt elaboration tag
    if same : future = checked.future then pure (same.symm ▸ PhasePlan.poll checked)
    else throw "async: waiting tag belongs to a different await"

/-- The whole phase table is resolved before any code is emitted.
    Each entry has the dependent type of its canonical record payload. -/
@[expose] public def checkPhaseTable (elaboration : Elaboration D V Λ types f) :
    Except String ((index : Fin (phases f).length) → PhasePlan elaboration ((phases f).get index)) :=
  Parser.sammle (phases f).length (fun index => PhasePlan elaboration ((phases f).get index))
    (fun index => checkPhase elaboration ((phases f).get index))

@[expose] public def PhasePlan.block {elaboration : Elaboration D V Λ types f}
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) :
    {phase : Phase} → PhasePlan elaboration phase → Block D V l (phaseType types f phase :: Γ) Λ Λ
  | _, .cancelled | _, .completed => .cons (.assignVar (.there finished) .tru) .nil
  | _, .bind checked => checked.block .here (.there state)
  | _, .start checked => checked.start .here (.there state)
  | _, .poll checked => checked.poll .here (.there state) (.there finished)
  | _, .final checked => checked.block .here (.there state) (.there finished)

/-- Emit the ordinary G dispatch from the complete checked phase table. -/
@[expose] public def checkedDispatch {elaboration : Elaboration D V Λ types f}
    (table : (index : Fin (phases f).length) → PhasePlan elaboration ((phases f).get index))
    (state : Var Γ (stateType types f)) (finished : Var Γ .bool) : Stmt D V l Γ Λ Λ :=
  phaseDispatch types f state (fun index => (table index).block state finished)

public theorem checkedDispatch_selects {elaboration : Elaboration D V Λ types f}
    (table : (index : Fin (phases f).length) → PhasePlan elaboration ((phases f).get index))
    (inventory : Inventory D) (state : Var Γ (stateType types f)) (finished : Var Γ .bool)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (source : State (Value D) (Child D types))
    (represented : Inv f types inventory source (env.get state)) :
    ∃ (index : Fin (phases f).length) (value : Wert D (phaseType types f ((phases f).get index))),
      PhaseRep D types f ((phases f).get index) source value ∧
      MarksRep inventory ((phases f).get index) source ∧
      execStmt oracle passes calls (checkedDispatch (l := l) table state finished) world env =
        (execBlock oracle passes calls ((table index).block state finished) world (.cons value env)).schrumpf :=
  phaseDispatch_selects types f inventory state (fun index => (table index).block state finished)
    oracle passes calls world env source represented

end Gabbro.Grammatik.Async.Representation
