module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.TaskLowering

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}

/-- Keep both updated slots when a child is still active. When both
    children have finished, cache the payloads in source order. -/
@[expose] public def collectJoin (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (first : Var Γ (taskStorageType types (0 :: path) left))
    (second : Var Γ (taskStorageType types (1 :: path) right))
    (out : Var Γ (taskStorageType types path (.join left right))) : Stmt D V l Γ Λ Λ :=
  collectStored first second
    (.cons (.assignVar (.there out)
      (joinChildrenExpr types path left right (.var (.there first)) (.var (.there second)))) .nil)
    (.cons (.assignVar (.there (.there out))
      (joinChildrenExpr types path left right (.var (.there (.there first))) (.var (.there (.there second))))) .nil)
    (.cons (.assignVar (.there (.there out))
      (.case [some (taskActiveType types path (.join left right)), some (taskResultType types path (.join left right))]
        ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩
        (.val (.prod (types.recordName (3 :: path)) (.cons (.var (.there .here)) (.cons (.var .here) .nil)))))) .nil)

-- Each recursive statement is generated in the environment containing
-- the two private child slots and the active parent payload.
@[expose] public abbrev JoinCtx (types : TypeResolution) (path : List Nat) (left right : FutureExpr) (Γ : Ctx) :=
  taskStorageType types (1 :: path) right :: taskStorageType types (0 :: path) left ::
    taskActiveType types path (.join left right) :: Γ

@[expose] public def joinActiveBlock (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (out : Var Γ (taskStorageType types path (.join left right)))
    (first second : Stmt D V l (JoinCtx types path left right Γ) Λ Λ) :
    Block D V l (taskActiveType types path (.join left right) :: Γ) Λ Λ :=
  .bind (.prodGet (.var .here) .head)
    (.bind (.prodGet (.var (.there .here)) (.tail .head))
      (.cons first (.cons second (.cons
        (collectJoin types path left right (.there .here) .here (.there (.there (.there out)))) .nil))))

/-- The cached branch skips the join's entire child tree. -/
@[expose] public def joinTaskStmt (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (out : Var Γ (taskStorageType types path (.join left right)))
    (first second : Stmt D V l (JoinCtx types path left right Γ) Λ Λ) :
    Stmt D V l Γ Λ Λ :=
  .onTag (.var out) (.cons (joinActiveBlock types path left right out first second) (.cons .nil .nil))

/-- Sample the two slots from the active payload before any poll, then
    run the second statement in the actual world of the first. -/
public theorem joinActiveBlock_exec (types : TypeResolution) (path : List Nat) (left right : FutureExpr)
    (out : Var Γ (taskStorageType types path (.join left right)))
    (first second : Stmt D V l (JoinCtx types path left right Γ) Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ)
    (a : Wert D (taskStorageType types (0 :: path) left)) (b : Wert D (taskStorageType types (1 :: path) right)) :
    let initial : Env D (JoinCtx types path left right Γ) := .cons b (.cons a (.cons (a, b, ()) env))
    execBlock oracle passes calls (joinActiveBlock types path left right out first second) world (.cons (a, b, ()) env) =
      (((match execStmt oracle passes calls first world initial with
        | .ok middle leftDone =>
          match execStmt oracle passes calls second middle leftDone with
          | .ok final rightDone => execStmt oracle passes calls
              (collectJoin (Λ := Λ) types path left right (.there .here) .here (.there (.there (.there out)))) final rightDone
          | failure => failure
        | failure => failure) : Ausgang V l (JoinCtx types path left right Γ)).schrumpf).schrumpf := by
  intro initial
  simp only [joinActiveBlock, execBlock, Expr.orte, World.lese, World.merke, List.map_nil, List.nil_append,
    eval, Env.get, prodGetW]
  change (((match execStmt oracle passes calls first world initial with
    | .ok middle leftDone => _
    | failure => _).schrumpf).schrumpf = _
  cases execStmt oracle passes calls first world initial with
  | ok middle leftDone =>
    cases execStmt oracle passes calls second middle leftDone with
    | ok final rightDone =>
      cases execStmt oracle passes calls
        (collectJoin (Λ := Λ) types path left right (.there .here) .here (.there (.there (.there out)))) final rightDone <;> rfl
    | _ => rfl
  | _ => rfl

/-- The semantic poll event determines the physical tag. A Ready tag
    additionally carries the result of the exact typed projection. -/
public theorem pollRep_tag {types : TypeResolution} {path : List Nat} {future : FutureExpr}
    {event : Poll (Value D)} {task : Task (Value D) (Child D types)}
    {record : Wert D (taskStorageType types path future)}
    (polled : PollRep D types path future event task)
    (stored : TaskRep D types path future task record) :
    match event with
    | .pending => ∃ payload, record =
        readyAnswer D (taskActiveType types path future) (taskResultType types path future) payload
    | .ready value => ∃ result, record =
        pendingAnswer D (taskActiveType types path future) (taskResultType types path future) result ∧
        valueAt D (taskResultType types path future) value = some result := by
  cases polled with
  | pending _ active =>
    cases stored with
    | callActive => exact ⟨_, rfl⟩
    | joinActive => exact ⟨_, rfl⟩
    | callReady | joinReady => exact (active _ rfl).elim
  | ready _ _ =>
    cases stored with
    | callReady | joinReady => exact ⟨_, rfl, by assumption⟩

/-- A reconstructed parent value is the exact encoding of the semantic
    join successor. Both children have already been evaluated. -/
public theorem collectJoin_exec {types : TypeResolution} (path : List Nat) (left right : FutureExpr)
    (first : Var Γ (taskStorageType types (0 :: path) left))
    (second : Var Γ (taskStorageType types (1 :: path) right))
    (out : Var Γ (taskStorageType types path (.join left right)))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) {lp rp : Poll (Value D)} {a b : Task (Value D) (Child D types)}
    (leftTask : TaskRep D types (0 :: path) left a (env.get first))
    (rightTask : TaskRep D types (1 :: path) right b (env.get second))
    (leftEvent : PollRep D types (0 :: path) left lp a) (rightEvent : PollRep D types (1 :: path) right rp b) :
    let successor : Task (Value D) (Child D types) :=
      match lp, rp with
      | .ready first, .ready second => .ready (.pair first second)
      | _, _ => .join a b
    ∃ value, execStmt oracle passes calls (collectJoin (V := V) (Λ := Λ) (l := l) types path left right
        first second out) world env = .ok world (env.set out value) ∧
      TaskRep D types path (.join left right) successor value := by
  obtain leftTag := pollRep_tag leftEvent leftTask
  obtain rightTag := pollRep_tag rightEvent rightTask
  cases lp with
  | pending =>
    obtain ⟨payload, tag⟩ := leftTag
    unfold collectJoin
    erw [collectStored_leftActive oracle passes calls first second _ _ _ world env payload tag]
    exact ⟨_, rfl, .joinActive leftTask rightTask⟩
  | ready aValue =>
    obtain ⟨aResult, aTag, aTyped⟩ := leftTag
    cases rp with
    | pending =>
      obtain ⟨payload, tag⟩ := rightTag
      unfold collectJoin
      erw [collectStored_rightActive oracle passes calls first second _ _ _ world env aResult payload aTag tag]
      exact ⟨_, rfl, .joinActive leftTask rightTask⟩
    | ready bValue =>
      obtain ⟨bResult, bTag, bTyped⟩ := rightTag
      unfold collectJoin
      erw [collectStored_bothCached oracle passes calls first second _ _ _ world env aResult bResult aTag bTag]
      refine ⟨_, rfl, .joinReady ?_⟩
      change valueAt D (taskResultType types path (.join left right)) (.pair aValue bValue) =
        some (aResult, bResult, ())
      simp only [taskResultType, valueAt, aTyped, bTyped, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def] <;> rfl

end Gabbro.Grammatik.Async.Representation
