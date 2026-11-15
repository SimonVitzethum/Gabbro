module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Waiting

namespace Gabbro.Grammatik.Async.Segment

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
  {Λ : List (Res D)} {result child storage : Ty}

/-- Ready carries the result, Pending carries the UPDATED child storage.
    The poll answer and its payload are two distinct ephemeral binders.
    Pending sets the dispatcher's finished flag after saving its state;
    Ready leaves that flag alone and advances via the supplied successor. -/
@[expose] public def pollAnswerArms (state : Var Γ storage) (finished : Var Γ Ty.bool)
    (ready : Expr D (result :: Ty.sum [some result, some child] :: Γ) Λ storage)
    (pending : Expr D (child :: Ty.sum [some result, some child] :: Γ) Λ storage) :
    Arms D V l (Ty.sum [some result, some child] :: Γ) Λ Λ [some result, some child] :=
  Arms.cons
    (Block.cons (Stmt.assignVar (Var.there (Var.there state)) ready) Block.nil)
    (Arms.cons
      (Block.cons (Stmt.assignVar (Var.there (Var.there state)) pending)
        (Block.cons (Stmt.assignVar (Var.there (Var.there finished)) Expr.tru) Block.nil))
      Arms.nil)

/-- The first answer is Ready; both constructors have named finite bounds. -/
@[expose] public def readyAnswer (D : Deklaration) (result child : Ty)
    (value : Wert D result) : Wert D (Ty.sum [some result, some child]) :=
  ⟨⟨0, Nat.zero_lt_succ 1⟩, value⟩

@[expose] public def pendingAnswer (D : Deklaration) (result child : Ty)
    (value : Wert D child) : Wert D (Ty.sum [some result, some child]) :=
  ⟨⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩, value⟩

public theorem pollAnswerArms_ready (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : Var Γ storage) (finished : Var Γ Ty.bool)
    (ready : Expr D (result :: Ty.sum [some result, some child] :: Γ) Λ storage)
    (pending : Expr D (child :: Ty.sum [some result, some child] :: Γ) Λ storage)
    (world : World D) (environment : Env D Γ) (value : Wert D result) :
    (execArms O passes calls (pollAnswerArms (V := V) (l := l) state finished ready pending)
      (readyAnswer D result child value) world
      (Env.cons (readyAnswer D result child value) environment)).schrumpf =
      Ausgang.ok (world.lese Λ ready.orte)
        (environment.set state (eval (world.lese Λ ready.orte) ready
          (world.lese Λ ready.orte)
          (Env.cons value (Env.cons (readyAnswer D result child value) environment)))) := rfl

public theorem pollAnswerArms_pending (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : Var Γ storage) (finished : Var Γ Ty.bool)
    (ready : Expr D (result :: Ty.sum [some result, some child] :: Γ) Λ storage)
    (pending : Expr D (child :: Ty.sum [some result, some child] :: Γ) Λ storage)
    (world : World D) (environment : Env D Γ) (updated : Wert D child) :
    (execArms O passes calls (pollAnswerArms (V := V) (l := l) state finished ready pending)
      (pendingAnswer D result child updated) world
      (Env.cons (pendingAnswer D result child updated) environment)).schrumpf =
      Ausgang.ok (world.lese Λ pending.orte)
        ((environment.set state (eval (world.lese Λ pending.orte) pending
          (world.lese Λ pending.orte)
          (Env.cons updated (Env.cons (pendingAnswer D result child updated) environment)))).set
            finished true) := rfl

public theorem pollAnswerArms_calls (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (state : Var Γ storage) (finished : Var Γ Ty.bool)
    (ready : Expr D (result :: Ty.sum [some result, some child] :: Γ) Λ storage)
    (pending : Expr D (child :: Ty.sum [some result, some child] :: Γ) Λ storage) :
    rufeArms direct indirect forever
      (pollAnswerArms (V := V) (l := l) state finished ready pending) = true := rfl

end Gabbro.Grammatik.Async.Segment
