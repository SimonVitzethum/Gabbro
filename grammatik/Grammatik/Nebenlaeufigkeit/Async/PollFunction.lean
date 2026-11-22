module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedPoll

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

@[expose] public def pollResultType (types : TypeResolution) (f : AsyncFn) : Ty :=
  .sum [some (types.ordinary f.resultType), some (stateType types f)]

@[expose] public def readyReply {types : TypeResolution} {f : AsyncFn}
    (value : Expr D Γ Λ (types.ordinary f.resultType)) : Expr D Γ Λ (pollResultType types f) :=
  .case _ ⟨0, Nat.zero_lt_succ 1⟩ (.val value)

@[expose] public def pendingReply {types : TypeResolution} {f : AsyncFn}
    (state : Var Γ (stateType types f)) : Expr D Γ Λ (pollResultType types f) :=
  .case _ ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ (.val (.var state))

@[expose] public def resultExpr (result : V.erg = some (pollResultType types f))
    (value : Expr D Γ Λ (pollResultType types f)) : ErgExpr D Γ Λ V.erg :=
  result.symm ▸ ErgExpr.val value

@[expose] public def resultValue (result : V.erg = some (pollResultType types f))
    (value : Wert D (pollResultType types f)) : ErgVal D V.erg :=
  result.symm ▸ value

public theorem resultExpr_eval (result : V.erg = some (pollResultType types f))
    (value : Expr D Γ Λ (pollResultType types f)) (world : World D) (env : Env D Γ) :
    (resultExpr result value).orte = value.orte ∧
      evalErg world (resultExpr result value) world env = resultValue result (eval world value world env) := by
  generalize same : V.erg = declared at result ⊢
  subst declared
  exact ⟨rfl, rfl⟩

/-- Invalid activation of a completed or cancelled future is refused at
    the private poll entry. Running and Waiting dispatch are silent. -/
@[expose] public def pollGuard (types : TypeResolution) (f : AsyncFn)
    (state : Var Γ (stateType types f)) : Stmt D V l Γ Λ Λ :=
  phaseDispatch types f state (fun i => match (phases f).get i with
    | .completed | .cancelled => rejectBlock _ _ _ _ _
    | _ => .nil)

@[expose] public def pollAnswerArm (state : Var Γ (stateType types f))
    (result : V.erg = some (pollResultType types f)) (exit : Λ.Perm V.ende) :
    (phase : Phase) → Block D V l (phaseType types f phase :: Γ) Λ Λ
  | .completed => .cons (.ret (resultExpr result (readyReply (.prodGet (.var .here) .head))) exit) .nil
  | .waiting .. => .cons (.ret (resultExpr result (pendingReply (.there state))) exit) .nil
  | .running .. | .cancelled => rejectBlock _ _ _ _ _

@[expose] public def pollAnswer (state : Var Γ (stateType types f))
    (result : V.erg = some (pollResultType types f)) (exit : Λ.Perm V.ende) : Stmt D V l Γ Λ Λ :=
  phaseDispatch types f state (fun i => pollAnswerArm state result exit ((phases f).get i))

/-- Generate an ordinary private G function. The single input is the
    future state, and its normal result is the canonical Ready/Pending sum. -/
@[expose] public def pollFunction {elaboration : Elaboration D V Λ types f}
    (table : (index : Fin (phases f).length) → PhasePlan elaboration ((phases f).get index))
    (result : V.erg = some (pollResultType types f)) (exit : Λ.Perm V.ende) :
    Endblock D V false [stateType types f] Λ :=
  .bind .fls
    (.cons (pollGuard types f (.there .here))
      (.cons (checkedRetryStmt table (.there .here) .here (rejectBlock _ _ _ _ _))
        (.cons (pollAnswer (.there .here) result exit)
          (.ret (resultExpr result (pendingReply (.there .here))) exit))))

end Gabbro.Grammatik.Async.Representation
