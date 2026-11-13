module

public import Grammatik.Nebenlaeufigkeit.Async.Layout
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

namespace Gabbro.Grammatik.Async

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The only inputs still needed from segment elaboration are ordinary typed
    blocks. Resource indices agree at dispatch boundaries. A segment may use
    calls/locks internally; its G proof must restore the boundary resources.
    The payload binder supplies precisely the selected record's type. -/
@[expose] public def dispatchArms : (cases : List (Option Ty)) →
    ((i : Fin cases.length) → Block D V l (ArmCtx Γ (cases.get i)) Λ Λ) →
    Arms D V l Γ Λ Λ cases
  | [], _ => .nil
  | c :: cs, bodies => .cons (bodies ⟨0, Nat.zero_lt_succ cs.length⟩)
      (dispatchArms cs (fun i => bodies ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

/-- This is a canonical G statement, not a semantic callback table. -/
@[expose] public def dispatch (cases : List (Option Ty))
    (value : Expr D Γ Λ (.sum cases))
    (bodies : (i : Fin cases.length) → Block D V l (ArmCtx Γ (cases.get i)) Λ Λ) :
    Stmt D V l Γ Λ Λ := .onTag value (dispatchArms cases bodies)

/-- Generic arm selection used by machine G itself. There is no per-program
    certificate and no second evaluator for the generated dispatcher. -/
public theorem dispatchArms_select (cases : List (Option Ty))
    (bodies : (i : Fin cases.length) → Block D V l (ArmCtx Γ (cases.get i)) Λ Λ)
    (i : Fin cases.length) (payload : Nutzlast D.Fn D.passt (cases.get i)) :
    armWahlG (dispatchArms cases bodies)
        ⟨i, Fall.ofNutzlast D.Fn D.passt cases i payload⟩ =
      ⟨cases.get i, bodies i, payload⟩ := by
  revert bodies i
  induction cases with
  | nil => intro _ i; exact (Nat.not_lt_zero _ i.isLt).elim
  | cons c cs ih =>
    intro bodies i payload
    rcases i with ⟨index, valid⟩
    cases index with
    | zero => rfl
    | succ index =>
      exact ih (fun j => bodies ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        ⟨index, Nat.lt_of_succ_lt_succ valid⟩ payload

/-- Exposes the selected body at an arbitrary (possibly bare) case. This is
    the local proof fact needed by both onTag unfold rules of G. -/
public theorem dispatchArms_select_value (cases : List (Option Ty))
    (bodies : (i : Fin cases.length) → Block D V l (ArmCtx Γ (cases.get i)) Λ Λ)
    (value : Wert D (.sum cases)) :
    armWahlG (dispatchArms cases bodies) value =
      ⟨cases.get value.1, bodies value.1,
        Fall.toNutzlast D.Fn D.passt cases value.1 value.2⟩ := by
  obtain ⟨index, payload⟩ := value
  have h := dispatchArms_select cases bodies index
    (Fall.toNutzlast D.Fn D.passt cases index payload)
  simpa only [Fall.of_to] using h

/-- Construction followed by generated dispatch feeds the original typed
    payload to exactly its own segment. This connects the record constructor
    with canonical expression evaluation and G arm selection. -/
public theorem stateExpr_dispatch (types : TypeResolution) (f : AsyncFn)
    (bodies : (i : Fin (stateCases types f).length) →
      Block D V l (ArmCtx Γ ((stateCases types f).get i)) Λ Λ)
    (phase : Fin (stateCases types f).length)
    (payload : NutzlastExpr D Γ Λ ((stateCases types f).get phase))
    (entry world : World D) (environment : Env D Γ) :
    armWahlG (dispatchArms (stateCases types f) bodies)
      (eval entry (stateDiscriminant types f (stateExpr types f phase payload))
        world environment) =
      ⟨(stateCases types f).get phase, bodies phase,
        evalNutz entry payload world environment⟩ :=
  dispatchArms_select (stateCases types f) bodies phase (evalNutz entry payload world environment)

/-- One dispatch body for the generated state schema. -/
@[expose] public def stateStepBody (types : TypeResolution) (f : AsyncFn)
    (state : Expr D Γ Λ (stateType types f))
    (bodies : (i : Fin (stateCases types f).length) →
      Block D V l (ArmCtx Γ ((stateCases types f).get i)) Λ Λ) : Block D V l Γ Λ Λ :=
  .cons (dispatch (stateCases types f) (stateDiscriminant types f state) bodies) .nil

/-- Finite ordinary retry around state dispatch. The existing retry overflow
    branch remains explicit: proving it unreachable needs the segment
    simulation, not a relaxed budget or an implicit fairness assumption. -/
@[expose] public def pollBody (types : TypeResolution) (f : AsyncFn)
    (state : Expr D Γ Λ (stateType types f)) (finished : Expr D Γ Λ .bool)
    (bodies : (i : Fin (stateCases types f).length) →
      Block D V true (ArmCtx Γ ((stateCases types f).get i)) Λ Λ)
    (exhausted : Block D V l Γ Λ Λ) : Block D V l Γ Λ Λ :=
  .cons (.retry (2 * f.body.length + 2) finished
    (stateStepBody types f state bodies) exhausted) .nil

/-- The resource-consuming epilogue clears the state only after release
    returns normally. A direct destructor call is one possible release. -/
@[expose] public def cancelEpilogue (types : TypeResolution) (f : AsyncFn)
    (state : Var Γ (stateType types f)) (release : Stmt D V l Γ Λ []) :
    Block D V l Γ Λ [] :=
  .cons release (.cons (.assignVar state (cancelledExpr types f)) .nil)

/-- Destruction sees the full payload in each arm. After those hooks, an
    ordinary resource-consuming statement must discharge Λ. Only THEN may the
    value be overwritten with Cancelled. There is no generic empty cleanup. -/
@[expose] public def cancelBody (types : TypeResolution) (f : AsyncFn)
    (state : Var Γ (stateType types f))
    (children : (i : Fin (stateCases types f).length) →
      Block D V l (ArmCtx Γ ((stateCases types f).get i)) Λ Λ)
    (release : Stmt D V l Γ Λ []) : Block D V l Γ Λ [] :=
  .cons (dispatch (stateCases types f)
    (stateDiscriminant types f (.var state)) children)
    (cancelEpilogue types f state release)

end Gabbro.Grammatik.Async
