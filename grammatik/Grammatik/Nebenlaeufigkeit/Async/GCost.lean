module

public import Grammatik.Nebenlaeufigkeit.Async.Resources
public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil1
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Bounds come from the ordinary G cost of EVERY elaborated segment,
    including child poll calls. Source costBound annotations do not enter. -/
public theorem dispatchArms_cost (calls : D.Fn → Nat) (passes limit : Nat)
    (cases : List (Option Ty))
    (bodies : (i : Fin cases.length) → Block D V l (ArmCtx Γ (cases.get i)) Λ Λ)
    (bounded : ∀ i, kostenBlock calls passes (bodies i) ≤ limit) :
    kostenArms calls passes (dispatchArms cases bodies) ≤ limit := by
  revert bodies
  induction cases with
  | nil => intro _ _; exact Nat.zero_le _
  | cons c cs ih =>
    intro bodies bounded
    have first := bounded ⟨0, Nat.zero_lt_succ cs.length⟩
    have remaining := ih
      (fun i => bodies ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => bounded ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    change max (kostenBlock calls passes (bodies ⟨0, Nat.zero_lt_succ cs.length⟩))
      (kostenArms calls passes (dispatchArms cs
        (fun i => bodies ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))) ≤ limit
    omega

/-- Match administration and record projection are charged too. -/
public theorem stateStepBody_cost (types : TypeResolution) (f : AsyncFn)
    (calls : D.Fn → Nat) (passes limit : Nat)
    (state : Expr D Γ Λ (stateType types f))
    (bodies : (i : Fin (stateCases types f).length) →
      Block D V l (ArmCtx Γ ((stateCases types f).get i)) Λ Λ)
    (bounded : ∀ i, kostenBlock calls passes (bodies i) ≤ limit) :
    kostenBlock calls passes (stateStepBody types f state bodies) ≤
      4 + kostenExpr state + limit := by
  have bound := dispatchArms_cost calls passes limit (stateCases types f) bodies bounded
  change 2 + (1 + kostenExpr state) +
    kostenArms calls passes (dispatchArms (stateCases types f) bodies) + 1 ≤ _
  omega

/-- The generated poll's finite G budget includes all retry checks AND its
    explicit overflow branch. No bound on the number of future polls, waiting
    time, scheduler fairness or eventual readiness is inferred. -/
public theorem pollBody_cost (types : TypeResolution) (f : AsyncFn)
    (calls : D.Fn → Nat) (passes limit : Nat)
    (state : Expr D Γ Λ (stateType types f)) (finished : Expr D Γ Λ .bool)
    (bodies : (i : Fin (stateCases types f).length) →
      Block D V true (ArmCtx Γ ((stateCases types f).get i)) Λ Λ)
    (exhausted : Block D V l Γ Λ Λ)
    (bounded : ∀ i, kostenBlock calls passes (bodies i) ≤ limit) :
    kostenBlock calls passes (pollBody types f state finished bodies exhausted) ≤
      5 + (2 * f.body.length + 2) *
        (6 + kostenExpr state + limit + kostenExpr finished) +
        kostenExpr finished + kostenBlock calls passes exhausted := by
  have segment := stateStepBody_cost types f calls passes limit state bodies bounded
  have multiplied := Nat.mul_le_mul_left (2 * f.body.length + 2)
    (Nat.add_le_add_right (Nat.add_le_add_right segment (kostenExpr finished)) 2)
  have administrative : (4 + kostenExpr state + limit + kostenExpr finished) + 2 =
      6 + kostenExpr state + limit + kostenExpr finished := by omega
  rw [administrative] at multiplied
  change 2 + (2 * f.body.length + 2) *
    (kostenBlock calls passes (stateStepBody types f state bodies) + kostenExpr finished + 2) +
    (2 + kostenExpr finished + kostenBlock calls passes exhausted) + 1 ≤ _
  omega

/-- Preserve the canonical cost engine's call gate, including its refusal of
    unpriced indirect calls. The generated dispatcher never grants a callee
    or a forever loop that its ordinary segment certificate did not grant. -/
public theorem dispatchArms_calls (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (cases : List (Option Ty))
    (bodies : (i : Fin cases.length) → Block D V l (ArmCtx Γ (cases.get i)) Λ Λ)
    (allowed : ∀ i, rufeB direct indirect forever (bodies i) = true) :
    rufeArms direct indirect forever (dispatchArms cases bodies) = true := by
  revert bodies
  induction cases with
  | nil => intro _ _; rfl
  | cons c cs ih =>
    intro bodies allowed
    change rufeB direct indirect forever (bodies ⟨0, Nat.zero_lt_succ cs.length⟩) &&
      rufeArms direct indirect forever (dispatchArms cs
        (fun i => bodies ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) = true
    rw [allowed ⟨0, Nat.zero_lt_succ cs.length⟩,
      ih _ (fun i => allowed ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)]
    rfl

public theorem pollBody_calls (types : TypeResolution) (f : AsyncFn)
    (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (state : Expr D Γ Λ (stateType types f)) (finished : Expr D Γ Λ .bool)
    (bodies : (i : Fin (stateCases types f).length) →
      Block D V true (ArmCtx Γ ((stateCases types f).get i)) Λ Λ)
    (exhausted : Block D V l Γ Λ Λ)
    (allowed : ∀ i, rufeB direct indirect forever (bodies i) = true)
    (overflow : rufeB direct indirect forever exhausted = true) :
    rufeB direct indirect forever (pollBody types f state finished bodies exhausted) = true := by
  have arms := dispatchArms_calls direct indirect forever (stateCases types f) bodies allowed
  simp only [pollBody, stateStepBody, dispatch, rufeB, rufeS, arms, overflow,
    Bool.true_and, Bool.and_true]

end Gabbro.Grammatik.Async
