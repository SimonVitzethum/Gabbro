module

public import Grammatik.Logik.Invarianten.Elim.Decision

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

/-- The unbounded execution succeeds and a sufficiently large finite allowance
    reproduces its value and exact charge. This is a resource property only. -/
private def Covers (action : Work α) : Prop :=
  ∀ start, ∃ value finish, start ≤ finish ∧
    action.run
      { limit := none
        spent := start } =
      .ok (value,
        { limit := none
          spent := finish }) ∧
    ∀ cap, finish ≤ cap →
      action.run
        { limit := some cap
          spent := start } =
        .ok (value,
          { limit := some cap
            spent := finish })

private theorem covers_pure (value : α) : Covers (pure value : Work α) := by
  intro start
  exact ⟨value, start, by omega, rfl, fun _ _ => rfl⟩

private theorem covers_bind {action : Work α} {next : α → Work β}
    (first : Covers action) (rest : ∀ value, Covers (next value)) :
    Covers (action >>= next) := by
  intro start
  obtain ⟨middle, used, hused, hfirst, hfirstCap⟩ := first start
  obtain ⟨value, finish, hfinish, hrest, hrestCap⟩ := rest middle used
  refine ⟨value, finish, by omega, ?_, ?_⟩
  · change (action.run
        { limit := none
          spent := start } >>= fun pair =>
        (next pair.1).run pair.2) = _
    rw [hfirst]
    exact hrest
  · intro cap hcap
    have hmiddle : used ≤ cap := by omega
    change (action.run
        { limit := some cap
          spent := start } >>= fun pair =>
        (next pair.1).run pair.2) = _
    rw [hfirstCap cap hmiddle]
    exact hrestCap cap hcap

private theorem covers_charge (amount : Nat) : Covers (charge amount) := by
  intro start
  refine ⟨(), start + amount, by omega, rfl, ?_⟩
  intro cap hcap
  simp [charge, StateT.run, StateT.mk, hcap]

private theorem covers_negate (body : QF α) : Covers (negateMetered body) :=
  covers_bind (covers_charge _) (fun _ => covers_pure _)

private theorem covers_eliminate [DecidableEq α] (name : α) (body : QF α) :
    Covers (eliminateMetered name body) :=
  covers_bind (covers_charge _) (fun _ =>
    covers_bind (covers_charge _) (fun _ => covers_pure _))

private theorem covers_compile [DecidableEq α] (formula : LProp α) :
    Covers (compile formula) := by
  induction formula with
  | tru => exact covers_bind (covers_charge _) (fun _ => covers_pure _)
  | fls => exact covers_bind (covers_charge _) (fun _ => covers_pure _)
  | le left right => exact covers_bind (covers_charge _) (fun _ => covers_pure _)
  | lt left right => exact covers_bind (covers_charge _) (fun _ => covers_pure _)
  | eq left right => exact covers_bind (covers_charge _) (fun _ => covers_pure _)
  | dvd divisor term => exact covers_bind (covers_charge _) (fun _ => covers_pure _)
  | not body ih => exact covers_bind ih covers_negate
  | and left right ihLeft ihRight =>
      exact covers_bind (covers_charge _) (fun _ =>
        covers_bind ihLeft (fun a => covers_bind ihRight (fun b => covers_pure (conj a b))))
  | or left right ihLeft ihRight =>
      exact covers_bind (covers_charge _) (fun _ =>
        covers_bind ihLeft (fun a => covers_bind ihRight (fun b => covers_pure (disj a b))))
  | imp left right ihLeft ihRight =>
      exact covers_bind (covers_charge _) (fun _ =>
        covers_bind ihLeft (fun a => covers_bind ihRight (fun b =>
          covers_bind (covers_negate a) (fun negative => covers_pure (disj negative b)))))
  | ex name body ih => exact covers_bind ih (covers_eliminate name)
  | all name body ih =>
      exact covers_bind ih (fun result => covers_bind (covers_negate result) (fun negative =>
        covers_bind (covers_eliminate name negative) covers_negate))

/-- No failure arm is reachable when computing the unbounded elimination. -/
theorem compile_success [DecidableEq α] (formula : LProp α) :
    ∃ result spent, (compile formula).run { limit := none } =
      .ok (result,
        { limit := none
          spent := spent }) := by
  obtain ⟨result, spent, _, success, _⟩ := covers_compile formula 0
  exact ⟨result, spent, success⟩

/-- The exact bound suffices; no assumption about truth or falsehood is needed.
    The closedness premise is required by the declaration-time entry point. -/
theorem budget_sufficient [DecidableEq α] (formula : LProp α) (fuel : Nat)
    (closed : closedUnderB [] formula = true) (enough : Budget formula ≤ fuel) :
    decideWithBudget formula fuel = .ok (decideB formula) := by
  obtain ⟨result, spent, _, unbounded, bounded⟩ := covers_compile formula 0
  have computed : elimination formula = (result, spent) := by
    simp [elimination, unbounded]
  have hspent : spent ≤ fuel := by simpa [Budget, computed] using enough
  have success := bounded fuel hspent
  simp [decideWithBudget, closed, success, decideB, computed]

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
