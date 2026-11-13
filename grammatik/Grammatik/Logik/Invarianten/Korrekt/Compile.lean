module

public import Grammatik.Logik.Invarianten.Korrekt.Projection
public import Grammatik.Logik.Invarianten.Korrekt.Budget
import Mathlib.Tactic.Tauto

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

/-- A successful `Except` bind ran its first action successfully. -/
private theorem except_bind_ok {ε σ τ : Type} {x : Except ε σ} {f : σ → Except ε τ} {y : τ}
    (h : x >>= f = Except.ok y) : ∃ a, x = Except.ok a ∧ f a = Except.ok y := by
  cases x with
  | error e =>
      have contra : (Except.error e : Except ε τ) = Except.ok y := h
      cases contra
  | ok a => exact ⟨a, rfl, h⟩

/-- Successful executions compose through the actual StateT/Except path. -/
theorem work_bind_success {action : Work β} {next : β → Work γ}
    {initial finish : Meter} {result : γ}
    (h : (action >>= next).run initial = .ok (result, finish)) :
    ∃ middle state, action.run initial = .ok (middle, state) ∧
      (next middle).run state = .ok (result, finish) := by
  change (action.run initial >>= fun pair => (next pair.1).run pair.2) = _ at h
  obtain ⟨⟨middle, state⟩, first, rest⟩ := except_bind_ok h
  exact ⟨middle, state, first, rest⟩

theorem work_pure_result {value result : β} {initial finish : Meter}
    (h : (pure value : Work β).run initial = .ok (result, finish)) : result = value := by
  cases h
  rfl

theorem charge_then_success {amount : Nat} {action : Work β}
    {initial finish : Meter} {result : β}
    (h : (do charge amount; action).run initial = .ok (result, finish)) :
    ∃ state, action.run state = .ok (result, finish) := by
  obtain ⟨middle, state, _, next⟩ := work_bind_success h
  cases middle
  exact ⟨state, next⟩

theorem negateMetered_result {body result : QF α} {initial finish : Meter}
    (h : (negateMetered body).run initial = .ok (result, finish)) : result = body.neg := by
  obtain ⟨state, next⟩ := charge_then_success h
  exact work_pure_result next

theorem eliminateMetered_result [DecidableEq α] {name : α} {body result : QF α}
    {initial finish : Meter}
    (h : (eliminateMetered name body).run initial = .ok (result, finish)) :
    result = eliminateOne name body := by
  obtain ⟨state, next⟩ := charge_then_success h
  obtain ⟨state', done⟩ := charge_then_success next
  exact work_pure_result done

/-- Zero and negative source divisors are handled by the very same semantics. -/
theorem divides_denote (divisor : Int) (term : LTerm α) (values : Assignment α) :
    (divides divisor term).denote values ↔ divisor ∣ term.denote values := by
  cases h : divisor.natAbs with
  | zero =>
      have hz : divisor = 0 := Int.natAbs_eq_zero.mp h
      simp [divides, equalZero_denote, hz]
  | succ n =>
      simp only [divides, h, atom_denote, Relation.denote]
      rw [← h]
      exact Int.natAbs_dvd

/-- Every successful metered execution preserves the whole formula at every
    assignment, for arbitrary alternation and shadowing of named quantifiers. -/
theorem compile_denote [DecidableEq α] (formula : LProp α)
    (initial finish : Meter) (result : QF α)
    (success : (compile formula).run initial = .ok (result, finish)) (values : Assignment α) :
    result.denote values ↔ formula.denote values := by
  classical
  induction formula generalizing initial finish result values with
  | tru =>
      obtain ⟨_, h⟩ := charge_then_success success
      have := work_pure_result h
      subst result
      rfl
  | fls =>
      obtain ⟨_, h⟩ := charge_then_success success
      have := work_pure_result h
      subst result
      rfl
  | le left right =>
      obtain ⟨_, h⟩ := charge_then_success success
      have := work_pure_result h
      subst result
      simp only [atom_denote, Relation.denote, subTerm_denote, LTerm.denote, LProp.denote]
      omega
  | lt left right =>
      obtain ⟨_, h⟩ := charge_then_success success
      have := work_pure_result h
      subst result
      simp only [atom_denote, Relation.denote, subTerm_denote, LProp.denote]
      omega
  | eq left right =>
      obtain ⟨_, h⟩ := charge_then_success success
      have := work_pure_result h
      subst result
      simp only [equalZero_denote, subTerm_denote, LProp.denote]
      omega
  | dvd divisor term =>
      obtain ⟨_, h⟩ := charge_then_success success
      have := work_pure_result h
      subst result
      exact divides_denote divisor term values
  | not body ih =>
      obtain ⟨middle, state, first, next⟩ := work_bind_success success
      have he := negateMetered_result next
      subst result
      show _ ↔ ¬ body.denote values
      rw [neg_denote, ih _ _ _ first values]
  | and left right ihLeft ihRight =>
      obtain ⟨state, start⟩ := charge_then_success success
      obtain ⟨a, stateA, ha, rest⟩ := work_bind_success start
      obtain ⟨b, stateB, hb, done⟩ := work_bind_success rest
      have he := work_pure_result done
      subst result
      show _ ↔ left.denote values ∧ right.denote values
      rw [conj_denote, ihLeft _ _ _ ha values, ihRight _ _ _ hb values]
  | or left right ihLeft ihRight =>
      obtain ⟨state, start⟩ := charge_then_success success
      obtain ⟨a, stateA, ha, rest⟩ := work_bind_success start
      obtain ⟨b, stateB, hb, done⟩ := work_bind_success rest
      have he := work_pure_result done
      subst result
      show _ ↔ left.denote values ∨ right.denote values
      rw [disj_denote, ihLeft _ _ _ ha values, ihRight _ _ _ hb values]
  | imp left right ihLeft ihRight =>
      obtain ⟨state, start⟩ := charge_then_success success
      obtain ⟨a, stateA, ha, rest⟩ := work_bind_success start
      obtain ⟨b, stateB, hb, rest'⟩ := work_bind_success rest
      obtain ⟨negative, stateN, hn, done⟩ := work_bind_success rest'
      have he := work_pure_result done
      subst result
      rw [negateMetered_result hn, disj_denote, neg_denote,
        ihLeft _ _ _ ha values, ihRight _ _ _ hb values]
      simp only [LProp.denote]
      tauto
  | ex name body ih =>
      obtain ⟨middle, state, first, next⟩ := work_bind_success success
      rw [eliminateMetered_result next, eliminateOne_denote]
      change (∃ x : Int, middle.denote (values.bind name x)) ↔
        ∃ x : Int, body.denote (values.bind name x)
      exact exists_congr (fun x => ih _ _ _ first _)
  | all name body ih =>
      obtain ⟨middle, state, first, rest⟩ := work_bind_success success
      obtain ⟨negative, stateN, hn, rest'⟩ := work_bind_success rest
      obtain ⟨eliminated, stateE, he, done⟩ := work_bind_success rest'
      rw [negateMetered_result done, neg_denote, eliminateMetered_result he, eliminateOne_denote,
        negateMetered_result hn]
      simp only [neg_denote, ih _ _ _ first, LProp.denote, not_exists, not_not]

/-- The unreachable error arm of `elimination` is discharged by P14's totality. -/
theorem elimination_denote [DecidableEq α] (formula : LProp α) (values : Assignment α) :
    (elimination formula).1.denote values ↔ formula.denote values := by
  obtain ⟨result, spent, success⟩ := compile_success formula
  simpa only [elimination, success] using compile_denote formula _ _ result success values

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
