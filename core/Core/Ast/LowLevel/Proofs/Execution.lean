module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level rule, unit and progress proofs

Use the same fixed source instruction to prove the ideal equation and the
concrete equation. The linearisation point is the local transition that
produces its result. The two private relations are empty.

- `IdealAussage`
- `EinheitAussage`
- `ImplAussage`
- `FortschrittAussage`
-/

namespace Gabbro.Core.Ast.LowLevel

/-- One ideal step is determined by the plan and the successor it writes, and
    the ideal rule of the fixed instruction is exactly that step. -/
theorem execution_ideal (form : Form) : IdealAussage form := by
  intro k scope tree op hElab
  constructor
  · intro c s w es es' s1 s2 h1 h2
    change ∃ t, op.evaluate s c = some t ∧ es = [plan] ∧ s1 = t.apply c s at h1
    change ∃ t, op.evaluate s c = some t ∧ es' = [plan] ∧ s2 = t.apply c s at h2
    rcases h1 with ⟨t1, he1, hes1, hs1⟩
    rcases h2 with ⟨t2, he2, hes2, hs2⟩
    constructor
    · rw [hes1, hes2]
    · have ht : t1 = t2 := by
        rw [he1] at he2
        cases he2
        rfl
      rw [hs1, hs2, ht]
  · intro c s w plans next
    rfl

/-- The unit has zero private steps, equality as its local-state relation and
    empty before/after relations, which commute trivially with every other. -/
theorem execution_einheit (form : Form) : EinheitAussage form := by
  intro k scope tree op hElab
  constructor
  · rfl
  constructor
  · rfl
  · intro other
    exact ⟨fun s s1 s2 h _ => False.elim h,
           fun s s1 s2 _ h => False.elim h⟩

/-- The concrete rule refines exactly when the evaluation produces a transfer;
    both then fix the same plan and successor. -/
theorem execution_impl (form : Form) : ImplAussage form := by
  intro k scope tree op hElab c s w plans next
  cases hEval : op.evaluate s c <;>
    simp [Instruction.rule, Instruction.impl, Instruction.ideal, hEval]

/-- At a live head the evaluation has a result, so the ideal rule has a step;
    the blocking relation of this system is empty. -/
theorem execution_fortschritt (form : Form) : FortschrittAussage form := by
  intro k scope tree op hElab s c hhead
  cases hEval : op.evaluate s c with
  | none =>
      exfalso
      have hnone : (unit op).system.kopf s c = none := by
        change head op s c = none
        rw [head]
        cases hs : s.status c <;> simp [hs, hEval]
      rw [hnone] at hhead
      cases hhead
  | some transfer =>
      left
      refine ⟨(), [plan], transfer.apply c s, ?_⟩
      change ∃ t, op.evaluate s c = some t ∧ [plan] = [plan] ∧
        transfer.apply c s = t.apply c s
      exact ⟨transfer, hEval, rfl, rfl⟩

end Gabbro.Core.Ast.LowLevel
