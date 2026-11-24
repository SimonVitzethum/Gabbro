module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.Merge.MergeObligations
public import Core.Ast.LowLevel.Mem.Proofs.Merge.MergePreservation
public import Core.Ast.LowLevel.Mem.Proofs.Merge.MergeSatisfiability
public import Core.Ast.LowLevel.Mem.Proofs.Kern

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

theorem merge_meaning : MergeMeaningAussage := by
  intro target s c first second
  constructor
  · intro missing
    cases hfirst : heldMemRegion target s c first with
    | none =>
        simp only [MemInstruction.evaluate, hfirst, Option.bind_eq_bind, Option.bind_none]
    | some _ =>
        cases missing with
        | inl h1 =>
            rw [hfirst] at h1
            cases h1
        | inr h2 =>
            simp only [MemInstruction.evaluate, hfirst, h2, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none]
  · intro left right hfirst hsecond
    let adjacent := first ≠ second ∧ left.extent.von < left.extent.bis ∧
      right.extent.von < right.extent.bis ∧
      (left.extent.bis = right.extent.von ∨ right.extent.bis = left.extent.von)
    constructor
    · intro adj
      let joined : MemRegion :=
        ⟨⟨min left.extent.von right.extent.von, max left.extent.bis right.extent.bis⟩,
          left.backing ++ right.backing⟩
      let next : MemFrame :=
        { (s.lokal c) with
          result := some (.merged joined)
          regions := ((s.lokal c).regions.set first (some joined)).set second none }
      refine ⟨next, joined, ?_, rfl, rfl, ?_, rfl, ?_⟩
      · dsimp [adjacent] at adj
        simp only [MemInstruction.evaluate, hfirst, hsecond, Option.bind_eq_bind, Option.bind_some,
          if_pos adj]
        rfl
      · dsimp [next]
        rw [List.getElem?_set_self']
        cases h : ((s.lokal c).regions.set first (some joined))[second]? with
        | none => rfl
        | some _ => rfl
      · intro addr
        change min left.extent.von right.extent.von ≤ addr ∧
            addr < max left.extent.bis right.extent.bis ↔
          (left.extent.von ≤ addr ∧ addr < left.extent.bis) ∨
          (right.extent.von ≤ addr ∧ addr < right.extent.bis)
        rcases adj with ⟨hne, hlv, hrv, hbis | hbis⟩
        · have hmin : min left.extent.von right.extent.von = left.extent.von :=
            min_eq_left (by omega)
          have hmax : max left.extent.bis right.extent.bis = right.extent.bis :=
            max_eq_right (by omega)
          rw [hmin, hmax, hbis]
          omega
        · have hmin : min left.extent.von right.extent.von = right.extent.von :=
            min_eq_right (by omega)
          have hmax : max left.extent.bis right.extent.bis = left.extent.bis :=
            max_eq_left (by omega)
          rw [hmin, hmax, hbis]
          omega
    · intro nadj
      dsimp [adjacent] at nadj
      simp only [MemInstruction.evaluate, hfirst, hsecond, Option.bind_eq_bind, Option.bind_some,
        if_neg nadj]

theorem merge_aussage : MergeAussage :=
  ⟨memObligationsKern_alle .merge, merge_meaning, merge_erfuellbar⟩

end Gabbro.Core.Ast.LowLevel
