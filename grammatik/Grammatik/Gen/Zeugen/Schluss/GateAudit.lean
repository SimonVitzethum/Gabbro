/- Current classification keeps accepted restorations separate from fragment findings. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit
public import Grammatik.Gen.Zeugen.Schluss.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.GateAudit

open Gabbro.Grammatik Gabbro.Grammatik.Gen
open Gabbro.Grammatik.Gen.Zeugen.Gap

/-- These earlier structural candidates carry full acceptance proofs. -/
def restored : List Einsatz :=
  [Reset.Good.e, M16_13.e, M169_350.e, M103_803.e, M103_131.e, M49_50.e, M99_824.e, M99_825.e]

theorem restored_checked : ∀ e ∈ restored, e.gueltig = true := by
  intro e member
  simp only [restored, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Reset.Good.e_gueltig
  · exact M16_13.e_gueltig
  · exact M169_350.e_gueltig
  · exact M103_803.e_gueltig
  · exact M103_131.e_gueltig
  · exact m49_50_checked
  · exact m99_824_checked
  · exact m99_825_checked

private theorem verdict_iff_restored (e : Einsatz) (refused : e.gueltig = false) :
    e.gueltig = true ↔ e ∈ restored := by
  constructor
  · intro accepted
    rw [refused] at accepted
    exact Bool.noConfusion accepted
  · intro member
    have accepted := restored_checked e member
    rw [refused] at accepted
    exact Bool.noConfusion accepted

/-- The updated gates restore all four coordinated lock fixtures. -/
theorem structural_candidates_verdicts : ∀ e ∈ structuralWitnesses,
    e.gueltig = true ↔ e ∈ restored := by
  intro e member
  simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun _ => by simp [restored], fun _ => m99_824_checked⟩
  · exact verdict_iff_restored _ m47_549_refused
  · exact ⟨fun _ => by simp [restored], fun _ => M169_350.e_gueltig⟩
  · exact ⟨fun _ => by simp [restored], fun _ => M16_13.e_gueltig⟩
  · exact ⟨fun _ => by simp [restored], fun _ => m49_50_checked⟩
  · exact ⟨fun _ => by simp [restored], fun _ => M103_803.e_gueltig⟩
  · exact ⟨fun _ => by simp [restored], fun _ => M103_131.e_gueltig⟩
  · exact ⟨fun _ => by simp [restored], fun _ => m99_825_checked⟩
  · exact ⟨fun _ => by simp [restored], fun _ => Reset.Good.e_gueltig⟩

theorem restored_checked_zeuge : M169_350.e ∈ restored ∧ M169_350.e.gueltig = true :=
  ⟨by simp [restored], M169_350.e_gueltig⟩

end Gabbro.Grammatik.Gen.Zeugen.GateAudit
