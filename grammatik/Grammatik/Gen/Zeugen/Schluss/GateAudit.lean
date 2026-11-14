/- Current classification of the earlier structural candidates. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit
public import Grammatik.Gen.Zeugen.Schluss.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.GateAudit

open Gabbro.Grammatik Gabbro.Grammatik.Gen
open Gabbro.Grammatik.Gen.Zeugen.Gap

private theorem verdict_iff_accepted (e : Einsatz) (refused : e.gueltig = false) :
    e.gueltig = true ↔ e = Reset.Good.e ∨ e = M16_13.e := by
  constructor
  · intro accepted
    rw [refused] at accepted
    exact Bool.noConfusion accepted
  · rintro (rfl | rfl)
    · rw [Reset.Good.e_gueltig] at refused
      exact Bool.noConfusion refused
    · rw [M16_13.e_gueltig] at refused
      exact Bool.noConfusion refused

/-- Preserved lock syntax restores M16, while secondary fragment gaps remain. -/
theorem structural_candidates_verdicts : ∀ e ∈ structuralWitnesses,
    e.gueltig = true ↔ e = Reset.Good.e ∨ e = M16_13.e := by
  intro e member
  simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact verdict_iff_accepted _ m99_824_refused
  · exact verdict_iff_accepted _ m47_549_refused
  · exact verdict_iff_accepted _ m169_350_refused
  · exact ⟨fun _ => Or.inr rfl, fun _ => M16_13.e_gueltig⟩
  · exact verdict_iff_accepted _ m49_50_refused
  · exact verdict_iff_accepted _ m103_803_refused
  · exact verdict_iff_accepted _ m103_131_refused
  · exact verdict_iff_accepted _ m99_825_refused
  · exact ⟨fun _ => Or.inl rfl, fun _ => Reset.Good.e_gueltig⟩

end Gabbro.Grammatik.Gen.Zeugen.GateAudit
