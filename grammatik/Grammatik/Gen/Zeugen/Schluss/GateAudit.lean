/- Verdict classification of the earlier structural candidates. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit
public import Grammatik.Gen.Zeugen.Schluss.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.GateAudit

open Gabbro.Grammatik Gabbro.Grammatik.Gen
open Gabbro.Grammatik.Gen.Zeugen.Gap

private theorem verdict_iff_reset (e : Einsatz) (refused : e.gueltig = false) :
    e.gueltig = true ↔ e = Reset.Good.e := by
  constructor
  · intro accepted
    rw [refused] at accepted
    exact Bool.noConfusion accepted
  · intro same
    rw [same, Reset.Good.e_gueltig] at refused
    exact Bool.noConfusion refused

/-- Exact classification of every old M candidate, including the accepted
    reset fixture. No unsupported fixture is called a false ensures. -/
theorem old_m_verdicts : ∀ e ∈ structuralWitnesses, e.gueltig = true ↔ e = Reset.Good.e := by
  intro e member
  simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact verdict_iff_reset _ m99_824_refused
  · exact verdict_iff_reset _ m47_549_refused
  · exact verdict_iff_reset _ m169_350_refused
  · exact verdict_iff_reset _ m16_13_refused
  · exact verdict_iff_reset _ m49_50_refused
  · exact verdict_iff_reset _ m103_803_refused
  · exact verdict_iff_reset _ m103_131_refused
  · exact verdict_iff_reset _ m99_825_refused
  · exact ⟨fun _ => rfl, fun _ => Reset.Good.e_gueltig⟩

end Gabbro.Grammatik.Gen.Zeugen.GateAudit
