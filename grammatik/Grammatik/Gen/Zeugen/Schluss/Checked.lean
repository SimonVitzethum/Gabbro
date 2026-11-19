/- Accepted and refused lists under the current gates. Structural coverage
   of the former candidate list does not establish coverage of these lists. -/
module

public import Grammatik.Gen.Zeugen.Schluss.GateAudit
public import Grammatik.Gen.Zeugen.Gap
public import Grammatik.Gen.Zeugen.M.ScalarRead
public import Grammatik.Gen.Zeugen.M.Recovery

@[expose] public section

set_option maxRecDepth 4096

namespace Gabbro.Grammatik.Gen.Zeugen

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- M contains only fixtures with a full acceptance proof. -/
def Mw : List Einsatz := Recovery.allFixtures

/-- N contains structural faults and the same-body false-postcondition twin. -/
def Nw : List Einsatz := structuralRefusals ++ [Vertraege.Pruefer.AtomicReadAudit.negative]

theorem checked_m : ∀ m ∈ Mw, m.gueltig = true := Recovery.all_checked

theorem checked_n : ∀ n ∈ Nw, n.gueltig = false := by
  intro n member
  simp only [Nw, structuralRefusals, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  · exact N16_5.e_gueltig
  · exact N18_0.e_gueltig
  · exact N18_4.e_gueltig
  · exact N19_0.e_gueltig
  · exact N19_2.e_gueltig
  · exact N19_5.e_gueltig
  · exact N19_7.e_gueltig
  · exact N20_1.e_gueltig
  · exact N23_4.e_gueltig
  · exact N24_0.e_gueltig
  · exact N3_0.e_gueltig
  · exact N47_P.e_gueltig
  · exact N47_45.e_gueltig
  · exact Reset.Bad.e_gueltig
  · exact Vertraege.Pruefer.AtomicReadAudit.false_contract_refused_zeuge

/-- Full acceptance excludes every restored candidate from the gap list. -/
theorem restored_disjoint : ∀ e ∈ GateAudit.restored, e ∉ Gap.fragmentGaps := by
  intro e member gap
  have accepted := GateAudit.restored_checked e member
  have refused := Gap.checked_gap e gap
  rw [accepted] at refused
  exact Bool.noConfusion refused

/-- A concrete remaining hole, not a claim that the cell is impossible for
    every accepted source program. W1/W2 still need coverage evidence. -/
theorem checked_m_missing_indirect_cell :
    ∀ m ∈ Mw, ¬ m.Hat ⟨0, 0, true, [true, true, false]⟩ := by
  intro m member present
  have covered := (Recovery.all_cells_iff ⟨0, 0, true, [true, true, false]⟩).mp
    ⟨m, member, present⟩
  exact (by decide : ⟨0, 0, true, [true, true, false]⟩ ∉ Recovery.allCells) covered

#print axioms checked_m
#print axioms checked_n

end Gabbro.Grammatik.Gen.Zeugen
