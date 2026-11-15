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

/-- N contains wrong programs refused by a structural model gate. -/
def Nw : List Einsatz := structuralRefusals

theorem checked_m : ∀ m ∈ Mw, m.gueltig = true := Recovery.all_checked

theorem checked_n : ∀ n ∈ Nw, n.gueltig = false := by
  intro n member
  simp only [Nw, structuralRefusals, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- A wrong reset program jointly witnesses N membership and refusal. -/
theorem checked_n_zeuge : Reset.Bad.e ∈ Nw ∧ Reset.Bad.e.gueltig = false :=
  ⟨by simp [Nw, structuralRefusals], Reset.Bad.e_gueltig⟩

/-- The scalar-read fine cell survives with full checker acceptance. -/
theorem checked_read_zeuge : ScalarRead.e ∈ Mw ∧ ScalarRead.e.gueltig = true ∧
    ScalarRead.e.HatF ⟨0, 0, 4, false, []⟩ :=
  ⟨List.mem_append_right _ List.mem_cons_self, ScalarRead.e_gueltig, ScalarRead.e_hatF⟩

/-- Source preservation restores the unchanged lock fixture to accepted M. -/
theorem m16_restored_zeuge : M16_13.e ∈ Mw ∧ M16_13.e ∉ Gap.fragmentGaps ∧
    M16_13.e.gueltig = true ∧ M16_13.e.Hat ⟨3, 0, true, [true, true]⟩ := by
  refine ⟨?_, ?_, M16_13.e_gueltig, M16_13.e_hat _ (by decide)⟩
  · exact List.mem_append_left _ (List.mem_map.2
      ⟨(M16_13.e, M16_13.zellen), by simp [Recovery.records], rfl⟩)
  · intro member
    have refused := Gap.checked_gap M16_13.e member
    rw [M16_13.e_gueltig] at refused
    exact Bool.noConfusion refused

/-- Full acceptance excludes every restored candidate from the gap list. -/
theorem restored_disjoint : ∀ e ∈ GateAudit.restored, e ∉ Gap.fragmentGaps := by
  intro e member gap
  have accepted := GateAudit.restored_checked e member
  have refused := Gap.checked_gap e gap
  rw [accepted] at refused
  exact Bool.noConfusion refused

theorem restored_disjoint_zeuge : M169_350.e ∈ GateAudit.restored ∧ M169_350.e ∈ Mw ∧
    M169_350.e ∉ Gap.fragmentGaps ∧ M169_350.e.gueltig = true := by
  have restored : M169_350.e ∈ GateAudit.restored := by simp [GateAudit.restored]
  have member : M169_350.e ∈ Mw := List.mem_append_left _ (List.mem_map.2
    ⟨(M169_350.e, M169_350.zellen), by simp [Recovery.records], rfl⟩)
  exact ⟨restored, member, restored_disjoint _ restored, M169_350.e_gueltig⟩

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
#print axioms GateAudit.m16_source_checked_zeuge

end Gabbro.Grammatik.Gen.Zeugen
