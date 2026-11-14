/- Accepted and refused lists under the current gates. Structural coverage
   of the former candidate list does not establish coverage of these lists. -/
module

public import Grammatik.Gen.Zeugen.Schluss.GateAudit
public import Grammatik.Gen.Zeugen.Gap
public import Grammatik.Gen.Zeugen.M.ScalarRead

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- M contains only fixtures with a full acceptance proof. -/
def Mw : List Einsatz := [ScalarRead.e, M16_13.e, Reset.Good.e]

/-- N contains wrong programs refused by a structural model gate. -/
def Nw : List Einsatz := structuralRefusals

theorem checked_m : ∀ m ∈ Mw, m.gueltig = true := by
  intro m member
  simp only [Mw, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ScalarRead.e_gueltig
  · exact M16_13.e_gueltig
  · exact Reset.Good.e_gueltig

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
  ⟨List.mem_cons_self, ScalarRead.e_gueltig, ScalarRead.e_hatF⟩

/-- A concrete remaining hole, not a claim that the cell is impossible for
    every accepted source program. W1/W2 still need coverage evidence. -/
theorem checked_m_missing_indirect_cell :
    ∀ m ∈ Mw, ¬ m.Hat ⟨0, 0, true, [true, true, false]⟩ := by
  intro m member
  simp only [Mw, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

#print axioms checked_m
#print axioms checked_n
#print axioms GateAudit.m16_source_accepted_zeuge

end Gabbro.Grammatik.Gen.Zeugen
