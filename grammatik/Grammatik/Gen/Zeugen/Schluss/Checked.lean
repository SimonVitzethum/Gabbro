/- Accepted and refused lists under the current gates. Structural coverage
   of the former candidate list does not establish coverage of these lists. -/
module

public import Grammatik.Gen.Zeugen.Schluss.GateAudit
public import Grammatik.Gen.Zeugen.M.ScalarRead

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- M contains only fixtures with a full acceptance proof. -/
def Mw : List Einsatz :=
  [ScalarRead.e, Reset.Good.e, M16_13.e, M169_350.e, M103_803.e, M103_131.e, M49_50.e]

/-- N includes fragment refusals as well as structural refusals. GateAudit
    records why the former candidates are refused; it does not call their
    contracts false. -/
def Nw : List Einsatz := structuralRefusals ++
  [M99_824.e, M47_549.e, M99_825.e]

theorem checked_m : ∀ m ∈ Mw, m.gueltig = true := by
  intro m member
  simp only [Mw, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ScalarRead.e_gueltig
  · exact Reset.Good.e_gueltig
  · exact M16_13.e_gueltig
  · exact M169_350.e_gueltig
  · exact M103_803.e_gueltig
  · exact M103_131.e_gueltig
  · exact GateAudit.m49_50_checked

theorem checked_n : ∀ n ∈ Nw, n.gueltig = false := by
  intro n member
  simp only [Nw, structuralRefusals, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl)
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
  · exact GateAudit.m99_824_refused
  · exact GateAudit.m47_549_refused
  · exact GateAudit.m99_825_refused

/-- The scalar-read fine cell survives with full checker acceptance. -/
theorem checked_read_zeuge : ScalarRead.e ∈ Mw ∧ ScalarRead.e.gueltig = true ∧
    ScalarRead.e.HatF ⟨0, 0, 4, false, []⟩ :=
  ⟨List.mem_cons_self, ScalarRead.e_gueltig, ScalarRead.e_hatF⟩

/-- The lock cell now has an accepted witness in the ordinary M list. -/
theorem checked_m_lock_cell_zeuge :
    M16_13.e ∈ Mw ∧ M16_13.e.gueltig = true ∧
      M16_13.e.Hat ⟨3, 0, true, [true, true]⟩ :=
  ⟨by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true],
    M16_13.e_gueltig, M16_13.e_hat _ (by decide)⟩

#print axioms checked_m
#print axioms checked_n
#print axioms GateAudit.m16_source_checked_zeuge

end Gabbro.Grammatik.Gen.Zeugen
