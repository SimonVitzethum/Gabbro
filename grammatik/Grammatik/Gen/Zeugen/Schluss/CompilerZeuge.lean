/- Joint premises of the structural compiler theorem, and the obstruction
   to reusing the old witness list as a fully accepted table. -/
module

public import Grammatik.Gen.Zeugen.Schluss.Teil3
public import Grammatik.Gen.Zeugen.Schluss.Checked

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen

open Gabbro.Grammatik.Gen.Zeugen.Gap

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz

/-- A cell-sensitive correctness predicate: every structural cell is good.
    Reset.Bad below witnesses that this predicate is not constantly true. -/
def structuralCompiler (e : Einsatz) : Prop := akzeptiert Einsatz.Hat gutTafel e

theorem structuralCompiler_neutral_zeuge : NeutralKorrekt structuralCompiler :=
  ⟨fun z => gutTafel z = true, fun _ => Iff.rfl⟩

theorem structuralCompiler_m_zeuge : ∀ m ∈ structuralWitnesses, structuralCompiler m := by
  intro m member
  simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact M99_824.e_strukturell
  · exact M47_549.e_strukturell
  · exact M169_350.e_strukturell
  · exact M16_13.e_strukturell
  · exact M49_50.e_strukturell
  · exact M103_803.e_strukturell
  · exact M103_131.e_strukturell
  · exact M99_825.e_strukturell
  · exact ((einsatz_akzeptiert _).mp Reset.Good.e_gueltig).1

/-- All premises of compiler_zeugen_korrekt hold together on a real static
    array, and the same compiler predicate rejects the zero-less array. -/
theorem compiler_zeugen_korrekt_zeuge :
    NeutralKorrekt structuralCompiler ∧
    (∀ m ∈ structuralWitnesses, structuralCompiler m) ∧
    Reset.Good.e.gueltig = true ∧
    structuralCompiler Reset.Good.e ∧ ¬ structuralCompiler Reset.Bad.e := by
  refine ⟨structuralCompiler_neutral_zeuge, structuralCompiler_m_zeuge,
    Reset.Good.e_gueltig, ?_, ?_⟩
  · exact compiler_zeugen_korrekt structuralCompiler structuralCompiler_neutral_zeuge
      structuralCompiler_m_zeuge Reset.Good.e Reset.Good.e_gueltig
  · intro accepted
    have bad := accepted _ Reset.Bad.e_hat
    change false = true at bad
    exact Bool.false_ne_true bad

/-- Atomic reads trigger the first refusal in the current checked fragment. -/
theorem m99_refused_zeuge : M99_824.e.gueltig = false := GateAudit.m99_824_refused

/-- W2 cannot use these fixed M/N lists: the gut_m premise is contradictory.
    This does not assert that every possible replacement table is impossible. -/
theorem old_tafel_impossible_zeuge : ¬ Tafel structuralWitnesses structuralRefusals := by
  intro table
  have accepted := table.gut_m M99_824.e (by simp [structuralWitnesses])
  rw [m99_refused_zeuge] at accepted
  exact Bool.noConfusion accepted

#print axioms compiler_zeugen_korrekt_zeuge
#print axioms old_tafel_impossible_zeuge

end Gabbro.Grammatik.Gen.Zeugen
