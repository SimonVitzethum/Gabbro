module

public import Grammatik.Gen.Zeugen.Erreicht
public import Grammatik.Gen.Zeugen.M.M99_824
public import Grammatik.Gen.Zeugen.M.M99_825
public import Grammatik.Gen.Zeugen.M.M47_549
public import Grammatik.Gen.Zeugen.M.M169_350
public import Grammatik.Gen.Zeugen.M.M16_13
public import Grammatik.Gen.Zeugen.M.M49_50
public import Grammatik.Gen.Zeugen.M.M103_803
public import Grammatik.Gen.Zeugen.M.M103_131
public import Grammatik.Gen.Zeugen.N.N16_5
public import Grammatik.Gen.Zeugen.N.N18_0
public import Grammatik.Gen.Zeugen.N.N18_4
public import Grammatik.Gen.Zeugen.N.N19_0
public import Grammatik.Gen.Zeugen.N.N19_2
public import Grammatik.Gen.Zeugen.N.N19_5
public import Grammatik.Gen.Zeugen.N.N19_7
public import Grammatik.Gen.Zeugen.N.N20_1
public import Grammatik.Gen.Zeugen.N.N23_4
public import Grammatik.Gen.Zeugen.N.N24_0
public import Grammatik.Gen.Zeugen.N.N3_0
public import Grammatik.Gen.Zeugen.N.N47_P
public import Grammatik.Gen.Zeugen.N.N47_45
public import Grammatik.Gen.Abdeckung.Satz.Neutral
public import Grammatik.Gen.Abdeckung.Satz.Unmoeglich
public import Grammatik.Gen.Zeugen.Schluss.Teil2
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Gabbro.Grammatik.Gen.Zeugen
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz

/-- The old witnesses cover structural cells. This does not assert that all
    witnesses are accepted by the strengthened checker. -/
theorem zeugen_deckung : ∀ x ∈ zellAlle, x.schlecht = false →
    (∃ m ∈ structuralWitnesses, m.Hat x) ∨ (∀ e : Einsatz, e.Hat x → e.gueltig = false) := by
    intro x hx hs
    rw [zellAlle_liste] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gut (u_2_0_sig false false))
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut (u_2_0_sig true false))
    · first | exact Or.inl ⟨M99_824.e, by simp [structuralWitnesses], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M103_803.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_803.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M49_50.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut (u_2_0_sig false true))
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut (u_2_0_sig true true))
    · exact Or.inr (nie_gut (u_2_0_11 false false))
    · exact Or.inr (nie_gut (u_2_0_11 true false))
    · exact Or.inr (nie_gut (u_2_0_11 false true))
    · exact Or.inr (nie_gut (u_2_0_11 true true))
    · exact absurd hs (by decide)
    · exact Or.inl ⟨M103_803.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_803.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M103_131.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_131.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp [structuralWitnesses], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp [structuralWitnesses], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gut u_4_01)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false true false rfl e hv)
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false false true rfl e hv)
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false true true rfl e hv)
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M16_13.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inl ⟨M49_50.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut u_7_1_110)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M49_50.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gut (u_8_ax false false))
    · exact Or.inr (nie_gut (u_8_ax true false))
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut (u_8_ax false true))
    · exact Or.inr (nie_gut (u_8_ax true true))
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M16_13.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M16_13.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [structuralWitnesses], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M16_13.e, by simp only [structuralWitnesses, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inl ⟨Reset.Good.e, by simp [structuralWitnesses], Reset.Good.e_hat⟩

/-- **A neutral compiler correct on the structural candidates is correct on every valid source program.** -/
theorem compiler_zeugen_korrekt (K : Einsatz → Prop) (hK : NeutralKorrekt K) (hM : ∀ m ∈ structuralWitnesses, K m) (e : Einsatz)
    (hv : e.gueltig = true) : K e := by
  obtain ⟨ψ, hψ⟩ := hK
  refine (hψ e).2 fun z hz => ?_
  obtain ⟨m, hm, hmz⟩ := zellen_deckt zeugen_deckung e hv z hz
  exact (hψ m).1 (hM m hm) z hmz

end Gabbro.Grammatik.Gen.Zeugen
