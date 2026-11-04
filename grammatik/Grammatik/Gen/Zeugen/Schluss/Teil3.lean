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
public import Grammatik.Gen.Zeugen.N.N47_20
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

/-- **The table of the witness lists**: M and N are complete. -/
theorem zeugen_tafel : Tafel Mw Nw where
  gut_m m hm := by
    simp only [Mw, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact M99_824.e_gueltig
    · exact M47_549.e_gueltig
    · exact M169_350.e_gueltig
    · exact M16_13.e_gueltig
    · exact M49_50.e_gueltig
    · exact M103_803.e_gueltig
    · exact M103_131.e_gueltig
    · exact M99_825.e_gueltig
    · exact Reset.Good.e_gueltig
  gut x hx hs := by
    rw [zellAlle_liste] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gut (u_2_0_sig false false))
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut (u_2_0_sig true false))
    · first | exact Or.inl ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M103_803.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_803.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M49_50.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut (u_2_0_sig false true))
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut (u_2_0_sig true true))
    · exact Or.inr (nie_gut (u_2_0_11 false false))
    · exact Or.inr (nie_gut (u_2_0_11 true false))
    · exact Or.inr (nie_gut (u_2_0_11 false true))
    · exact Or.inr (nie_gut (u_2_0_11 true true))
    · exact absurd hs (by decide)
    · exact Or.inl ⟨M103_803.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_803.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M103_131.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_131.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gut u_4_01)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false true false rfl e hv)
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false false true rfl e hv)
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false true true rfl e hv)
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M16_13.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inl ⟨M49_50.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut u_7_1_110)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M49_50.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inr (nie_gut (u_8_ax false false))
    · exact Or.inr (nie_gut (u_8_ax true false))
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inr (nie_gut (u_8_ax false true))
    · exact Or.inr (nie_gut (u_8_ax true true))
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M16_13.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M16_13.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M16_13.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
    · exact absurd hs (by decide)
    · exact Or.inl ⟨Reset.Good.e, by simp [Mw], Reset.Good.e_hat⟩

  n_schlecht n hn := by
    simp only [Nw, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact N47_20.e_gueltig
    · exact N47_45.e_gueltig
    · exact Reset.Bad.e_gueltig
  schlecht x hx hs := by
    rw [zellAlle_liste] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun e h => absurd h (u_0_ohne false false e)
    · exact absurd hs (by decide)
    · exact fun e h => absurd h (u_0_ohne true false e)
    · exact absurd hs (by decide)
    · exact fun e h => absurd h (u_0_ohne false true e)
    · exact absurd hs (by decide)
    · exact fun e h => absurd h (u_0_ohne true true e)
    · exact fun e h => ⟨N47_20.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N47_20.e e N47_20.bnoetig N47_20.e_gedeckt
          (fun w hw => by
          obtain rfl := (by decide : ∀ w ∈ N47_20.bnoetig, w = ⟨0, 0, true, [true, true, true]⟩) w hw
          exact h)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => absurd h (u_1_0_110 e)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => ⟨N24_0.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N24_0.e e N24_0.bnoetig N24_0.e_gedeckt
          (fun w hw => by
          obtain rfl := (by decide : ∀ w ∈ N24_0.bnoetig, w = ⟨2, 0, true, [false, false, false, false]⟩) w hw
          exact h)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => ⟨N23_4.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N23_4.e e N23_4.bnoetig N23_4.e_gedeckt
          (fun w hw => by
          obtain rfl := (by decide : ∀ w ∈ N23_4.bnoetig, w = ⟨2, 1, true, [false, false]⟩) w hw
          exact h)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => absurd h (u_3_0_10 e)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => absurd h (u_4_10 e)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => by
        obtain ⟨m, hm⟩ := m_5_0 true false e h
        cases m
        · exact ⟨N18_0.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N18_0.e e N18_0.bnoetig N18_0.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N18_0.bnoetig, w = ⟨5, 0, true, [true, false]⟩ ∨ w = ⟨6, 0, true, [false, true, false]⟩) w hw with rfl | rfl <;> assumption)⟩
        · exact ⟨N18_4.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N18_4.e e N18_4.bnoetig N18_4.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N18_4.bnoetig, w = ⟨5, 0, true, [true, false]⟩ ∨ w = ⟨6, 0, true, [true, true, false]⟩) w hw with rfl | rfl <;> assumption)⟩
    · exact fun e h => by
        obtain ⟨m, hm⟩ := m_5_0 false true e h
        cases m
        · exact ⟨N19_0.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N19_0.e e N19_0.bnoetig N19_0.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N19_0.bnoetig, w = ⟨5, 0, true, [false, true]⟩ ∨ w = ⟨6, 0, true, [false, false, true]⟩) w hw with rfl | rfl <;> assumption)⟩
        · exact ⟨N19_5.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N19_5.e e N19_5.bnoetig N19_5.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N19_5.bnoetig, w = ⟨5, 0, true, [false, true]⟩ ∨ w = ⟨6, 0, true, [true, false, true]⟩) w hw with rfl | rfl <;> assumption)⟩
    · exact fun e h => by
        obtain ⟨m, hm⟩ := m_5_0 true true e h
        cases m
        · exact ⟨N19_2.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N19_2.e e N19_2.bnoetig N19_2.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N19_2.bnoetig, w = ⟨5, 0, true, [true, true]⟩ ∨ w = ⟨6, 0, true, [false, true, true]⟩) w hw with rfl | rfl <;> assumption)⟩
        · exact ⟨N19_7.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N19_7.e e N19_7.bnoetig N19_7.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N19_7.bnoetig, w = ⟨5, 0, true, [true, true]⟩ ∨ w = ⟨6, 0, true, [true, true, true]⟩) w hw with rfl | rfl <;> assumption)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => by
        have hm := (m_6_0 true true false rfl e h).1
        exact ⟨N18_4.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N18_4.e e N18_4.bnoetig N18_4.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N18_4.bnoetig, w = ⟨6, 0, true, [true, true, false]⟩ ∨ w = ⟨5, 0, true, [true, false]⟩) w hw with rfl | rfl <;> assumption)⟩
    · exact absurd hs (by decide)
    · exact fun e h => by
        have hm := (m_6_0 true false true rfl e h).1
        exact ⟨N19_5.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N19_5.e e N19_5.bnoetig N19_5.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N19_5.bnoetig, w = ⟨6, 0, true, [true, false, true]⟩ ∨ w = ⟨5, 0, true, [false, true]⟩) w hw with rfl | rfl <;> assumption)⟩
    · exact absurd hs (by decide)
    · exact fun e h => by
        have hm := (m_6_0 true true true rfl e h).1
        exact ⟨N19_7.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N19_7.e e N19_7.bnoetig N19_7.e_gedeckt
          (fun w hw => by
          rcases (by decide : ∀ w ∈ N19_7.bnoetig, w = ⟨6, 0, true, [true, true, true]⟩ ∨ w = ⟨5, 0, true, [true, true]⟩) w hw with rfl | rfl <;> assumption)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => ⟨N3_0.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N3_0.e e N3_0.bnoetig N3_0.e_gedeckt
          (fun w hw => by
          obtain rfl := (by decide : ∀ w ∈ N3_0.bnoetig, w = ⟨6, 1, true, [true, true, true, false]⟩) w hw
          exact h)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => ⟨N20_1.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], n_deckt Mw erreicht erreicht_mw N20_1.e e N20_1.bnoetig N20_1.e_gedeckt
          (fun w hw => by
          obtain rfl := (by decide : ∀ w ∈ N20_1.bnoetig, w = ⟨7, 0, true, [false, false]⟩) w hw
          exact h)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => ⟨N47_45.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], n_deckt Mw erreicht erreicht_mw N47_45.e e N47_45.bnoetig N47_45.e_gedeckt
          (fun w hw => by
          obtain rfl := (by decide : ∀ w ∈ N47_45.bnoetig, w = ⟨8, 0, true, [true, false, false]⟩) w hw
          exact h)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => ⟨N16_5.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, true_or], n_deckt Mw erreicht erreicht_mw N16_5.e e N16_5.bnoetig N16_5.e_gedeckt
          (fun w hw => by
          obtain rfl := (by decide : ∀ w ∈ N16_5.bnoetig, w = ⟨9, 0, true, [true, true, true, false]⟩) w hw
          exact h)⟩
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact absurd hs (by decide)
    · exact fun e h => ⟨Reset.Bad.e, by simp [Nw],
        n_deckt Mw erreicht erreicht_mw Reset.Bad.e e Reset.Bad.bnoetig Reset.Bad.e_gedeckt (fun w hw => by
          have same : w = ⟨10, 0, true, [false]⟩ := by
            simpa only [Reset.Bad.bnoetig, List.mem_singleton] using hw
          exact same.symm ▸ h)⟩
    · exact absurd hs (by decide)

/-- **A neutral checker that answers like the model on the witness lists M and N answers like the model on every
    program of the source.** -/
theorem pruefer_zeugen_korrekt (C : Einsatz → Bool) (hC : Neutral C) (hM : ∀ m ∈ Mw, C m = m.gueltig)
    (hN : ∀ n ∈ Nw, C n = n.gueltig) (e : Einsatz) : C e = e.gueltig := by
  obtain ⟨φ, hφ⟩ := hC
  have h := einsatz_hinreichend zeugen_tafel φ (fun m hm => by rw [← hφ m, hM m hm]) (fun n hn => by rw [← hφ n, hN n hn]) e
  rw [Bool.eq_iff_iff, hφ e]
  exact h

/-- **A neutral compiler correct on the witness list M is correct on every valid program of the source.** -/
theorem compiler_zeugen_korrekt (K : Einsatz → Prop) (hK : NeutralKorrekt K) (hM : ∀ m ∈ Mw, K m) (e : Einsatz)
    (hv : e.gueltig = true) : K e := by
  obtain ⟨ψ, hψ⟩ := hK
  refine (hψ e).2 fun z hz => ?_
  obtain ⟨m, hm, hmz⟩ := (vollstaendig_aus_tafel zeugen_tafel).gut e z hz ((einsatz_akzeptiert e).2 hv)
  exact (hψ m).1 (hM m hm) z hmz

end Gabbro.Grammatik.Gen.Zeugen
