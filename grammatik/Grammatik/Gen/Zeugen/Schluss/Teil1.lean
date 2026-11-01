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

@[expose] public section



set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Gabbro.Grammatik.Gen.Zeugen

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz

theorem zellAlle_liste : zellAlle = [
    ⟨0, 0, true, [false, false, false]⟩,
    ⟨0, 0, true, [true, false, false]⟩,
    ⟨0, 0, true, [false, true, false]⟩,
    ⟨0, 0, true, [true, true, false]⟩,
    ⟨0, 0, true, [false, false, true]⟩,
    ⟨0, 0, true, [true, false, true]⟩,
    ⟨0, 0, true, [false, true, true]⟩,
    ⟨0, 0, true, [true, true, true]⟩,
    ⟨1, 0, true, [false, false, false]⟩,
    ⟨1, 0, true, [true, false, false]⟩,
    ⟨1, 0, true, [false, true, false]⟩,
    ⟨1, 0, true, [true, true, false]⟩,
    ⟨1, 0, true, [false, false, true]⟩,
    ⟨1, 0, true, [true, false, true]⟩,
    ⟨1, 0, true, [false, true, true]⟩,
    ⟨1, 0, true, [true, true, true]⟩,
    ⟨2, 0, true, [false, false, false, false]⟩,
    ⟨2, 0, true, [true, false, false, false]⟩,
    ⟨2, 0, true, [false, true, false, false]⟩,
    ⟨2, 0, true, [true, true, false, false]⟩,
    ⟨2, 0, true, [false, false, true, false]⟩,
    ⟨2, 0, true, [true, false, true, false]⟩,
    ⟨2, 0, true, [false, true, true, false]⟩,
    ⟨2, 0, true, [true, true, true, false]⟩,
    ⟨2, 0, true, [false, false, false, true]⟩,
    ⟨2, 0, true, [true, false, false, true]⟩,
    ⟨2, 0, true, [false, true, false, true]⟩,
    ⟨2, 0, true, [true, true, false, true]⟩,
    ⟨2, 0, true, [false, false, true, true]⟩,
    ⟨2, 0, true, [true, false, true, true]⟩,
    ⟨2, 0, true, [false, true, true, true]⟩,
    ⟨2, 0, true, [true, true, true, true]⟩,
    ⟨2, 1, true, [false, false]⟩,
    ⟨2, 1, true, [true, false]⟩,
    ⟨2, 1, true, [false, true]⟩,
    ⟨2, 1, true, [true, true]⟩,
    ⟨2, 2, false, [false, false, false]⟩,
    ⟨2, 2, false, [true, false, false]⟩,
    ⟨2, 2, false, [false, true, false]⟩,
    ⟨2, 2, false, [true, true, false]⟩,
    ⟨2, 2, false, [false, false, true]⟩,
    ⟨2, 2, false, [true, false, true]⟩,
    ⟨2, 2, false, [false, true, true]⟩,
    ⟨2, 2, false, [true, true, true]⟩,
    ⟨2, 3, false, [false, false, false]⟩,
    ⟨2, 3, false, [true, false, false]⟩,
    ⟨2, 3, false, [false, true, false]⟩,
    ⟨2, 3, false, [true, true, false]⟩,
    ⟨2, 3, false, [false, false, true]⟩,
    ⟨2, 3, false, [true, false, true]⟩,
    ⟨2, 3, false, [false, true, true]⟩,
    ⟨2, 3, false, [true, true, true]⟩,
    ⟨3, 0, true, [false, false]⟩,
    ⟨3, 0, true, [true, false]⟩,
    ⟨3, 0, true, [false, true]⟩,
    ⟨3, 0, true, [true, true]⟩,
    ⟨4, 0, true, [false, false]⟩,
    ⟨4, 0, true, [true, false]⟩,
    ⟨4, 0, true, [false, true]⟩,
    ⟨4, 0, true, [true, true]⟩,
    ⟨5, 0, true, [false, false]⟩,
    ⟨5, 0, true, [true, false]⟩,
    ⟨5, 0, true, [false, true]⟩,
    ⟨5, 0, true, [true, true]⟩,
    ⟨6, 0, true, [false, false, false]⟩,
    ⟨6, 0, true, [true, false, false]⟩,
    ⟨6, 0, true, [false, true, false]⟩,
    ⟨6, 0, true, [true, true, false]⟩,
    ⟨6, 0, true, [false, false, true]⟩,
    ⟨6, 0, true, [true, false, true]⟩,
    ⟨6, 0, true, [false, true, true]⟩,
    ⟨6, 0, true, [true, true, true]⟩,
    ⟨6, 1, true, [false, false, false, false]⟩,
    ⟨6, 1, true, [true, false, false, false]⟩,
    ⟨6, 1, true, [false, true, false, false]⟩,
    ⟨6, 1, true, [true, true, false, false]⟩,
    ⟨6, 1, true, [false, false, true, false]⟩,
    ⟨6, 1, true, [true, false, true, false]⟩,
    ⟨6, 1, true, [false, true, true, false]⟩,
    ⟨6, 1, true, [true, true, true, false]⟩,
    ⟨6, 1, true, [false, false, false, true]⟩,
    ⟨6, 1, true, [true, false, false, true]⟩,
    ⟨6, 1, true, [false, true, false, true]⟩,
    ⟨6, 1, true, [true, true, false, true]⟩,
    ⟨6, 1, true, [false, false, true, true]⟩,
    ⟨6, 1, true, [true, false, true, true]⟩,
    ⟨6, 1, true, [false, true, true, true]⟩,
    ⟨6, 1, true, [true, true, true, true]⟩,
    ⟨7, 0, true, [false, false]⟩,
    ⟨7, 0, true, [true, false]⟩,
    ⟨7, 0, true, [false, true]⟩,
    ⟨7, 0, true, [true, true]⟩,
    ⟨7, 1, false, [false, false, false]⟩,
    ⟨7, 1, false, [true, false, false]⟩,
    ⟨7, 1, false, [false, true, false]⟩,
    ⟨7, 1, false, [true, true, false]⟩,
    ⟨7, 1, false, [false, false, true]⟩,
    ⟨7, 1, false, [true, false, true]⟩,
    ⟨7, 1, false, [false, true, true]⟩,
    ⟨7, 1, false, [true, true, true]⟩,
    ⟨8, 0, true, [false, false, false]⟩,
    ⟨8, 0, true, [true, false, false]⟩,
    ⟨8, 0, true, [false, true, false]⟩,
    ⟨8, 0, true, [true, true, false]⟩,
    ⟨8, 0, true, [false, false, true]⟩,
    ⟨8, 0, true, [true, false, true]⟩,
    ⟨8, 0, true, [false, true, true]⟩,
    ⟨8, 0, true, [true, true, true]⟩,
    ⟨9, 0, true, [false, false, false, false]⟩,
    ⟨9, 0, true, [true, false, false, false]⟩,
    ⟨9, 0, true, [false, true, false, false]⟩,
    ⟨9, 0, true, [true, true, false, false]⟩,
    ⟨9, 0, true, [false, false, true, false]⟩,
    ⟨9, 0, true, [true, false, true, false]⟩,
    ⟨9, 0, true, [false, true, true, false]⟩,
    ⟨9, 0, true, [true, true, true, false]⟩,
    ⟨9, 0, true, [false, false, false, true]⟩,
    ⟨9, 0, true, [true, false, false, true]⟩,
    ⟨9, 0, true, [false, true, false, true]⟩,
    ⟨9, 0, true, [true, true, false, true]⟩,
    ⟨9, 0, true, [false, false, true, true]⟩,
    ⟨9, 0, true, [true, false, true, true]⟩,
    ⟨9, 0, true, [false, true, true, true]⟩,
    ⟨9, 0, true, [true, true, true, true]⟩] := by decide

theorem erreicht_raum : ∀ w ∈ erreicht, RaumGut ncZiel w := by
  intro w hw
  simp only [erreicht, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M169_350.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M103_803.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M169_350.zellen _ (by decide)
  · exact M49_50.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M103_803.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M103_131.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M169_350.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M169_350.zellen _ (by decide)
  · exact M169_350.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M16_13.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M49_50.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M49_50.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M16_13.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M47_549.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M16_13.zellen _ (by decide)
  · first | exact M99_824.zellen _ (by decide) | exact M99_825.zellen _ (by decide)
  · exact M16_13.zellen _ (by decide)

theorem schluss_gut : GutGedeckt ncZiel := by
  intro x hx hs
  rw [zellAlle_liste] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hs (by decide)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact absurd hs (by decide)
  · exact Or.inl (M47_549.zellen _ (by decide))
  · exact absurd hs (by decide)
  · exact Or.inl (M47_549.zellen _ (by decide))
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M169_350.zellen _ (by decide))
  · exact absurd hs (by decide)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · exact absurd hs (by decide)
  · exact Or.inr (nie_gut (u_2_0_sig false false))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inr (nie_gut (u_2_0_sig true false))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M103_803.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M169_350.zellen _ (by decide))
  · exact Or.inl (M49_50.zellen _ (by decide))
  · exact Or.inr (nie_gut (u_2_0_sig false true))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inr (nie_gut (u_2_0_sig true true))
  · exact Or.inr (nie_gut (u_2_0_11 false false))
  · exact Or.inr (nie_gut (u_2_0_11 true false))
  · exact Or.inr (nie_gut (u_2_0_11 false true))
  · exact Or.inr (nie_gut (u_2_0_11 true true))
  · exact absurd hs (by decide)
  · exact Or.inl (M103_803.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M103_131.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M169_350.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M169_350.zellen _ (by decide))
  · exact Or.inl (M169_350.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact absurd hs (by decide)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact absurd hs (by decide)
  · exact Or.inr (nie_gut u_4_01)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false true false rfl e hv)
  · exact absurd hs (by decide)
  · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false false true rfl e hv)
  · exact absurd hs (by decide)
  · exact Or.inr (nie_gueltig fun e hv => ug_6_0 false true true rfl e hv)
  · exact absurd hs (by decide)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M16_13.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · exact absurd hs (by decide)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact absurd hs (by decide)
  · exact Or.inl (M49_50.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inr (nie_gut u_7_1_110)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M49_50.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact absurd hs (by decide)
  · exact Or.inr (nie_gut (u_8_ax false false))
  · exact Or.inr (nie_gut (u_8_ax true false))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inr (nie_gut (u_8_ax false true))
  · exact Or.inr (nie_gut (u_8_ax true true))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M16_13.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact absurd hs (by decide)
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M47_549.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M16_13.zellen _ (by decide))
  · first | exact Or.inl (M99_824.zellen _ (by decide)) | exact Or.inl (M99_825.zellen _ (by decide))
  · exact Or.inl (M16_13.zellen _ (by decide))

end Gabbro.Grammatik.Gen.Zeugen
