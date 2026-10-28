/-
  File:      Grammatik/Gen/Zeugen/Schluss.lean
  Subject:   GENERATED (`gen-zellen-sammeln`, `ZellenSchluss.lean`): every cell of the universe has its reason, so
             M and N are complete and a neutral checker or compiler that treats them right treats every program of
             the source right. Do not edit.
             (Edited 2026-10-21: the witness `M99_825` joined `M99_824`, see there.)
-/
import Grammatik.Gen.Zeugen.Erreicht
import Grammatik.Gen.Zeugen.M.M99_824
import Grammatik.Gen.Zeugen.M.M99_825
import Grammatik.Gen.Zeugen.M.M47_549
import Grammatik.Gen.Zeugen.M.M169_350
import Grammatik.Gen.Zeugen.M.M16_13
import Grammatik.Gen.Zeugen.M.M49_50
import Grammatik.Gen.Zeugen.M.M103_803
import Grammatik.Gen.Zeugen.M.M103_131
import Grammatik.Gen.Zeugen.N.N16_5
import Grammatik.Gen.Zeugen.N.N18_0
import Grammatik.Gen.Zeugen.N.N18_4
import Grammatik.Gen.Zeugen.N.N19_0
import Grammatik.Gen.Zeugen.N.N19_2
import Grammatik.Gen.Zeugen.N.N19_5
import Grammatik.Gen.Zeugen.N.N19_7
import Grammatik.Gen.Zeugen.N.N20_1
import Grammatik.Gen.Zeugen.N.N23_4
import Grammatik.Gen.Zeugen.N.N24_0
import Grammatik.Gen.Zeugen.N.N3_0
import Grammatik.Gen.Zeugen.N.N47_20
import Grammatik.Gen.Zeugen.N.N47_45
import Grammatik.Gen.Abdeckung.Satz.Neutral
import Grammatik.Gen.Abdeckung.Satz.Unmoeglich

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

theorem schluss_schlecht : SchlechtGedeckt ncZiel erreicht := by
  intro x hx hs
  rw [zellAlle_liste] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e h => absurd h (u_0_ohne false false e)
  · exact absurd hs (by decide)
  · exact fun e h => absurd h (u_0_ohne true false e)
  · exact absurd hs (by decide)
  · exact fun e h => absurd h (u_0_ohne false true e)
  · exact absurd hs (by decide)
  · exact fun e h => absurd h (u_0_ohne true true e)
  · exact fun e h => ⟨N47_20.bnoetig, fun w hw => by
        obtain rfl := (by decide : ∀ w ∈ N47_20.bnoetig, w = ⟨0, 0, true, [true, true, true]⟩) w hw
        exact h, N47_20.zellen⟩
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact fun e h => absurd h (u_1_0_110 e)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact fun e h => ⟨N24_0.bnoetig, fun w hw => by
        obtain rfl := (by decide : ∀ w ∈ N24_0.bnoetig, w = ⟨2, 0, true, [false, false, false, false]⟩) w hw
        exact h, N24_0.zellen⟩
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
  · exact fun e h => ⟨N23_4.bnoetig, fun w hw => by
        obtain rfl := (by decide : ∀ w ∈ N23_4.bnoetig, w = ⟨2, 1, true, [false, false]⟩) w hw
        exact h, N23_4.zellen⟩
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
      · exact ⟨N18_0.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N18_0.bnoetig, w = ⟨5, 0, true, [true, false]⟩ ∨ w = ⟨6, 0, true, [false, true, false]⟩) w hw with rfl | rfl <;> assumption,
        N18_0.zellen⟩
      · exact ⟨N18_4.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N18_4.bnoetig, w = ⟨5, 0, true, [true, false]⟩ ∨ w = ⟨6, 0, true, [true, true, false]⟩) w hw with rfl | rfl <;> assumption,
        N18_4.zellen⟩
  · exact fun e h => by
      obtain ⟨m, hm⟩ := m_5_0 false true e h
      cases m
      · exact ⟨N19_0.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N19_0.bnoetig, w = ⟨5, 0, true, [false, true]⟩ ∨ w = ⟨6, 0, true, [false, false, true]⟩) w hw with rfl | rfl <;> assumption,
        N19_0.zellen⟩
      · exact ⟨N19_5.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N19_5.bnoetig, w = ⟨5, 0, true, [false, true]⟩ ∨ w = ⟨6, 0, true, [true, false, true]⟩) w hw with rfl | rfl <;> assumption,
        N19_5.zellen⟩
  · exact fun e h => by
      obtain ⟨m, hm⟩ := m_5_0 true true e h
      cases m
      · exact ⟨N19_2.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N19_2.bnoetig, w = ⟨5, 0, true, [true, true]⟩ ∨ w = ⟨6, 0, true, [false, true, true]⟩) w hw with rfl | rfl <;> assumption,
        N19_2.zellen⟩
      · exact ⟨N19_7.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N19_7.bnoetig, w = ⟨5, 0, true, [true, true]⟩ ∨ w = ⟨6, 0, true, [true, true, true]⟩) w hw with rfl | rfl <;> assumption,
        N19_7.zellen⟩
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact fun e h => by
      have hm := (m_6_0 true true false rfl e h).1
      exact ⟨N18_4.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N18_4.bnoetig, w = ⟨6, 0, true, [true, true, false]⟩ ∨ w = ⟨5, 0, true, [true, false]⟩) w hw with rfl | rfl <;> assumption,
        N18_4.zellen⟩
  · exact absurd hs (by decide)
  · exact fun e h => by
      have hm := (m_6_0 true false true rfl e h).1
      exact ⟨N19_5.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N19_5.bnoetig, w = ⟨6, 0, true, [true, false, true]⟩ ∨ w = ⟨5, 0, true, [false, true]⟩) w hw with rfl | rfl <;> assumption,
        N19_5.zellen⟩
  · exact absurd hs (by decide)
  · exact fun e h => by
      have hm := (m_6_0 true true true rfl e h).1
      exact ⟨N19_7.bnoetig, fun w hw => by
        rcases (by decide : ∀ w ∈ N19_7.bnoetig, w = ⟨6, 0, true, [true, true, true]⟩ ∨ w = ⟨5, 0, true, [true, true]⟩) w hw with rfl | rfl <;> assumption,
        N19_7.zellen⟩
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact fun e h => ⟨N3_0.bnoetig, fun w hw => by
        obtain rfl := (by decide : ∀ w ∈ N3_0.bnoetig, w = ⟨6, 1, true, [true, true, true, false]⟩) w hw
        exact h, N3_0.zellen⟩
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact fun e h => ⟨N20_1.bnoetig, fun w hw => by
        obtain rfl := (by decide : ∀ w ∈ N20_1.bnoetig, w = ⟨7, 0, true, [false, false]⟩) w hw
        exact h, N20_1.zellen⟩
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
  · exact fun e h => ⟨N47_45.bnoetig, fun w hw => by
        obtain rfl := (by decide : ∀ w ∈ N47_45.bnoetig, w = ⟨8, 0, true, [true, false, false]⟩) w hw
        exact h, N47_45.zellen⟩
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
  · exact fun e h => ⟨N16_5.bnoetig, fun w hw => by
        obtain rfl := (by decide : ∀ w ∈ N16_5.bnoetig, w = ⟨9, 0, true, [true, true, true, false]⟩) w hw
        exact h, N16_5.zellen⟩
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

/-- **M and N are complete.** -/
theorem mn_vollstaendig : Tafel (mGen ncZiel) (nGen ncZiel) :=
  tafel_erzeugt ncZiel erreicht schluss_gut schluss_schlecht erreicht_raum

/-- **A neutral checker (a function: terminating, deterministic) that answers like the model on M and N answers like
    the model on every program of the source.** -/
theorem pruefer_korrekt (C : Einsatz → Bool) (hC : Neutral C) (hM : ∀ m ∈ mGen ncZiel, C m = m.gueltig)
    (hN : ∀ n ∈ nGen ncZiel, C n = n.gueltig) (e : Einsatz) : C e = e.gueltig :=
  pruefer_hinreichend ncZiel erreicht schluss_gut schluss_schlecht erreicht_raum C hC hM hN e

/-- **A neutral compiler correct on M is correct on every valid program of the source.** -/
theorem compiler_korrekt (K : Einsatz → Prop) (hK : NeutralKorrekt K) (hM : ∀ m ∈ mGen ncZiel, K m) (e : Einsatz)
    (hv : e.gueltig = true) : K e :=
  compiler_hinreichend ncZiel erreicht schluss_gut schluss_schlecht erreicht_raum K hK hM e hv

/-! ## The witnesses alone: M and N as explicit lists of programs of the source -/

/-- **M**: the valid witnesses. -/
def Mw : List Einsatz := [M99_824.e, M47_549.e, M169_350.e, M16_13.e, M49_50.e, M103_803.e, M103_131.e, M99_825.e]

/-- **N**: the refused tests. -/
def Nw : List Einsatz := [N16_5.e, N18_0.e, N18_4.e, N19_0.e, N19_2.e, N19_5.e, N19_7.e, N20_1.e, N23_4.e, N24_0.e, N3_0.e, N47_20.e, N47_45.e]

theorem erreicht_mw : ∀ w ∈ erreicht, ∃ m ∈ Mw, m.Hat w := by
  intro w hw
  simp only [erreicht, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M103_803.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_803.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
  · exact ⟨M49_50.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M103_803.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_803.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M103_131.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M103_131.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
  · exact ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M16_13.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M49_50.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M49_50.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M49_50.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M16_13.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M16_13.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M16_13.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M16_13.e_hat _ (by decide)⟩

/-- **The table of the witness lists**: M and N are complete. -/
theorem zeugen_tafel : Tafel Mw Nw where
  gut_m m hm := by
    simp only [Mw, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact M99_824.e_gueltig
    · exact M47_549.e_gueltig
    · exact M169_350.e_gueltig
    · exact M16_13.e_gueltig
    · exact M49_50.e_gueltig
    · exact M103_803.e_gueltig
    · exact M103_131.e_gueltig
    · exact M99_825.e_gueltig
  gut x hx hs := by
    rw [zellAlle_liste] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · first | exact Or.inl ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true], M99_825.e_hat _ (by decide)⟩
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
    · first | exact Or.inl ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true], M99_825.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · exact Or.inl ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
    · first | exact Or.inl ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact Or.inl ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true], M99_825.e_hat _ (by decide)⟩
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
  n_schlecht n hn := by
    simp only [Nw, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  schlecht x hx hs := by
    rw [zellAlle_liste] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact fun e h => ⟨N47_45.e, by simp only [Nw, List.mem_cons, List.not_mem_nil, or_false, or_true], n_deckt Mw erreicht erreicht_mw N47_45.e e N47_45.bnoetig N47_45.e_gedeckt
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
