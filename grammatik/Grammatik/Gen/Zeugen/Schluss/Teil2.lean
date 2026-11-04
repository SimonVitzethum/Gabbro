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
public import Grammatik.Gen.Zeugen.Schluss.Teil1
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

theorem schluss_schlecht : SchlechtGedeckt ncZiel erreicht := by
  intro x hx hs
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
  · exact fun e h => ⟨Reset.Bad.bnoetig, (fun w hw => by
      have same : w = ⟨10, 0, true, [false]⟩ := by simpa only [Reset.Bad.bnoetig, List.mem_singleton] using hw
      exact same.symm ▸ h), Reset.Bad.zellen⟩
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
def Mw : List Einsatz := [M99_824.e, M47_549.e, M169_350.e, M16_13.e, M49_50.e, M103_803.e, M103_131.e, M99_825.e, Reset.Good.e]

/-- **N**: the refused tests. -/
def Nw : List Einsatz := [N16_5.e, N18_0.e, N18_4.e, N19_0.e, N19_2.e, N19_5.e, N19_7.e, N20_1.e, N23_4.e, N24_0.e, N3_0.e, N47_20.e, N47_45.e, Reset.Bad.e]

theorem erreicht_mw : ∀ w ∈ erreicht, ∃ m ∈ Mw, m.Hat w := by
  intro w hw
  simp only [erreicht, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · first | exact ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
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
  · first | exact ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp [Mw], M99_825.e_hat _ (by decide)⟩
  · exact ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
  · exact ⟨M169_350.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M169_350.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · exact ⟨M47_549.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true], M47_549.e_hat _ (by decide)⟩
  · first | exact ⟨M99_824.e, by simp [Mw], M99_824.e_hat _ (by decide)⟩ | exact ⟨M99_825.e, by simp only [Mw, List.mem_cons, List.not_mem_nil, or_false, or_true, true_or], M99_825.e_hat _ (by decide)⟩
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
  · exact ⟨Reset.Good.e, by simp [Mw], Reset.Good.e_hat⟩

end Gabbro.Grammatik.Gen.Zeugen
