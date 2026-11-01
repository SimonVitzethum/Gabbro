/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Operands.lean
  Subject:   Execution of the operand placement of the multiword integer operators, once for all of them.

  `wideBinary_ok` runs the first operand's code, extends it in place, runs the second operand's code behind it,
  extends that, and hands the two canonical `k`-limb operands to the kernel's contract. The contract (`kernel`)
  is stated on actual memory with its exact footprint (`Agree fp d K`); each operator supplies it from its
  execution theorem in `Arithmetik/Wide`. Nothing here depends on which operator runs.
-/
import Stage0.Senke.Ausdruck.Sim
import Stage0.Senke.Welt.Spans.Cell
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Extend
import Stage0.Senke.Ausdruck.Aggregat.WideInt.Fits

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ}
variable {W : Runner.Mem → Prop} {fp : Runner.W} {K d : Nat}

theorem wideBinary_ok {lo1 hi1 lo2 hi2 : Int} (x : Zahl lo1 hi1) (y : Zahl lo2 hi2)
    {ka kb : Nat} (hka : integerWords lo1 hi1 ≤ ka) (hkb : integerWords lo2 hi2 ≤ kb)
    {foot : Nat} {kern : List II} {fa fb : Nat → Option (List II × Nat)} {c : List II} {top : Nat}
    {m : Runner.Mem} {pc : Runner.W} {R : Runner.Mem → Prop}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int lo1 hi1) x)
    (ihb : ∀ cb tb, fb (d + ka) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + ka) cb ρ W reserved → ValueOk L m pc fp K (d + ka) cb (.int lo2 hi2) y)
    (h : wideBinaryL (integerWords lo1 hi1) (integerWords lo2 hi2) ka kb (extSigned lo1) (extSigned lo2)
      d foot kern fa fb = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved)
    (kernel : ∀ (m : Runner.Mem) (pc : Runner.W), Pre L m pc fp K d kern ρ W reserved → d + foot ≤ K →
      WordsAt m fp d (integerEncoding ka x.n) → WordsAt m fp (d + ka) (integerEncoding kb y.n) →
      ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * kern.length), fp⟩ m' ∧ Agree fp d K m m' ∧ R m') :
    Executes m pc fp K d c R := by
  unfold wideBinaryL at h
  split at h
  · next ca ta cb tb heqa heqb =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have positiveA := integerWords_pos' lo1 hi1
    have positiveB := integerWords_pos' lo2 hi2
    have hp' : Pre L m pc fp K d (ca ++ (wideExtendC (extSigned lo1) (integerWords lo1 hi1) ka d ++
        (cb ++ (wideExtendC (extSigned lo2) (integerWords lo2 hi2) kb (d + ka) ++ kern)))) ρ W reserved := by
      simpa only [List.append_assoc] using hp
    -- the first operand
    obtain ⟨m1, run1, ch1, vx1⟩ := iha ca ta heqa (by omega) m pc hp'.left
    have n1 := hp'.next ch1 (Nat.le_refl d) (by omega)
    -- its extension to `ka` limbs
    obtain ⟨m2, run2, ch2, wx2⟩ := wideExtend_run (extSigned lo1) x.n positiveA hka (wideFits_zahl x)
      n1.frame n1.small (by omega) n1.left.code n1.left.far vx1.2
    have n2 := n1.next ch2 (by omega : d ≤ d + ka) (by omega)
    -- the second operand, behind it
    obtain ⟨m3, run3, ch3, vy3⟩ := ihb cb tb heqb (by omega) m2 _ n2.left
    have n3 := n2.next ch3 (Nat.le_refl (d + ka)) (by omega)
    have room := n3.frame.room
    have wx3 : WordsAt m3 fp d (integerEncoding ka x.n) :=
      wx2.agree_low ch3 n2.frame.room (by simp only [integerEncoding_length]; omega) (by omega)
    -- its extension
    obtain ⟨m4, run4, ch4, wy4⟩ := wideExtend_run (extSigned lo2) y.n positiveB hkb (wideFits_zahl y)
      n3.frame n3.small (by omega) n3.left.code n3.left.far vy3.2
    have n4 := n3.next ch4 (Nat.le_refl (d + ka)) (by omega)
    have wx4 : WordsAt m4 fp d (integerEncoding ka x.n) :=
      wx3.agree_low ch4 n3.frame.room (by simp only [integerEncoding_length]; omega) (by omega)
    -- the kernel
    obtain ⟨m5, run5, ch5, post⟩ := kernel m4 _ { n4 with ctx := hp.ctx } (by omega) wx4 wy4
    refine ⟨m5, ?_, ?_, post⟩
    · simpa only [List.length_append, pc_add] using
        run1.trans (run2.trans (run3.trans (run4.trans run5)))
    · exact ch1.trans ((ch2.mono (Nat.le_refl d)).trans (((ch3.mono (by omega : d ≤ d + ka)).trans
        ((ch4.mono (by omega : d ≤ d + ka)).trans ch5))))
  · cases h

/-- A single operand: extended in place, then the kernel. -/
theorem wideUnary_ok {lo hi : Int} (x : Zahl lo hi) {ka : Nat} (hka : integerWords lo hi ≤ ka)
    {foot : Nat} {kern : List II} {fa : Nat → Option (List II × Nat)} {c : List II} {top : Nat}
    {m : Runner.Mem} {pc : Runner.W} {R : Runner.Mem → Prop}
    (iha : ∀ ca ta, fa d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved →
      ValueOk L m pc fp K d ca (.int lo hi) x)
    (h : wideUnaryL (integerWords lo hi) ka (extSigned lo) d foot kern fa = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved)
    (kernel : ∀ (m : Runner.Mem) (pc : Runner.W), Pre L m pc fp K d kern ρ W reserved → d + foot ≤ K →
      WordsAt m fp d (integerEncoding ka x.n) →
      ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * kern.length), fp⟩ m' ∧ Agree fp d K m m' ∧ R m') :
    Executes m pc fp K d c R := by
  unfold wideUnaryL at h
  split at h
  · next ca ta heqa =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have positive := integerWords_pos' lo hi
    have hp' : Pre L m pc fp K d (ca ++ (wideExtendC (extSigned lo) (integerWords lo hi) ka d ++ kern))
        ρ W reserved := by
      simpa only [List.append_assoc] using hp
    obtain ⟨m1, run1, ch1, vx1⟩ := iha ca ta heqa (by omega) m pc hp'.left
    have n1 := hp'.next ch1 (Nat.le_refl d) (by omega)
    obtain ⟨m2, run2, ch2, wx2⟩ := wideExtend_run (extSigned lo) x.n positive hka (wideFits_zahl x)
      n1.frame n1.small (by omega) n1.left.code n1.left.far vx1.2
    have n2 := n1.next ch2 (Nat.le_refl d) (by omega)
    obtain ⟨m3, run3, ch3, post⟩ := kernel m2 _ n2 (by omega) wx2
    refine ⟨m3, ?_, ch1.trans (ch2.trans ch3), post⟩
    simpa only [List.length_append, pc_add] using run1.trans (run2.trans run3)
  · cases h

end Gabbro.Stage0.Senke
