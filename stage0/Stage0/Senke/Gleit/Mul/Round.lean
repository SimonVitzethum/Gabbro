/- Exponent dispatch for a normalized multiplication guard word. -/
module
public import Stage0.Senke.Gleit.Mul.Replay
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem

/-- `total` includes both normalized offset indices and the product shift.
    Subtracting 1200 gives the usual binary64 exponent index. All arithmetic
    stays unsigned until the source replay identifies its mathematical scale. -/
def softMulRoundWord (sign total magnitude : Runner.W) : Runner.W :=
  if total.ult 1201 then
    routineRoundPackWord sign 1 (floatShiftJamWord magnitude (1201 - total))
  else if total.ult 3247 then routineRoundPackWord sign (total - 1200) magnitude
  else packWord sign 2047 0

variable [Kern] {D : Deklaration} {L : Lay D}

def softMulRoundL (d : Nat) (sign total magnitude : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let c := fun (n : Int) (j : Nat) => some ([ci 1 j n 0], j + 1)
  let sub := fun j => routineRoundPackL j sign (c 1)
    (fun k => floatShiftJamL k magnitude (fun v => wordL 4 v (c 1201 v) (total (v + 1))))
  let normal := fun j => routineRoundPackL j sign (fun k => wordK 4 k (total k) 1200) magnitude
  let overflow := fun j => packL j sign (c 2047) (c 0)
  let finite := fun j => routineChooseL j (fun k => routineLessL k total (c 3247)) normal overflow
  routineChooseL d (fun j => routineLessL j total (c 1201)) sub finite

theorem softMulRoundL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {sign total magnitude : Nat → Option (List II × Nat)} {sv tv mv : Runner.W}
    (hs : WordCode (L := L) ρ W sign sv) (ht : WordCode (L := L) ρ W total tv)
    (hm : WordCode (L := L) ρ W magnitude mv) :
    WordCode (L := L) ρ W (fun d => softMulRoundL d sign total magnitude)
      (softMulRoundWord sv tv mv) := by
  have count : WordCode (L := L) ρ W _ _ := WordCode.bin (WordCode.const 1201 (by decide)) ht
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have jam : WordCode (L := L) ρ W _ _ := floatShiftJamL_ok hm count
  have sub : WordCode (L := L) ρ W _ _ := routineRoundPackL_ok hs (WordCode.const 1 (by decide)) jam
  have index : WordCode (L := L) ρ W _ _ := WordCode.bin ht (WordCode.const 1200 (by decide))
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have normal : WordCode (L := L) ρ W _ _ := routineRoundPackL_ok hs index hm
  have overflow : WordCode (L := L) ρ W _ _ :=
    packL_ok hs (WordCode.const 2047 (by decide)) (WordCode.const 0 (by decide))
  have finite : WordCode (L := L) ρ W _ _ :=
    routineChooseL_ok (routineLessL_ok ht (WordCode.const 3247 (by decide)))
      (fun _ => normal) (fun _ => overflow)
  have result : WordCode (L := L) ρ W _ _ :=
    routineChooseL_ok (routineLessL_ok ht (WordCode.const 1201 (by decide)))
      (fun _ => sub) (fun _ => finite)
  intro fp K d c top emitted fits m pc pre
  exact result (fp := fp) (K := K) (d := d) (c := c) (top := top) emitted fits m pc pre

/-- The shared rounding and packing continuation handles all three exponent
    ranges. Its exponent input is bounded independently of the word modulus. -/
theorem softMulRoundWord_model (s : Bool) (total n : Nat)
    (tb : total < 4400) (nl : 2 ^ 55 ≤ n) (nb : n < 2 ^ 56) :
    softMulRoundWord (Runner.IR.bool s) (BitVec.ofNat 64 total) (BitVec.ofNat 64 n) =
      BitVec.ofNat 64 (zuBits f64
        (rundeExakt f64 ⟨if s then -(n : Int) else n, (total : Int) - 2278⟩)) := by
  have t64 : total < 2 ^ 64 := by omega
  have n64 : n < 2 ^ 64 := by omega
  have positive : 0 < n := by omega
  have subTest : (BitVec.ofNat 64 total).ult 1201 = decide (total < 1201) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt t64]
    rfl
  have finiteTest : (BitVec.ofNat 64 total).ult 3247 = decide (total < 3247) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt t64]
    rfl
  unfold softMulRoundWord
  rw [subTest, finiteTest]
  by_cases sub : total < 1201
  · simp only [sub, decide_true, ite_true]
    have count : (1201 : Runner.W) - BitVec.ofNat 64 total = BitVec.ofNat 64 (1201 - total) :=
      BitVec.ofNat_sub_ofNat_of_le 1201 total t64 (by omega)
    rw [count]
    have k64 : 1201 - total < 2 ^ 64 := by omega
    have jam : floatShiftJamWord (BitVec.ofNat 64 n) (BitVec.ofNat 64 (1201 - total)) =
        BitVec.ofNat 64 (softShiftJamNat n (1201 - total)) := by
      have result := congrArg (BitVec.ofNat 64)
        (floatShiftJamWord_nat (BitVec.ofNat 64 n) (BitVec.ofNat 64 (1201 - total)))
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt n64, Nat.mod_eq_of_lt k64] using result
    rw [jam, softMulUnderflow_model s n (1201 - total) nl nb (by omega)]
    have scale : -1077 - ((1201 - total : Nat) : Int) = (total : Int) - 2278 := by omega
    rw [scale]
  · simp only [sub, decide_false, Bool.false_eq_true, ite_false]
    by_cases finite : total < 3247
    · simp only [finite, decide_true, ite_true]
      have index : BitVec.ofNat 64 total - 1200 = BitVec.ofNat 64 (total - 1200) :=
        BitVec.ofNat_sub_ofNat_of_le total 1200 (by decide) (by omega)
      rw [index, routineRoundPackWord_exact s (total - 1200) n
        (by omega) (by omega) (by omega) nb (Or.inl nl)]
      have scale : ((total - 1200 : Nat) : Int) - 1078 = (total : Int) - 2278 := by omega
      rw [scale]
    · simp only [finite, decide_false, Bool.false_eq_true, ite_false]
      have nonzero : (if s then -(n : Int) else (n : Int)) ≠ 0 := by
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      have mag : (if s then -(n : Int) else (n : Int)).natAbs = n := by cases s <;> simp
      have sign : decide ((if s then -(n : Int) else (n : Int)) < 0) = s := by
        cases s <;> simp [positive]
      have replay := softRound_replay_all (if s then -(n : Int) else n)
        ((total : Int) - 2278) nonzero
      dsimp only at replay
      rw [mag, sign, bitlen_unique n 56 nl nb positive] at replay
      have above : (f64.emax : Int) < (total : Int) - 2278 + (56 : Nat) - 1 := by
        change (1023 : Int) < _
        omega
      rw [if_pos above] at replay
      rw [replay]
      exact packWord_canonical ⟨s, 2047, 0⟩ (by
        change 2047 ≤ 2047 ∧ 0 < 2 ^ 52
        constructor <;> decide)

/-- Ordinary multiplication, gradual underflow and overflow all reach this
    one continuation with the same 56-bit guard representation. -/
theorem softMulRound_zeuge :
    softMulRoundWord 0 2223 (BitVec.ofNat 64 (2 ^ 55)) =
      BitVec.ofNat 64 4607182418800017408 ∧
    softMulRoundWord 0 1200 (BitVec.ofNat 64 (2 ^ 55)) =
      BitVec.ofNat 64 (2 ^ 51) ∧
    softMulRoundWord 1 1147 (BitVec.ofNat 64 (2 ^ 55)) =
      BitVec.ofNat 64 (2 ^ 63) ∧
    softMulRoundWord 0 3247 (BitVec.ofNat 64 (2 ^ 55)) =
      BitVec.ofNat 64 9218868437227405312 := by
  decide +kernel

#print axioms softMulRoundL_word
#print axioms softMulRoundWord_model
#print axioms softMulRound_zeuge
end Gabbro.Stage0.Senke
