/- Actual bounded dyadic normalization in integer runner instructions. -/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Schleifea
public import Stage0.Senke.Ausdruck.Arithmetik.Adaptiv
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- The corrected carry at a halved denominator preserves exact value and
    canonicality for every canonical input, including the old counterexample. -/
theorem floatNormalizeLoop_large_transfer (q r : Int) (k : Nat)
    (hr : 0 ≤ r ∧ r < 2^(k+1)) :
    let c : Int := if r < 2^k then 0 else 1
    (2*q+c)*2^k + (r-c*2^k) = q*2^(k+1)+r ∧
    0 ≤ r-c*2^k ∧ r-c*2^k < 2^k := by
  have hp : (0 : Int) < 2^k := Int.pow_pos (by decide)
  rw [pow_succ] at hr
  dsimp only
  split <;> constructor
  · rw [pow_succ]; ring
  · constructor <;> omega
  · rw [pow_succ]; ring
  · constructor <;> omega

/-- Skipping the threshold computation above the signed-word range loses
    no carry for any nonnegative signed-word remainder. -/
theorem floatNormalizeLoop_large_no_carry (r : Int) (k : Nat)
    (hr : r < 2^63) (hk : 63 ≤ k) : r < 2^k := by
  have hp : (2 : Int)^63 ≤ 2^k := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk)
  exact lt_of_lt_of_le hr hp

/-- The corrected quotient, including its carry, still fits a positive
    signed word under the existing target ceiling. No input restriction is added. -/
theorem floatNormalizeLoop_large_carry_word_bounds (q target c : Int)
    (hq : 0 ≤ q) (ha : q < target) (ht : target ≤ 2^60)
    (hc : 0 ≤ c ∧ c ≤ 1) :
    0 ≤ 2*q+c ∧ 2*q+c < 2^61 := by omega

#print axioms floatNormalizeLoop_large_carry_word_bounds

/-- Joint boundary witnesses for the corrected arithmetic, with a genuine
    carry at distance 62 and a retained tail before the next carry at 63. -/
theorem floatNormalizeLoop_large_transfer_zeuge :
    (1 : Int)*2^61 + 0 = 0*2^62+2^61 ∧
    (1 : Int)*2^62 + 0 = 0*2^63+2^62 ∧
    (0 : Int)*2^62 + 2^61 = 0*2^63+2^61 ∧
    (floatNormalizeStep 0 (2^60) (2^61) 8) = (1,0) := by
  decide +kernel

#print axioms floatNormalizeLoop_large_transfer
#print axioms floatNormalizeLoop_large_no_carry
#print axioms floatNormalizeLoop_large_transfer_zeuge

/-- The carry instructions use a signed comparison against a shifted one.
    Below 63 this computes precisely the mathematical carry, including 61/62.
    This statement concerns word operations, not an assumed arithmetic result. -/
theorem floatNormalizeLoop_carry_word (r : Int) (k : Nat)
    (hr : 0 ≤ r ∧ r < 2^63) (hk : k < 63) :
    let den : Runner.W := (BitVec.ofInt 64 1) <<<
      ((BitVec.ofNat 64 k).toNat % 64)
    (1 : Runner.W) - Runner.IR.bool ((BitVec.ofInt 64 r).slt den) =
      BitVec.ofInt 64 (if r < 2^k then 0 else 1) := by
  have hkn : (BitVec.ofNat 64 k).toNat % 64 = k := by
    simp only [BitVec.toNat_ofNat]
    omega
  have hd : (BitVec.ofInt 64 1) <<< k = BitVec.ofInt 64 ((2 : Int)^k) := by
    rw [show (2 : Int)^k = ((2^k : Nat) : Int) by simp,
      BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hp : (0 : Int) < 2^k := Int.pow_pos (by decide)
  have hu : (2 : Int)^k < 2^63 := by
    exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1 < 2) hk)
  dsimp only
  rw [hkn, hd, slt_in (by constructor <;> omega) (by constructor <;> omega)]
  by_cases h : r < 2^k <;> simp [h, Runner.IR.bool]

/-- The emitted multiply/subtract/add sequence implements the corrected exact
    transfer without signed overflow, for every canonical signed-word tail.
    The upper branch needs no materialized denominator. -/
theorem floatNormalizeLoop_large_word_transfer (q r target : Int) (k : Nat)
    (hq : 0 ≤ q) (ha : q < target) (ht : target ≤ 2^60)
    (hr : 0 ≤ r ∧ r < 2^63) (hc : r < 2^(k+1)) :
    let c : Int := if r < 2^k then 0 else 1
    let qw := (BitVec.ofInt 64 q * 2 : Runner.W) + BitVec.ofInt 64 c
    let rw := (BitVec.ofInt 64 r : Runner.W) -
      BitVec.ofInt 64 (2^k) * BitVec.ofInt 64 c
    qw = BitVec.ofInt 64 (2*q+c) ∧
    rw = BitVec.ofInt 64 (r-c*2^k) ∧
    0 ≤ 2*q+c ∧ 2*q+c < 2^61 ∧
    (2*q+c)*2^k+(r-c*2^k) = q*2^(k+1)+r ∧
    0 ≤ r-c*2^k ∧ r-c*2^k < 2^k ∧
    r-c*2^k < 2^63 ∧ (63 ≤ k → c = 0) := by
  dsimp only
  have cb : 0 ≤ (if r < 2^k then (0 : Int) else 1) ∧
      (if r < 2^k then (0 : Int) else 1) ≤ 1 := by split <;> omega
  have hb := floatNormalizeLoop_large_carry_word_bounds q target _ hq ha ht cb
  have he := floatNormalizeLoop_large_transfer q r k ⟨hr.1, hc⟩
  dsimp only at he
  refine ⟨?_, ?_, hb.1, hb.2, he.1, he.2.1, he.2.2, ?_, ?_⟩
  · rw [show (2 : Runner.W) = BitVec.ofInt 64 2 from rfl,
      ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
    congr 1
    ring
  · rw [← BitVec.ofInt_mul, BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg,
      ← BitVec.ofInt_add]
    congr 1
    ring
  · have hp : (0 : Int) ≤ 2^k := le_of_lt (Int.pow_pos (by decide))
    have hm := Int.mul_nonneg cb.1 hp
    omega
  · intro hk
    simp [floatNormalizeLoop_large_no_carry r k hr.2 hk]

#print axioms floatNormalizeLoop_carry_word
#print axioms floatNormalizeLoop_large_word_transfer

/-- Reducing the distance instead of doubling the exact tail is the same
    normalization step in a different denominator scale. This is the bridge
    needed at each large-branch iteration of the Runner simulation. -/
theorem floatNormalizeLoop_large_math_step (q r target : Int) (k : Nat)
    (ha : q < target) :
    let c : Int := if r < 2^k then 0 else 1
    floatNormalizeStep q r (2^(k+1)) target =
      (2*q+c, 2*(r-c*2^k)) := by
  have hb : (r < (2 : Int)^(k+1)-r) ↔ r < 2^k := by
    rw [pow_succ]
    omega
  simp only [floatNormalizeStep, floatNormalizeActive, ha, ↓reduceIte,
    floatNormalizeCarry, hb]
  split <;> rw [pow_succ] <;> congr 1 <;> ring

/-- Joint nonzero-tail premises at the original failing boundary. -/
theorem floatNormalizeLoop_word_transfer_zeuge :
    ((1 : Runner.W) - Runner.IR.bool
      ((BitVec.ofInt 64 (2^61)).slt ((BitVec.ofInt 64 1) <<< 61))) = 1 ∧
    floatNormalizeStep 0 (2^61) (2^62) 8 = (1,0) ∧
    (0 : Int) < 8 ∧ (8 : Int) ≤ 2^60 ∧
    (0 : Int) ≤ 2^61 ∧ (2 : Int)^61 < 2^63 ∧ (2 : Int)^61 < 2^62 := by
  decide +kernel

#print axioms floatNormalizeLoop_large_math_step
#print axioms floatNormalizeLoop_word_transfer_zeuge

/-- Positive budget entry is one actual Runner instruction, fetched from
    the emitted code; it preserves the whole memory and advances by 16 bytes. -/
theorem floatNormalizeLoopL_positive_entry [Kern] {D : Deklaration} {L : Lay D}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base top reserved : Nat}
    {code : List II} {fuel : Runner.W}
    (hc : floatNormalizeLoopL base = some (code, top))
    (h : Pre L m pc fp K base code ρ W reserved)
    (hb : base+4 < K)
    (hz : m.rd64 (slot fp (BitVec.ofNat 64 (base+4))) = some fuel)
    (hf : fuel ≠ 0) :
    Run (Runner.IR.step ⟨pc, fp⟩) m ⟨pc+16, fp⟩ m := by
  have he := floatNormalizeLoopL_head base hc
  have hn : 0 < code.length := by
    apply Classical.byContradiction
    intro hh
    have hn : code[0]? = none := List.getElem?_eq_none (by omega)
    rw [hn] at he
    cases he
  have hi := h.code 0 hn
  have entry : code[0] = ci 19 (base+4) (16*code.length) 0 := by
    simpa only [List.getElem?_eq_getElem hn, Option.some.injEq] using he
  rw [entry] at hi
  simp only [ci, Nat.mul_zero, BitVec.add_zero] at hi
  have hs : sx (II.f ((base : Int)+4)) = BitVec.ofNat 64 (base+4) := by
    simpa using (sx_nat (d := base+4) (by have := h.small; omega))
  exact run_step hi (by decide)
    (run_brz_ne hi (by rw [hs]; exact hz) hf)

#print axioms floatNormalizeLoopL_positive_entry

end Gabbro.Stage0.Senke
