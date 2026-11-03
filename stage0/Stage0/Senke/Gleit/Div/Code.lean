/- Reuse the checked restoring shift/subtract loop on a two-limb numerator. -/
module
public import Stage0.Senke.Gleit.Div.Quotient
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Bits
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- The prepared numerator occupies slots 0/1 relative to `d`; the divisor
    occupies slot 2. The shared loop returns quotient and rest, then one
    unsigned comparison adds the sticky bit. No new IR opcode is needed. -/
def softDivQuotientC (d : Nat) : List II :=
  [ci 1 (d + 3) 0 0] ++ wideDivC 2 d ++
    [ci 1 (d + 4) 0 0, ci 27 (d + 4) (d + 4) (d + 2), ci 9 d d (d + 4)]

theorem softDivQuotientC_aluIns {K d : Nat} (room : d + 26 ≤ K) :
    ∀ i ∈ softDivQuotientC d, AluIns K d i := by
  intro i member
  simp only [softDivQuotientC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | member | rfl | rfl | rfl
  · exact AluIns.const _ _ (by omega) (by omega) (by decide)
  · exact wideDivC_aluIns 2 d (by decide) (by omega) i member
  · exact AluIns.const _ _ (by omega) (by omega) (by decide)
  · exact AluIns.bin 27 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)
  · exact AluIns.bin 9 _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega)

/-- Nonnegative limbs agree with the word encodings used by float unpacking. -/
theorem softDiv_limb (n j : Nat) :
    lmb (n : Int) j = BitVec.ofNat 64 (n / 2 ^ (64 * j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [lmb_natCast_toNat, BitVec.toNat_ofNat]

/-- Mathematical value of the entire existing restoring loop and sticky
    suffix. The finite caller establishes both machine-width bounds. -/
theorem softDivQuotientC_value (d n b : Nat) (s : Nat → Runner.W)
    (bp : 0 < b) (bb : b < 2 ^ 64) (nb : n < 2 ^ 128)
    (low : s d = BitVec.ofNat 64 n)
    (high : s (d + 1) = BitVec.ofNat 64 (n / 2 ^ 64))
    (divisor : s (d + 2) = BitVec.ofNat 64 b) :
    aluRun (softDivQuotientC d) s d = BitVec.ofNat 64 (softDivJam n b) := by
  let initial := slotUpd s (d + 3) 0
  have numerator : ∀ j, j < 2 → initial (d + j) = lmb (n : Int) j := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
      simp [initial, slotUpd, softDiv_limb, low, high]
  have denominator : ∀ j, j < 2 → initial (d + 2 + j) = lmb (b : Int) j := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · simp [initial, slotUpd, softDiv_limb, divisor]
    · rw [lmb_high b 1 1 bb (Nat.le_refl _)]
      simp [initial, slotUpd]
  have result := wideDiv_value 2 d n b (by decide) bp (by omega) nb initial numerator denominator
  have quotient := result.1 0 (by decide)
  have rest := result.2 0 (by decide)
  simp only [Nat.add_zero, softDiv_limb, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at quotient rest
  let divided := aluRun (wideDivC 2 d) initial
  change divided d = _ at quotient
  change divided (d + 2) = _ at rest
  have tail : aluRun
      [ci 1 (d + 4) 0 0, ci 27 (d + 4) (d + 4) (d + 2), ci 9 d d (d + 4)] divided d =
      divided d ||| Runner.IR.bool ((0 : Runner.W).ult (divided (d + 2))) := by
    simp [aluRun_cons, aluRun_nil, aluStep, aluVal, aluFn, ci, slotUpd]
  have rb : n % b < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ bp) bb
  have test : (0 : Runner.W).ult (BitVec.ofNat 64 (n % b)) = decide (n % b ≠ 0) := by
    simp only [BitVec.ult, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt rb]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have run : aluRun (softDivQuotientC d) s d =
      aluRun [ci 1 (d + 4) 0 0, ci 27 (d + 4) (d + 4) (d + 2), ci 9 d d (d + 4)] divided d := by
    simp only [softDivQuotientC, aluRun_append, aluRun_cons, aluRun_nil, aluStep_const]
    rfl
  rw [run, tail, quotient, rest, test]
  unfold softDivJam
  rw [softDivQR_model n b bp nb]
  dsimp only
  by_cases zero : n % b = 0 <;>
    simp [zero, Runner.IR.bool, BitVec.ofNat_or]

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The actual instruction stream preserves the generic memory contract.
    All loop writes stay in the caller's temporary frame interval. -/
theorem softDivQuotientC_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {reserved : Nat}
    (hp : Pre L m pc fp K d (softDivQuotientC d) ρ W reserved)
    (room : d + 26 ≤ K) (n b : Nat) (bp : 0 < b) (bb : b < 2 ^ 64) (nb : n < 2 ^ 128)
    (low : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofNat 64 n))
    (high : m.rd64 (slot fp (BitVec.ofNat 64 (d + 1))) = some (BitVec.ofNat 64 (n / 2 ^ 64)))
    (divisor : m.rd64 (slot fp (BitVec.ofNat 64 (d + 2))) = some (BitVec.ofNat 64 b)) :
    Ok m pc fp K d (softDivQuotientC d) (· = BitVec.ofNat 64 (softDivJam n b)) := by
  have read : ∀ j, j < K → m.rd64 (slot fp (BitVec.ofNat 64 j)) = some (slotVal m fp j) :=
    fun j hj => slotVal_rd hp.frame hj
  have lo := Option.some.inj ((read d (by omega)).symm.trans low)
  have hi := Option.some.inj ((read (d + 1) (by omega)).symm.trans high)
  have den := Option.some.inj ((read (d + 2) (by omega)).symm.trans divisor)
  obtain ⟨m', steps, agree, output⟩ := alu_run hp.frame hp.small hp.code hp.far
    (softDivQuotientC_aluIns room) (slotVal m fp) read
  refine ⟨m', steps, agree, _, output d (by omega), ?_⟩
  exact softDivQuotientC_value d n b (slotVal m fp) bp bb nb lo hi den

#print axioms softDivQuotientC_value
#print axioms softDivQuotientC_ok
end Gabbro.Stage0.Senke
