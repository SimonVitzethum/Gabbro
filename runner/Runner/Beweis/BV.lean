import Runner.X86.Step

/-! # `BitVec` facts the handler proofs use: flags of `cmp`, the low byte after `setcc`, `cqo` -/

namespace Runner.Beweis

theorem toInt64 (a : BitVec 64) :
    a.toInt = if 2 * a.toNat < 2 ^ 64 then (a.toNat : Int) else (a.toNat : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_cond]; rfl

/-- `setl` after `cmp a, b`: SF ≠ OF is the signed `<`. -/
theorem slt_flags (a b : BitVec 64) :
    ((a - b).msb != ((a.msb != b.msb) && ((a - b).msb != a.msb))) = a.slt b := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.slt_eq_decide, toInt64 a, toInt64 b]
  simp only [BitVec.msb_eq_decide, BitVec.toNat_sub, Nat.add_one_sub_one]
  by_cases h1 : 2 ^ 63 ≤ a.toNat <;> by_cases h2 : 2 ^ 63 ≤ b.toNat <;>
    by_cases h3 : 2 ^ 63 ≤ (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 <;>
    simp [h1, h2, h3] <;> omega

/-- `sete` after `cmp a, b`: ZF is equality. -/
theorem eq_flags (a b : BitVec 64) : (a - b == 0#64) = (a == b) := by
  have ha := a.isLt
  have hb := b.isLt
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ 0#64 := fun h' => h (by
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      omega)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

/-- `setcc` writes the low byte, `movzx` keeps only it. -/
theorem setcc_zx (a : BitVec 64) (t : Bool) :
    (((a &&& ~~~(BitVec.ofNat 64 255)) ||| (if t = true then 1#64 else 0#64)).setWidth 8).setWidth 64 =
      if t = true then 1#64 else 0#64 := by
  cases t <;> (apply BitVec.eq_of_toNat_eq; simp)

/-- `cqo` then the dividend of `idiv` is the signed value of `rax`. -/
theorem cqo_int (a : BitVec 64) :
    (if a.msb = true then BitVec.allOnes 64 else 0#64).toInt * 2 ^ 64 + (a.toNat : Int) = a.toInt := by
  rw [BitVec.toInt_eq_msb_cond a]
  cases h : a.msb <;> simp <;> omega

/-- `cqo` then the dividend of `idiv`, in the form `simp` leaves it. -/
theorem cqo_int' (a : BitVec 64) :
    (BitVec.toInt (if a.msb = true then 18446744073709551615#64 else 0#64) * 18446744073709551616 +
      (a.toNat : Int)) = a.toInt := cqo_int a

theorem zx_bool (t : Bool) :
    BitVec.setWidth 64 (BitVec.setWidth 8 (if t = true then 1#64 else 0#64)) = if t = true then 1#64 else 0#64 := by
  cases t <;> decide

theorem zx_prop (p : Prop) [Decidable p] :
    BitVec.setWidth 64 (BitVec.setWidth 8 (if p then 1#64 else 0#64)) = if p then 1#64 else 0#64 := by
  split <;> decide

end Runner.Beweis
