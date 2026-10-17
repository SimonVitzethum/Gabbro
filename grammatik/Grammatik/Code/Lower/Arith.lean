/-
  File:      Grammatik/Code/Lower/Arith.lean
  Subject:   TRACK L, PHASE L1 -- THE ARITHMETIC OF INTEGER WIDTHS: why a `u32 in 0 .. 200` may
             live in an `i8`, why `a + b` computed modulo `2^w` is the exact sum, and how a value
             moves between widths. Pure `Int`/`BitVec` facts; nothing here knows the IR.

  THE CORRESPONDENCE ASSUMPTION ABOUT WIDTHS, as a definition and not an axiom:
    `Fits lo hi w`  -- every integer in `lo .. hi` is representable in `w` bits, as an unsigned
                       number if `lo ≥ 0`, as a two's complement number otherwise.
    `wid lo hi`     -- the width the lowering gives a value of that range: the first of
                       8, 16, 32, 64, 128 that fits (a range beyond 128 bits has no lowering;
                       the theorems carry `Fits lo hi 128` for every range they meet).
    `dec lo w v`    -- the integer a bit pattern denotes under that discipline, and
                       `dec_ofInt` -- decoding the encoding of an in-range integer gives it back.

  The operation lemmas say that the machine operation on the encodings is the encoding of the
  exact result, PROVIDED the exact result fits the width the operation is carried out in:
  `add_ofInt`, `sub_ofInt`, `mul_ofInt`, `neg_ofInt`; the width changes `zext_ofInt`,
  `sext_ofInt`, `trunc_ofInt`; the comparisons `ult_ofInt`, `ule_ofInt`, `slt_ofInt`,
  `sle_ofInt`, `eq_ofInt`; and division `udiv_ofInt`, `urem_ofInt`.
-/

namespace Gabbro.Code.Ar

/-- Every integer of `lo .. hi` is representable in `w` bits. -/
def Fits (lo hi : Int) (w : Nat) : Prop :=
  if 0 ≤ lo then hi < 2 ^ w else (-(2 ^ (w - 1)) ≤ lo ∧ hi < 2 ^ (w - 1))

instance (lo hi : Int) (w : Nat) : Decidable (Fits lo hi w) := by
  unfold Fits; infer_instance

/-- The width of a value of range `lo .. hi`. -/
def wid (lo hi : Int) : Nat :=
  if Fits lo hi 8 then 8 else if Fits lo hi 16 then 16 else if Fits lo hi 32 then 32
  else if Fits lo hi 64 then 64 else 128

theorem wid_fits {lo hi : Int} (h : Fits lo hi 128) : Fits lo hi (wid lo hi) := by
  unfold wid
  split <;> try assumption
  split <;> try assumption
  split <;> try assumption
  split <;> try assumption

theorem wid_pos (lo hi : Int) : 8 ≤ wid lo hi := by
  unfold wid
  by_cases h8 : Fits lo hi 8 <;> by_cases h16 : Fits lo hi 16 <;> by_cases h32 : Fits lo hi 32 <;>
    by_cases h64 : Fits lo hi 64 <;> simp [h8, h16, h32, h64]

/-- The integer a bit pattern denotes: unsigned for a non-negative range, signed otherwise. -/
def dec (lo : Int) (w : Nat) (v : BitVec w) : Int :=
  if 0 ≤ lo then (v.toNat : Int) else v.toInt

theorem toNat_ofInt_lt {w : Nat} {n : Int} (h0 : 0 ≤ n) (h1 : n < 2 ^ w) :
    (BitVec.ofInt w n).toNat = n.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by exact_mod_cast h1)]

theorem dec_ofInt {lo hi : Int} {w : Nat} {n : Int} (hf : Fits lo hi w) (hw : 0 < w)
    (h1 : lo ≤ n) (h2 : n ≤ hi) : dec lo w (BitVec.ofInt w n) = n := by
  unfold Fits at hf
  unfold dec
  by_cases hl : 0 ≤ lo
  · rw [if_pos hl] at hf ⊢
    rw [toNat_ofInt_lt (by omega) (by omega)]
    omega
  · rw [if_neg hl] at hf ⊢
    exact BitVec.toInt_ofInt_eq_self hw (by omega) (by omega)

/-- Two encodings are equal exactly when the integers are, if both fit. -/
theorem ofInt_inj {lo hi : Int} {w : Nat} {a b : Int} (hf : Fits lo hi w) (hw : 0 < w)
    (ha1 : lo ≤ a) (ha2 : a ≤ hi) (hb1 : lo ≤ b) (hb2 : b ≤ hi) :
    BitVec.ofInt w a = BitVec.ofInt w b ↔ a = b := by
  constructor
  · intro h
    have := congrArg (dec lo w) h
    rwa [dec_ofInt hf hw ha1 ha2, dec_ofInt hf hw hb1 hb2] at this
  · intro h; rw [h]

/-! ## Exact operations -/

theorem add_ofInt {w : Nat} (a b : Int) :
    BitVec.ofInt w a + BitVec.ofInt w b = BitVec.ofInt w (a + b) := (BitVec.ofInt_add a b).symm

theorem mul_ofInt {w : Nat} (a b : Int) :
    BitVec.ofInt w a * BitVec.ofInt w b = BitVec.ofInt w (a * b) := (BitVec.ofInt_mul a b).symm

theorem neg_ofInt {w : Nat} (a : Int) : -BitVec.ofInt w a = BitVec.ofInt w (-a) :=
  BitVec.ofInt_neg.symm

theorem sub_ofInt {w : Nat} (a b : Int) :
    BitVec.ofInt w a - BitVec.ofInt w b = BitVec.ofInt w (a - b) := by
  rw [BitVec.sub_eq_add_neg, neg_ofInt, add_ofInt, Int.sub_eq_add_neg]

/-! ## Changing width -/

theorem two_pow_le {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  exact_mod_cast Nat.pow_le_pow_right (by decide) h

theorem pow_cast (w : Nat) : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by
  simp [Int.natCast_pow]

theorem zext_ofInt {w1 w2 : Nat} {n : Int} (hw : w1 ≤ w2) (h0 : 0 ≤ n) (h1 : n < 2 ^ w1) :
    (BitVec.ofInt w1 n).setWidth w2 = BitVec.ofInt w2 n := by
  apply BitVec.eq_of_toNat_eq
  have h2 : n < 2 ^ w2 := Int.lt_of_lt_of_le h1 (two_pow_le hw)
  rw [BitVec.toNat_setWidth, toNat_ofInt_lt h0 h1, toNat_ofInt_lt h0 h2]
  apply Nat.mod_eq_of_lt
  have h3 : n < ((2 ^ w2 : Nat) : Int) := by rw [pow_cast]; exact h2
  omega

theorem sext_ofInt {w1 w2 : Nat} {n : Int} (hw : w1 ≤ w2) (hp : 0 < w1)
    (h0 : -(2 ^ (w1 - 1)) ≤ n) (h1 : n < 2 ^ (w1 - 1)) :
    (BitVec.ofInt w1 n).signExtend w2 = BitVec.ofInt w2 n := by
  rw [← BitVec.toInt_inj, BitVec.toInt_signExtend_of_le hw,
    BitVec.toInt_ofInt_eq_self hp h0 h1,
    BitVec.toInt_ofInt_eq_self (by omega) (by have := two_pow_le (show w1 - 1 ≤ w2 - 1 by omega); omega)
      (by have := two_pow_le (show w1 - 1 ≤ w2 - 1 by omega); omega)]

theorem trunc_ofInt {w1 w2 : Nat} (n : Int) (hw : w2 ≤ w1) :
    (BitVec.ofInt w1 n).setWidth w2 = BitVec.ofInt w2 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have hd : ((2 ^ w2 : Nat) : Int) ∣ ((2 ^ w1 : Nat) : Int) := by
    exact_mod_cast Nat.pow_dvd_pow 2 hw
  have e := Int.emod_emod_of_dvd n hd
  have p1 : ((2 ^ w1 : Nat) : Int) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos w1)
  have p2 : ((2 ^ w2 : Nat) : Int) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos w2)
  have h0 : 0 ≤ n % ((2 ^ w1 : Nat) : Int) := Int.emod_nonneg _ p1
  have hy : 0 ≤ n % ((2 ^ w2 : Nat) : Int) := Int.emod_nonneg _ p2
  apply Int.ofNat.inj
  have hx : ((n % ((2 ^ w1 : Nat) : Int)).toNat : Int) = n % ((2 ^ w1 : Nat) : Int) := Int.toNat_of_nonneg h0
  show (((n % ((2 ^ w1 : Nat) : Int)).toNat % 2 ^ w2 : Nat) : Int) = (((n % ((2 ^ w2 : Nat) : Int)).toNat : Nat) : Int)
  rw [Int.natCast_emod, hx, Int.toNat_of_nonneg hy, e]

/-! ## Comparison -/

theorem ult_ofInt {w : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ w) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ w) : (BitVec.ofInt w a).ult (BitVec.ofInt w b) = decide (a < b) := by
  rw [BitVec.ult_eq_decide, toNat_ofInt_lt ha0 ha1, toNat_ofInt_lt hb0 hb1]
  simp only [decide_eq_decide]
  omega

theorem ule_ofInt {w : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ w) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ w) : (BitVec.ofInt w a).ule (BitVec.ofInt w b) = decide (a ≤ b) := by
  have : (BitVec.ofInt w a).ule (BitVec.ofInt w b) = decide ((BitVec.ofInt w a).toNat ≤ (BitVec.ofInt w b).toNat) := rfl
  rw [this, toNat_ofInt_lt ha0 ha1, toNat_ofInt_lt hb0 hb1]
  simp only [decide_eq_decide]
  omega

theorem slt_ofInt {w : Nat} (hw : 0 < w) {a b : Int} (ha0 : -(2 ^ (w - 1)) ≤ a)
    (ha1 : a < 2 ^ (w - 1)) (hb0 : -(2 ^ (w - 1)) ≤ b) (hb1 : b < 2 ^ (w - 1)) :
    (BitVec.ofInt w a).slt (BitVec.ofInt w b) = decide (a < b) := by
  have : (BitVec.ofInt w a).slt (BitVec.ofInt w b) = decide ((BitVec.ofInt w a).toInt < (BitVec.ofInt w b).toInt) := rfl
  rw [this, BitVec.toInt_ofInt_eq_self hw ha0 ha1, BitVec.toInt_ofInt_eq_self hw hb0 hb1]

theorem sle_ofInt {w : Nat} (hw : 0 < w) {a b : Int} (ha0 : -(2 ^ (w - 1)) ≤ a)
    (ha1 : a < 2 ^ (w - 1)) (hb0 : -(2 ^ (w - 1)) ≤ b) (hb1 : b < 2 ^ (w - 1)) :
    (BitVec.ofInt w a).sle (BitVec.ofInt w b) = decide (a ≤ b) := by
  have : (BitVec.ofInt w a).sle (BitVec.ofInt w b) = decide ((BitVec.ofInt w a).toInt ≤ (BitVec.ofInt w b).toInt) := rfl
  rw [this, BitVec.toInt_ofInt_eq_self hw ha0 ha1, BitVec.toInt_ofInt_eq_self hw hb0 hb1]

/-! ## Division of non-negative numbers -/

theorem udiv_ofInt {w : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ w) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ w) : BitVec.ofInt w a / BitVec.ofInt w b = BitVec.ofInt w (a / b) := by
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨b', rfl⟩ := Int.eq_ofNat_of_zero_le hb0
  have ha : a' < 2 ^ w := by exact_mod_cast ha1
  have hb : b' < 2 ^ w := by exact_mod_cast hb1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, ← Int.natCast_ediv]
  simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem urem_ofInt {w : Nat} {a b : Int} (ha0 : 0 ≤ a) (ha1 : a < 2 ^ w) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ w) : BitVec.ofInt w a % BitVec.ofInt w b = BitVec.ofInt w (a % b) := by
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨b', rfl⟩ := Int.eq_ofNat_of_zero_le hb0
  have ha : a' < 2 ^ w := by exact_mod_cast ha1
  have hb : b' < 2 ^ w := by exact_mod_cast hb1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, ← Int.natCast_emod]
  simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rcases Nat.eq_zero_or_pos b' with h | h
  · subst h; simp [Nat.mod_eq_of_lt ha]
  · rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ h) hb)]

end Gabbro.Code.Ar
