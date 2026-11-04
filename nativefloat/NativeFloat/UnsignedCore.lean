/- Shared native rounding states for the portable UInt64 conversion. -/
module
public import NativeFloat.NormalForm
public import NativeFloat.IntSticky
public import NativeFloat.RoundState
import all NativeFloat.NormalForm
import all NativeFloat.IntSticky
import all NativeFloat.RoundState
@[expose] public section

namespace RootNativeFloat.UnsignedCore
open Float.Model
open Float.Model.UnpackedFloat

private theorem shifted_round_bounds (F : Format) (m h : Nat) (positive : 0 < m)
    (log : m.log2 = h) (room : F.mantissaBitsWithoutImplicit + 3 ≤ h) :
    let j := h - F.mantissaBitsWithoutImplicit
    2 ^ F.mantissaBitsWithoutImplicit ≤ ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa ∧
      ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa ≤ 2 ^ (F.mantissaBitsWithoutImplicit + 1) := by
  dsimp only
  let j := h - F.mantissaBitsWithoutImplicit
  change 2 ^ F.mantissaBitsWithoutImplicit ≤ ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa ∧
    ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa ≤ 2 ^ (F.mantissaBitsWithoutImplicit + 1)
  have jpos : 0 < j := by dsimp [j]; omega
  have magnitude := (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mp log
  have bottom : 2 ^ h = 2 ^ F.mantissaBitsWithoutImplicit * 2 ^ j := by
    rw [← Nat.pow_add]
    congr 1
    dsimp [j]
    omega
  have top : 2 ^ (h + 1) = 2 ^ (F.mantissaBitsWithoutImplicit + 1) * 2 ^ j := by
    rw [← Nat.pow_add]
    congr 1
    dsimp [j]
    omega
  have qlower : 2 ^ F.mantissaBitsWithoutImplicit ≤ m / 2 ^ j :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [← bottom]; exact magnitude.1)
  have qupper : m / 2 ^ j < 2 ^ (F.mantissaBitsWithoutImplicit + 1) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by rw [← top]; exact magnitude.2)
  have mantissa : ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).mantissa = m / 2 ^ j := by
    change (Nat.repeat ExtendedMantissa.shiftRightOne j ⟨m, false, false⟩).mantissa = _
    have shifted := exact_shift_bits m (j - 1)
    have amount : (j - 1) + 1 = j := by omega
    rw [amount] at shifted
    exact congrArg ExtendedMantissa.mantissa shifted
  have rounded := rounded_bounds ((⟨m, false, false⟩ : ExtendedMantissa) >>> j)
  have below : m / 2 ^ j ≤ ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa := by
    rw [← mantissa]
    exact rounded.1
  have above : ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa ≤ m / 2 ^ j + 1 := by
    rw [← mantissa]
    exact rounded.2
  exact ⟨Nat.le_trans qlower below, Nat.le_trans above (Nat.succ_le_of_lt qupper)⟩

private theorem integer_form (F : Format) (m h : Nat) (positive : 0 < m) (log : m.log2 = h)
    (room : F.mantissaBitsWithoutImplicit + 3 ≤ h) (minimum : F.minExponent ≤ 0) :
    let j := h - F.mantissaBitsWithoutImplicit
    let r := ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa
    round F .positive m 0 = if r = 2 ^ (F.mantissaBitsWithoutImplicit + 1) then
      .finite .positive (2 ^ F.mantissaBitsWithoutImplicit) ((j : Int) + 1) (Nat.two_pow_pos _)
      else .finite .positive r j (by
        exact Nat.lt_of_lt_of_le (Nat.two_pow_pos F.mantissaBitsWithoutImplicit)
          (shifted_round_bounds F m h positive log room).1) := by
  dsimp only
  let j := h - F.mantissaBitsWithoutImplicit
  let r := ((⟨m, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa
  have bounds : 2 ^ F.mantissaBitsWithoutImplicit ≤ r ∧
      r ≤ 2 ^ (F.mantissaBitsWithoutImplicit + 1) := shifted_round_bounds F m h positive log room
  have rpositive : 0 < r := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) bounds.1
  change round F .positive m 0 = if r = 2 ^ (F.mantissaBitsWithoutImplicit + 1) then
    .finite .positive (2 ^ F.mantissaBitsWithoutImplicit) ((j : Int) + 1) (Nat.two_pow_pos _)
    else .finite .positive r j rpositive
  have target : F.targetExponent (totalExponent m 0) = (j : Int) := by
    simp only [Format.targetExponent, totalExponent, log, Format.mantissaBits,
      Int.natCast_add, Int.cast_ofNat_Int]
    dsimp [j]
    omega
  have first : shiftToTargetExponent F m 0 .exact =
      (((⟨m, false, false⟩ : ExtendedMantissa) >>> j), (j : Int)) := by
    unfold shiftToTargetExponent
    rw [target]
    unfold shiftToExponent
    dsimp only
    have amount : ((j : Int) - 0).toNat = j := by omega
    rw [amount]
    apply Prod.ext
    · rfl
    · change (0 : Int) + j = j
      omega
  have same : round F .positive m 0 = roundWithAccuracy F .positive m 0 .exact := by
    unfold round decreaseExponent
    rw [target]
    dsimp only
    have noDecrease : (0 - (j : Int)).toNat = 0 := by omega
    rw [noDecrease]
    rfl
  rw [same]
  unfold roundWithAccuracy
  rw [first]
  dsimp only
  have last := after_round_shift F _ j (by omega) bounds.1 bounds.2
  by_cases carry : r = 2 ^ (F.mantissaBitsWithoutImplicit + 1)
  · rw [if_pos carry] at last
    rw [last]
    dsimp only
    simp only [carry, Nat.ne_of_gt (Nat.two_pow_pos F.mantissaBitsWithoutImplicit),
      ↓reduceIte, ↓reduceDIte]
  · have nonzero : r ≠ 0 := Nat.ne_of_gt rpositive
    rw [if_neg carry] at last
    rw [last]
    dsimp only
    simp only [carry, nonzero, ↓reduceIte, ↓reduceDIte]

private theorem add_normal_twice (F : Format) (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2 ^ F.mantissaBitsWithoutImplicit ≤ m)
    (upper : m < 2 ^ (F.mantissaBitsWithoutImplicit + 1)) (minimum : F.minExponent ≤ e) :
    UnpackedFloat.add F (.finite .positive m e positive) (.finite .positive m e positive) =
      .finite .positive m (e + 1) positive := by
  have log : m.log2 = F.mantissaBitsWithoutImplicit :=
    (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mpr ⟨lower, upper⟩
  have doubledLog : (m + m).log2 = F.mantissaBitsWithoutImplicit + 1 := by
    have value := Nat.log2_two_mul (Nat.ne_of_gt positive)
    simpa only [log, show 2 * m = m + m by omega] using value
  have normalized : UnpackedFloat.add F (.finite .positive m e positive) (.finite .positive m e positive) =
      round F .positive (m + m) e := by
    have cp : compare ((m + m : Nat) : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
    simp only [UnpackedFloat.add, Int.min_self, decreaseExponent, Int.sub_self, Int.toNat_zero,
      Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero, Sign.apply]
    change normalize F ((m + m : Nat) : Int) e .positive = round F .positive (m + m) e
    unfold normalize
    rw [cp]
    rfl
  have target : F.targetExponent (totalExponent (m + m) e) = e + 1 := by
    simp only [Format.targetExponent, totalExponent, doubledLog, Format.mantissaBits,
      Int.natCast_add, Int.cast_ofNat_Int]
    omega
  have unchanged : F.targetExponent (totalExponent m (e + 1)) = e + 1 := by
    simp only [Format.targetExponent, totalExponent, log, Format.mantissaBits,
      Int.natCast_add, Int.cast_ofNat_Int]
    omega
  rw [normalized]
  unfold round decreaseExponent
  rw [target]
  dsimp only
  have noDecrease : (e - (e + 1)).toNat = 0 := by omega
  rw [noDecrease]
  simp only [Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero]
  have scaled := exact_scaled F .positive m 1 (e + 1) positive unchanged
  simp only [Nat.shiftLeft_eq, Nat.pow_one, Int.cast_ofNat_Int] at scaled
  have exponent : e + (1 : Int) - 1 = e := by omega
  rw [exponent] at scaled
  simpa only [show m * 2 = m + m by omega] using scaled

private theorem double_pack (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (n t : Nat) (npositive : 0 < n) (tpositive : 0 < t) (nlog : n.log2 = 63) (tlog : t.log2 = 62)
    (states : (⟨t, false, false⟩ : ExtendedMantissa) >>> (62 - F.mantissaBitsWithoutImplicit) =
      (⟨n, false, false⟩ : ExtendedMantissa) >>> ((62 - F.mantissaBitsWithoutImplicit) + 1)) :
    UnpackedFloat.pack F (round F .positive n 0) =
      UnpackedFloat.pack F (UnpackedFloat.add F
        (UnpackedFloat.unpack F (UnpackedFloat.pack F (round F .positive t 0)))
        (UnpackedFloat.unpack F (UnpackedFloat.pack F (round F .positive t 0)))) := by
  let p := F.mantissaBitsWithoutImplicit
  let j := 62 - p
  let r := ((⟨t, false, false⟩ : ExtendedMantissa) >>> j).roundedMantissa
  have pmax : p ≤ 59 := by rcases standard with rfl | rfl <;> decide
  have minimum : F.minExponent ≤ 0 := by rcases standard with rfl | rfl <;> decide
  have unpackMin : (1 : Int) - F.exponentBias - p ≤ 0 := by
    rcases standard with rfl | rfl <;> decide
  have unpackMax : (64 : Int) ≤ ((2 ^ F.exponentBits : Nat) : Int) - 2 - F.exponentBias - p := by
    rcases standard with rfl | rfl <;> decide
  have jmax : j + 2 ≤ 64 := by dsimp [j]; omega
  have fullShift : 63 - p = j + 1 := by dsimp [j]; omega
  have bounds : 2 ^ p ≤ r ∧ r ≤ 2 ^ (p + 1) :=
    shifted_round_bounds F t 62 tpositive tlog (by omega)
  have rpositive : 0 < r := Nat.lt_of_lt_of_le (Nat.two_pow_pos p) bounds.1
  let rn := ((⟨n, false, false⟩ : ExtendedMantissa) >>> (63 - p)).roundedMantissa
  have fullState : (⟨n, false, false⟩ : ExtendedMantissa) >>> (63 - p) =
      (⟨t, false, false⟩ : ExtendedMantissa) >>> j :=
    (congrArg (fun amount : Nat => (⟨n, false, false⟩ : ExtendedMantissa) >>> amount) fullShift).trans
      (show (⟨t, false, false⟩ : ExtendedMantissa) >>> j =
        (⟨n, false, false⟩ : ExtendedMantissa) >>> (j + 1) from states).symm
  have rounding : rn = r := congrArg ExtendedMantissa.roundedMantissa fullState
  have rnPositive : 0 < rn := by rw [rounding]; exact rpositive
  have exponent : ((63 - p : Nat) : Int) = (j : Int) + 1 := by
    simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
      congrArg (fun amount : Nat => (amount : Int)) fullShift
  have finiteEq {a b : Nat} {u v : Int} (ha : 0 < a) (hb : 0 < b)
      (magnitude : a = b) (exponent : u = v) :
      UnpackedFloat.finite .positive a u ha = .finite .positive b v hb := by
    cases magnitude
    cases exponent
    rfl
  have rawFull : round F .positive n 0 = if rn = 2 ^ (p + 1) then
      .finite .positive (2 ^ p) (((63 - p : Nat) : Int) + 1) (Nat.two_pow_pos _)
      else .finite .positive rn ((63 - p : Nat) : Int) rnPositive :=
    integer_form F n 63 npositive nlog (by omega) minimum
  have full : round F .positive n 0 = if r = 2 ^ (p + 1) then
      .finite .positive (2 ^ p) ((j : Int) + 1 + 1) (Nat.two_pow_pos _)
      else .finite .positive r ((j : Int) + 1) rpositive := by
    by_cases carry : r = 2 ^ (p + 1)
    · have rawCarry : rn = 2 ^ (p + 1) := rounding.trans carry
      rw [if_pos rawCarry] at rawFull
      rw [if_pos carry]
      exact rawFull.trans (finiteEq (Nat.two_pow_pos p) (Nat.two_pow_pos p) rfl
        (congrArg (fun e : Int => e + 1) exponent))
    · have rawCarry : rn ≠ 2 ^ (p + 1) := fun eq => carry (rounding.symm.trans eq)
      rw [if_neg rawCarry] at rawFull
      rw [if_neg carry]
      exact rawFull.trans (finiteEq rnPositive rpositive rounding exponent)
  have half : round F .positive t 0 = if r = 2 ^ (p + 1) then
    .finite .positive (2 ^ p) ((j : Int) + 1) (Nat.two_pow_pos _)
    else .finite .positive r (j : Int) rpositive :=
    integer_form F t 62 tpositive tlog (by omega) minimum
  rw [full, half]
  have span : 2 ^ p < 2 ^ (p + 1) := by
    rw [Nat.pow_succ]
    have := Nat.two_pow_pos p
    omega
  by_cases carry : r = 2 ^ (p + 1)
  · simp only [carry, ↓reduceIte]
    have decoded := normal_unpack F .positive (2 ^ p) ((j : Int) + 1) (Nat.two_pow_pos p)
      (Nat.le_refl _) span (by omega) (by omega)
    simp only [decoded]
    rw [add_normal_twice F (2 ^ p) ((j : Int) + 1) (Nat.two_pow_pos p)
      (Nat.le_refl _) span (by omega)]
  · simp only [carry, ↓reduceIte]
    have positive : 0 < r := rpositive
    have upper : r < 2 ^ (p + 1) := by omega
    have decoded := normal_unpack F .positive r (j : Int) positive bounds.1 upper (by omega) (by omega)
    simp only [decoded]
    rw [add_normal_twice F r (j : Int) positive bounds.1 upper (by omega)]

end RootNativeFloat.UnsignedCore
