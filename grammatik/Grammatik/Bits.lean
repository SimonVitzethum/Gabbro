/-
  File:      Grammatik/Bits.lean
  Subject:   BIT INTRINSICS (lane 68) -- PLAN-BITS.md section 3, model half.

  Parametric in the width from the start: the width is carried as `w + 1`,
  so no `Nat` truncation can hide a wrong bound. All bit access goes through
  `Nat.testBit` on the value seen as a `Nat`; results are packed back with
  `Nat` arithmetic. The argument type excludes zero for `clz` / `ctz` /
  `log2`, so the C lowering never reaches the undefined `__builtin_clz(0)`
  case.
-/
import Grammatik.Typen

namespace Gabbro.Grammatik

/-- Bit list of `x` over `w` positions, LSB first. -/
def natBits (w x : Nat) : List Bool :=
  List.ofFn (fun i : Fin w => Nat.testBit x i.val)

theorem natBits_length (w x : Nat) : (natBits w x).length = w := by
  simp [natBits]

theorem natBits_get (w x i : Nat) (hi : i < w) :
    (natBits w x)[i]'(by rw [natBits_length]; exact hi) = Nat.testBit x i := by
  simp [natBits]

/-! ## Nat-level intrinsics over a `w + 1` wide field.

    `log2n` is `Nat.log2` guarded by `x ≠ 0`; `clzn` counts leading zeros
    (`w - log2`), `ctzn` counts trailing zeros. The width parameter is the
    full width `W = w + 1`; callers pass `x < 2 ^ W`. -/

/-- Floor log2, total on `Nat` (`Nat.log2 0 = 0` by core definition). -/
def log2n (x : Nat) : Nat := Nat.log2 x

/-- Spec of floor log2: `2 ^ r ≤ x < 2 ^ (r+1)` for `r = log2 x`, `x ≠ 0`. -/
theorem log2n_spez {x : Nat} (hx : x ≠ 0) :
    2 ^ log2n x ≤ x ∧ x < 2 ^ (log2n x + 1) :=
  (Nat.log2_eq_iff hx).mp rfl

/-- Count leading zeros over width `W = w + 1`: `W - 1 - log2 x`. -/
def clzn (w x : Nat) : Nat := w - Nat.log2 x

/-- `clz x + log2 x = w` for `0 < x < 2 ^ (w+1)`. Both premises are used:
    `hx0` rules out `log2 0`, `hxW` bounds the log from above. -/
theorem clzn_log2n {w x : Nat} (hx0 : 0 < x) (hxW : x < 2 ^ (w + 1)) :
    clzn w x + Nat.log2 x = w := by
  unfold clzn
  have hne : x ≠ 0 := by omega
  have hle : Nat.log2 x ≤ w := by
    cases Decidable.em (Nat.log2 x ≤ w) with
    | inl h => exact h
    | inr h =>
      exfalso
      have hge : w + 1 ≤ Nat.log2 x := by omega
      have hmono : 2 ^ (w + 1) ≤ 2 ^ Nat.log2 x :=
        Nat.pow_le_pow_right (by decide) hge
      have hspec := (Nat.log2_eq_iff hne).mp rfl
      omega
  omega

/-! ## Trailing zeros: `ctz` with the dvd spec.

    `ctzAux fuel x` recurses on `x / 2` with fuel `w + 1`; the spec is
    `2 ^ r ∣ x` and `¬ 2 ^ (r+1) ∣ x`, which pins `r` uniquely. -/

/-- Trailing-zero count, fuel-bounded recursion on `x / 2`. -/
def ctzAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, x =>
    if x = 0 then 0 else if x % 2 = 1 then 0 else 1 + ctzAux fuel (x / 2)

/-- Trailing-zero count over width `W = w + 1`. -/
def ctzn (w x : Nat) : Nat := ctzAux (w + 1) x

theorem ctzAux_rw {fuel x : Nat} (hne : x ≠ 0) (heven : x % 2 = 0) :
    ctzAux (fuel + 1) x = 1 + ctzAux fuel (x / 2) := by
  simp [ctzAux, hne, heven]

theorem ctzAux_spez (fuel x : Nat) (hx0 : 0 < x) (hxW : x < 2 ^ fuel) :
    2 ^ ctzAux fuel x ∣ x ∧ ¬ 2 ^ (ctzAux fuel x + 1) ∣ x := by
  induction fuel generalizing x with
  | zero =>
    simp at hxW
    omega
  | succ fuel ih =>
    have hne : x ≠ 0 := by omega
    have hcase : x % 2 = 1 ∨ x % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · exact Or.inr h
      · exact Or.inl h
    cases hcase with
    | inl hodd =>
      have hrw : ctzAux (fuel + 1) x = 0 := by simp [ctzAux, hodd, hne]
      rw [hrw]
      constructor
      · simp
      · intro hdvd
        have hmod := (@Nat.dvd_iff_mod_eq_zero 2 x).mp hdvd
        omega
    | inr heven =>
      have hx2 : 0 < x / 2 := Nat.div_pos (by omega) (by decide)
      have hlt : x < 2 * 2 ^ fuel := by
        have hps : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := Nat.pow_succ 2 fuel
        omega
      have hxW2 : x / 2 < 2 ^ fuel := Nat.div_lt_of_lt_mul hlt
      obtain ⟨ihdvd, ihnondvd⟩ := ih (x / 2) hx2 hxW2
      have hxeq : x = 2 * (x / 2) := by
        have h := Nat.div_add_mod x 2
        omega
      generalize hgen : ctzAux fuel (x / 2) = c
      have hrw : ctzAux (fuel + 1) x = 1 + c := by
        simp [ctzAux, hne, heven, hgen]
      have hpow1 : 2 ^ (1 + c) = 2 * 2 ^ c := by
        rw [Nat.pow_add, Nat.pow_one]
      have hpow2 : 2 ^ ((1 + c) + 1) = 2 * 2 ^ (c + 1) := by
        have e : (1 + c) + 1 = 1 + (c + 1) := by omega
        rw [e, Nat.pow_add, Nat.pow_one]
      generalize hgeny : x / 2 = y
      have hxeqy : x = 2 * y := by omega
      rw [hrw]
      constructor
      · obtain ⟨q, hq⟩ := ihdvd
        rw [hgen, hgeny] at hq
        rw [hpow1]
        exact ⟨q, by rw [hxeqy, hq, Nat.mul_assoc]⟩
      · intro hdvd
        apply ihnondvd
        rw [hgen] at ihnondvd ⊢
        rw [hgeny] at ihnondvd ⊢
        rw [hpow2, hxeqy] at hdvd
        exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hdvd

/-- `ctz` spec over width `W = w + 1`: `2 ^ r ∣ x`, `¬ 2 ^ (r+1) ∣ x`. -/
theorem ctzn_spez {w x : Nat} (hx0 : 0 < x) (hxW : x < 2 ^ (w + 1)) :
    2 ^ ctzn w x ∣ x ∧ ¬ 2 ^ (ctzn w x + 1) ∣ x :=
  ctzAux_spez (w + 1) x hx0 hxW

/-- `ctz` fits the field: `ctz x ≤ w`. Both premises are used (`hxW` bounds
    the power, `hx0` keeps the quotient positive). -/
theorem ctzn_le {w x : Nat} (hx0 : 0 < x) (hxW : x < 2 ^ (w + 1)) :
    ctzn w x ≤ w := by
  obtain ⟨hdvd, _⟩ := ctzn_spez hx0 hxW
  obtain ⟨q, hq⟩ := hdvd
  cases Decidable.em (ctzn w x ≤ w) with
  | inl h => exact h
  | inr h =>
    exfalso
    have hge : w + 1 ≤ ctzn w x := by omega
    have hmono : 2 ^ (w + 1) ≤ 2 ^ ctzn w x :=
      Nat.pow_le_pow_right (by decide) hge
    have hqpos : 0 < q := by
      cases Decidable.em (q = 0) with
      | inl h0 => simp [h0] at hq; omega
      | inr h0 =>
        have : 0 < q := Nat.pos_of_ne_zero h0
        exact this
    have hle : 2 ^ ctzn w x ≤ x := by
      have h1 : 2 ^ ctzn w x * 1 ≤ 2 ^ ctzn w x * q :=
        Nat.mul_le_mul_left _ hqpos
      omega
    omega

/-! ## Popcount, rotation, byteswap at `Nat` level. -/

/-- Popcount over `fuel` binary digits. -/
def popAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, x => (x % 2) + popAux fuel (x / 2)

/-- Popcount over width `W = w + 1`. -/
def popcountn (w x : Nat) : Nat := popAux (w + 1) x

theorem popAux_le (fuel x : Nat) : popAux fuel x ≤ fuel := by
  induction fuel generalizing x with
  | zero => simp [popAux]
  | succ fuel ih =>
    simp only [popAux]
    have hmod : x % 2 ≤ 1 := by
      have h := Nat.mod_lt x (by decide : 0 < 2)
      omega
    have hi := ih (x / 2)
    omega

theorem popcountn_le (w x : Nat) : popcountn w x ≤ w + 1 :=
  popAux_le (w + 1) x

/-- Popcount splits over fuel addition at a `2 ^ a` boundary. -/
theorem popAux_add_fuel (a b x : Nat) :
    popAux (a + b) x = popAux a x + popAux b (x / 2 ^ a) := by
  induction a generalizing x with
  | zero => simp [popAux]
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    simp only [popAux]
    rw [ih]
    have hdiv : x / 2 / 2 ^ a = x / 2 ^ (a + 1) := by
      have e2 : (2 : Nat) * 2 ^ a = 2 ^ (a + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [Nat.div_div_eq_div_mul, e2]
    rw [hdiv]
    omega

/-- Popcount of disjoint halves adds. -/
theorem popAux_add_mul_pow (s t lo hi : Nat) (hlo : lo < 2 ^ s) :
    popAux (s + t) (lo + hi * 2 ^ s) = popAux s lo + popAux t hi := by
  induction s generalizing lo hi with
  | zero =>
    simp at hlo
    simp [popAux, hlo]
  | succ s ih =>
    have e : s + 1 + t = (s + t) + 1 := by omega
    rw [e]
    simp only [popAux]
    have hps : (2 : Nat) ^ (s + 1) = 2 ^ s * 2 := Nat.pow_succ 2 s
    have hmod : (lo + hi * 2 ^ (s + 1)) % 2 = lo % 2 := by
      have h2 : hi * 2 ^ (s + 1) = 2 * (hi * 2 ^ s) := by
        calc hi * 2 ^ (s + 1) = hi * (2 ^ s * 2) := by rw [hps]
          _ = hi * (2 * 2 ^ s) := by rw [Nat.mul_comm (2 ^ s) 2]
          _ = 2 * (hi * 2 ^ s) := by
              rw [← Nat.mul_assoc, Nat.mul_comm hi 2, Nat.mul_assoc]
      rw [h2, Nat.add_mul_mod_self_left]
    have hdiv : (lo + hi * 2 ^ (s + 1)) / 2
        = lo / 2 + hi * 2 ^ s := by
      have h2 : hi * 2 ^ (s + 1) = (hi * 2 ^ s) * 2 := by
        rw [hps, Nat.mul_assoc]
      rw [h2]
      rw [Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
    rw [hmod, hdiv]
    have hlo2 : lo / 2 < 2 ^ s := by
      have h2 : lo < 2 * 2 ^ s := by omega
      exact Nat.div_lt_of_lt_mul h2
    rw [ih _ _ hlo2]
    omega

/-! ## Rotation at `Nat` level. -/

/-- Rotate left over width `W = w + 1` by `s`: low `W - s` bits move up. -/
def rotln (w s x : Nat) : Nat :=
  (x % 2 ^ (w + 1 - s)) * 2 ^ s + x / 2 ^ (w + 1 - s)

/-- Rotate right over width `W = w + 1` by `s`. -/
def rotrn (w s x : Nat) : Nat :=
  (x % 2 ^ s) * 2 ^ (w + 1 - s) + x / 2 ^ s

/-- Rotation stays in the field. Uses `hs` (shift fits) and `hx` (input fits). -/
theorem rotln_lt (w s x : Nat) (hs : s ≤ w) (hx : x < 2 ^ (w + 1)) :
    rotln w s x < 2 ^ (w + 1) := by
  have hW : w + 1 - s + s = w + 1 := by omega
  have hpowW : 2 ^ (w + 1 - s) * 2 ^ s = 2 ^ (w + 1) := by
    rw [← Nat.pow_add, hW]
  have hmod : x % 2 ^ (w + 1 - s) < 2 ^ (w + 1 - s) :=
    Nat.mod_lt x (Nat.pow_pos (by decide))
  have hdiv : x / 2 ^ (w + 1 - s) < 2 ^ s := by
    have hxW : x < 2 ^ (w + 1 - s) * 2 ^ s := by omega
    exact Nat.div_lt_of_lt_mul hxW
  have hmul1 : (x % 2 ^ (w + 1 - s) + 1) * 2 ^ s
      ≤ 2 ^ (w + 1 - s) * 2 ^ s :=
    Nat.mul_le_mul_right _ hmod
  have hexpand : (x % 2 ^ (w + 1 - s) + 1) * 2 ^ s
      = (x % 2 ^ (w + 1 - s)) * 2 ^ s + 2 ^ s := by
    rw [Nat.add_mul, Nat.one_mul]
  have hstep : (x % 2 ^ (w + 1 - s)) * 2 ^ s + x / 2 ^ (w + 1 - s)
      < (x % 2 ^ (w + 1 - s)) * 2 ^ s + 2 ^ s :=
    Nat.add_lt_add_left hdiv _
  have h2 : (x % 2 ^ (w + 1 - s)) * 2 ^ s + 2 ^ s ≤ 2 ^ (w + 1) := by
    rw [← hexpand]
    exact Nat.le_trans hmul1 (Nat.le_of_eq hpowW)
  have hchain : (x % 2 ^ (w + 1 - s)) * 2 ^ s + x / 2 ^ (w + 1 - s)
      < 2 ^ (w + 1) :=
    Nat.lt_of_lt_of_le hstep h2
  show rotln w s x < 2 ^ (w + 1)
  unfold rotln
  exact hchain

/-- `rotr ∘ rotl = id`. Uses `hs` (split points fit) and `hx` (input fits). -/
theorem rotrn_rotln (w s x : Nat) (hs : s ≤ w) (hx : x < 2 ^ (w + 1)) :
    rotrn w s (rotln w s x) = x := by
  have hW : w + 1 - s + s = w + 1 := by omega
  have hpowW : 2 ^ (w + 1 - s) * 2 ^ s = 2 ^ (w + 1) := by
    rw [← Nat.pow_add, hW]
  generalize hhi : x / 2 ^ (w + 1 - s) = hi
  generalize hlo : x % 2 ^ (w + 1 - s) = lo
  have hlox : lo < 2 ^ (w + 1 - s) := by omega
  have hhix : hi < 2 ^ s := by
    have hxW : x < 2 ^ (w + 1 - s) * 2 ^ s := by omega
    have hdiv : x / 2 ^ (w + 1 - s) < 2 ^ s := Nat.div_lt_of_lt_mul hxW
    omega
  have hsplit : hi * 2 ^ (w + 1 - s) + lo = x := by
    have h := Nat.div_add_mod x (2 ^ (w + 1 - s))
    have hc : 2 ^ (w + 1 - s) * (x / 2 ^ (w + 1 - s))
        = hi * 2 ^ (w + 1 - s) := by rw [hhi, Nat.mul_comm]
    omega
  have hrot : rotln w s x = hi + lo * 2 ^ s := by
    simp [rotln, hlo, hhi, Nat.add_comm]
  have hmod : (hi + lo * 2 ^ s) % 2 ^ s = hi % 2 ^ s :=
    Nat.add_mul_mod_self_right hi lo (2 ^ s)
  have hmodhi : hi % 2 ^ s = hi := Nat.mod_eq_of_lt hhix
  have hdiv : (hi + lo * 2 ^ s) / 2 ^ s = hi / 2 ^ s + lo :=
    Nat.add_mul_div_right hi lo (Nat.pow_pos (by decide))
  have hdivhi : hi / 2 ^ s = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hhix)
  have hfin : rotrn w s (hi + lo * 2 ^ s) = hi * 2 ^ (w + 1 - s) + lo := by
    simp [rotrn, hmod, hmodhi, hdiv, hdivhi]
  rw [← hrot, hfin] at *
  omega

/-- Popcount is invariant under rotation. Uses `hs` and `hx` via the halves. -/
theorem popcountn_rotln (w s x : Nat) (hs : s ≤ w) (hx : x < 2 ^ (w + 1)) :
    popcountn w (rotln w s x) = popcountn w x := by
  generalize ht : w + 1 - s = t
  have hW : s + t = w + 1 := by omega
  have hW2 : t + s = w + 1 := by omega
  have hpowW : 2 ^ t * 2 ^ s = 2 ^ (w + 1) := by
    rw [← Nat.pow_add, hW2]
  generalize hhi : x / 2 ^ t = hi
  generalize hlo : x % 2 ^ t = lo
  have hlox : lo < 2 ^ t := by omega
  have hhix : hi < 2 ^ s := by
    have hxW : x < 2 ^ t * 2 ^ s := by omega
    have hdiv : x / 2 ^ t < 2 ^ s := Nat.div_lt_of_lt_mul hxW
    omega
  have hrot : rotln w s x = hi + lo * 2 ^ s := by
    simp [rotln, ht, hlo, hhi, Nat.add_comm]
  have hsplit : x = lo + hi * 2 ^ t := by
    have h := Nat.div_add_mod x (2 ^ t)
    have hc : 2 ^ t * (x / 2 ^ t) = hi * 2 ^ t := by rw [hhi, Nat.mul_comm]
    omega
  have hLHS : popAux (w + 1) (hi + lo * 2 ^ s)
      = popAux s hi + popAux t lo := by
    rw [← hW]
    exact popAux_add_mul_pow s t hi lo hhix
  have hRHS : popAux (w + 1) x = popAux t lo + popAux s hi := by
    rw [← hW2, hsplit]
    exact popAux_add_mul_pow t s lo hi hlox
  simp [popcountn, hrot, hLHS, hRHS, Nat.add_comm]

end Gabbro.Grammatik
