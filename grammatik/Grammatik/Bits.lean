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

/-! ## Byteswap at `Nat` level: one byte reader, three widths. -/

/-- Byte `n` of `x` (base 256). -/
def byteOf (x n : Nat) : Nat := (x / 256 ^ n) % 256

theorem byteOf_lt (x n : Nat) : byteOf x n < 256 :=
  Nat.mod_lt _ (by decide)

theorem ladder0 (x : Nat) : x / 256 ^ 0 = x := by
  have : (256 : Nat) ^ 0 = 1 := Nat.pow_zero 256
  rw [this, Nat.div_one]

theorem ladder2 (x : Nat) : x / 256 ^ 2 = (x / 256) / 256 := by
  have e : (256 : Nat) ^ 2 = 256 * 256 := by decide
  rw [e, ← Nat.div_div_eq_div_mul]

theorem ladder3 (x : Nat) : x / 256 ^ 3 = ((x / 256) / 256) / 256 := by
  have e3 : (256 : Nat) ^ 3 = 256 * 256 * 256 := by decide
  rw [e3, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]

/-- One packet step: low byte out, rest down. Uses `hb` (byte fits). -/
theorem pkt_div (r b : Nat) (hb : b < 256) : (r * 256 + b) / 256 = r := by
  have e : r * 256 + b = b + r * 256 := Nat.add_comm _ _
  rw [e, Nat.add_mul_div_right _ _ (by decide : 0 < 256)]
  have hb0 : b / 256 = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hb)
  omega

/-- One packet step for `%`. Uses `hb` (byte fits). -/
theorem pkt_mod (r b : Nat) (hb : b < 256) : (r * 256 + b) % 256 = b := by
  have e : r * 256 + b = b + r * 256 := Nat.add_comm _ _
  rw [e, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt hb

/-- Packet bound: one more byte stays under the next power. -/
theorem pkt_lt (r b k : Nat) (hr : r < 256 ^ k) (hb : b < 256) :
    r * 256 + b < 256 ^ (k + 1) := by
  have e : (256 : Nat) ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
  have hr1 : r + 1 ≤ 256 ^ k := hr
  have hmul : (r + 1) * 256 ≤ 256 ^ k * 256 := Nat.mul_le_mul_right _ hr1
  have hexpand : (r + 1) * 256 = r * 256 + 256 := by
    rw [Nat.add_mul, Nat.one_mul]
  have hlt : r * 256 + b < r * 256 + 256 :=
    Nat.add_lt_add_left hb _
  have hle : r * 256 + 256 ≤ 256 ^ k * 256 := by
    rw [← hexpand]
    exact hmul
  have hfin : r * 256 + b < 256 ^ k * 256 := Nat.lt_of_lt_of_le hlt hle
  rw [e]
  exact hfin

/-- Byte pair reads back both bytes. Uses `h0`, `h1` (bytes fit). -/
theorem byteOf_pair (b0 b1 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) :
    byteOf (b1 * 256 + b0) 0 = b0 ∧ byteOf (b1 * 256 + b0) 1 = b1 := by
  have m0 : byteOf (b1 * 256 + b0) 0 = b0 := by
    simp only [byteOf]
    have e0 : (b1 * 256 + b0) / 256 ^ 0 = b1 * 256 + b0 := by
      have e : (256 : Nat) ^ 0 = 1 := Nat.pow_zero 256
      rw [e, Nat.div_one]
    rw [e0]
    exact pkt_mod _ _ h0
  have m1 : byteOf (b1 * 256 + b0) 1 = b1 := by
    simp only [byteOf]
    have e : (256 : Nat) ^ 1 = 256 := Nat.pow_one 256
    rw [e, pkt_div _ _ h0]
    exact Nat.mod_eq_of_lt h1
  exact ⟨m0, m1⟩

/-- Two-byte split from the `u16` bound. Uses `hx` (value fits). -/
theorem split2 (x : Nat) (hx : x < 256 ^ 2) :
    ∃ b0 b1, b0 < 256 ∧ b1 < 256 ∧ x = b1 * 256 + b0 := by
  refine ⟨x % 256, x / 256, Nat.mod_lt _ (by decide), ?_, ?_⟩
  · have h256 : (256 : Nat) ^ 2 = 256 * 256 := by decide
    rw [h256] at hx
    exact Nat.div_lt_of_lt_mul hx
  · have h := Nat.div_add_mod x 256
    omega

/-- Four-byte split from the `u32` bound. Uses `hx` (value fits). -/
theorem split4 (x : Nat) (hx : x < 256 ^ 4) :
    ∃ b0 b1 b2 b3, b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      x = ((b3 * 256 + b2) * 256 + b1) * 256 + b0 := by
  refine ⟨x % 256, (x / 256) % 256, (x / 256 / 256) % 256, x / 256 / 256 / 256,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    ?_, ?_⟩
  · have h256 : (256 : Nat) ^ 4 = 256 * (256 * (256 * 256)) := by decide
    rw [h256] at hx
    have h1 : x / 256 < 256 * (256 * 256) := Nat.div_lt_of_lt_mul hx
    have h2 : x / 256 / 256 < 256 * 256 := Nat.div_lt_of_lt_mul h1
    exact Nat.div_lt_of_lt_mul h2
  · have h := Nat.div_add_mod x 256
    have h2 := Nat.div_add_mod (x / 256) 256
    have h3 := Nat.div_add_mod (x / 256 / 256) 256
    omega

/-- Four-byte nest reads back all bytes. -/
theorem byteOf_nest (b0 b1 b2 b3 : Nat)
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    byteOf (((b3 * 256 + b2) * 256 + b1) * 256 + b0) 0 = b0 ∧
    byteOf (((b3 * 256 + b2) * 256 + b1) * 256 + b0) 1 = b1 ∧
    byteOf (((b3 * 256 + b2) * 256 + b1) * 256 + b0) 2 = b2 ∧
    byteOf (((b3 * 256 + b2) * 256 + b1) * 256 + b0) 3 = b3 := by
  have d1 : ((((b3 * 256 + b2) * 256 + b1) * 256 + b0) / 256)
      = ((b3 * 256 + b2) * 256 + b1) := pkt_div _ _ h0
  have d2 : ((((b3 * 256 + b2) * 256 + b1)) / 256)
      = (b3 * 256 + b2) := pkt_div _ _ h1
  have d3 : (((b3 * 256 + b2)) / 256) = b3 := pkt_div _ _ h2
  have m0 : byteOf (((b3 * 256 + b2) * 256 + b1) * 256 + b0) 0 = b0 := by
    simp only [byteOf, ladder0]
    exact pkt_mod _ _ h0
  have m1 : byteOf (((b3 * 256 + b2) * 256 + b1) * 256 + b0) 1 = b1 := by
    simp only [byteOf, d1]
    exact pkt_mod _ _ h1
  have m2 : byteOf (((b3 * 256 + b2) * 256 + b1) * 256 + b0) 2 = b2 := by
    simp only [byteOf, ladder2, d1, d2]
    exact pkt_mod _ _ h2
  have m3 : byteOf (((b3 * 256 + b2) * 256 + b1) * 256 + b0) 3 = b3 := by
    simp only [byteOf, ladder3, d1, d2, d3]
    exact Nat.mod_eq_of_lt h3
  exact ⟨m0, m1, m2, m3⟩

/-- Byte swap 16: exchange the two bytes. -/
def bswap16n (x : Nat) : Nat := byteOf x 0 * 256 + byteOf x 1

/-- Byte swap 32: reverse the four bytes. -/
def bswap32n (x : Nat) : Nat :=
  byteOf x 0 * 256 ^ 3 + byteOf x 1 * 256 ^ 2 + byteOf x 2 * 256 + byteOf x 3

/-- Byte swap 64: reverse the eight bytes. -/
def bswap64n (x : Nat) : Nat :=
  byteOf x 0 * 256 ^ 7 + byteOf x 1 * 256 ^ 6 + byteOf x 2 * 256 ^ 5
    + byteOf x 3 * 256 ^ 4 + byteOf x 4 * 256 ^ 3 + byteOf x 5 * 256 ^ 2
    + byteOf x 6 * 256 + byteOf x 7

/-- `bswap16` stays in range. Uses the byte bounds. -/
theorem bswap16n_lt (x : Nat) : bswap16n x < 256 ^ 2 := by
  have h0 : byteOf x 0 < 256 := byteOf_lt x 0
  have h1 : byteOf x 1 < 256 := byteOf_lt x 1
  have h0' : byteOf x 0 < 256 ^ 1 := by
    have e : (256 : Nat) ^ 1 = 256 := Nat.pow_one 256
    rw [e]; exact h0
  have hA := pkt_lt (byteOf x 0) (byteOf x 1) 1 h0' h1
  rw [show (1 : Nat) + 1 = 2 from rfl] at hA
  simp [bswap16n]
  exact hA

/-- `bswap16` is an involution on `u16`. Uses `hx` (value fits). -/
theorem bswap16n_invol (x : Nat) (hx : x < 256 ^ 2) :
    bswap16n (bswap16n x) = x := by
  obtain ⟨b0, b1, h0, h1, hsplit⟩ := split2 x hx
  have hbytes := byteOf_pair b0 b1 h0 h1
  have hswap : bswap16n (b1 * 256 + b0) = b0 * 256 + b1 := by
    simp only [bswap16n, hbytes.1, hbytes.2]
  have hback := byteOf_pair b1 b0 h1 h0
  have hfin : bswap16n (b0 * 256 + b1) = b1 * 256 + b0 := by
    simp only [bswap16n, hback.1, hback.2]
  rw [hsplit, hswap, hfin]

/-- 32-bit nest folds to the packet form. -/
theorem bswap32n_nest (b0 b1 b2 b3 : Nat) :
    b0 * 256 ^ 3 + b1 * 256 ^ 2 + b2 * 256 + b3
      = ((b0 * 256 + b1) * 256 + b2) * 256 + b3 := by
  have e2 : (256 : Nat) ^ 2 = 256 * 256 := by decide
  have e3 : (256 : Nat) ^ 3 = (256 * 256) * 256 := by decide
  have h0 : b0 * 256 ^ 3 = ((b0 * 256) * 256) * 256 := by
    rw [e3, ← Nat.mul_assoc, ← Nat.mul_assoc]
  have h1 : b1 * 256 ^ 2 = (b1 * 256) * 256 := by
    rw [e2, ← Nat.mul_assoc]
  rw [h0, h1, ← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]

/-- `bswap32` stays in range. Uses the byte bounds. -/
theorem bswap32n_lt (x : Nat) : bswap32n x < 256 ^ 4 := by
  have h0 : byteOf x 0 < 256 := byteOf_lt x 0
  have h1 : byteOf x 1 < 256 := byteOf_lt x 1
  have h2 : byteOf x 2 < 256 := byteOf_lt x 2
  have h3 : byteOf x 3 < 256 := byteOf_lt x 3
  have h0' : byteOf x 0 < 256 ^ 1 := by
    have e : (256 : Nat) ^ 1 = 256 := Nat.pow_one 256
    rw [e]; exact h0
  have hA := pkt_lt (byteOf x 0) (byteOf x 1) 1 h0' h1
  rw [show (1 : Nat) + 1 = 2 from rfl] at hA
  have hB := pkt_lt _ (byteOf x 2) 2 hA h2
  rw [show (2 : Nat) + 1 = 3 from rfl] at hB
  have hC := pkt_lt _ (byteOf x 3) 3 hB h3
  rw [show (3 : Nat) + 1 = 4 from rfl] at hC
  have hnest := bswap32n_nest (byteOf x 0) (byteOf x 1) (byteOf x 2) (byteOf x 3)
  simp only [bswap32n] at hnest ⊢
  rw [hnest]
  exact hC

/-- `bswap32` is an involution on `u32`. Uses `hx` (value fits). -/
theorem bswap32n_invol (x : Nat) (hx : x < 256 ^ 4) :
    bswap32n (bswap32n x) = x := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, hsplit⟩ := split4 x hx
  have hbytes := byteOf_nest b0 b1 b2 b3 h0 h1 h2 h3
  have hswap : bswap32n (((b3 * 256 + b2) * 256 + b1) * 256 + b0)
      = ((b0 * 256 + b1) * 256 + b2) * 256 + b3 := by
    simp only [bswap32n, hbytes.1, hbytes.2.1, hbytes.2.2.1, hbytes.2.2.2]
    exact bswap32n_nest b0 b1 b2 b3
  have hback := byteOf_nest b3 b2 b1 b0 h3 h2 h1 h0
  have hfin : bswap32n (((b0 * 256 + b1) * 256 + b2) * 256 + b3)
      = ((b3 * 256 + b2) * 256 + b1) * 256 + b0 := by
    simp only [bswap32n, hback.1, hback.2.1, hback.2.2.1, hback.2.2.2]
    exact bswap32n_nest b3 b2 b1 b0
  rw [hsplit, hswap, hfin]

theorem ladder4 (x : Nat) : x / 256 ^ 4 = (((x / 256) / 256) / 256) / 256 := by
  have e : (256 : Nat) ^ 4 = 256 * 256 * 256 * 256 := by decide
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]

theorem ladder5 (x : Nat) : x / 256 ^ 5 = ((((x / 256) / 256) / 256) / 256) / 256 := by
  have e : (256 : Nat) ^ 5 = 256 * 256 * 256 * 256 * 256 := by decide
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul]

theorem ladder6 (x : Nat) : x / 256 ^ 6 = (((((x / 256) / 256) / 256) / 256) / 256) / 256 := by
  have e : (256 : Nat) ^ 6 = 256 * 256 * 256 * 256 * 256 * 256 := by decide
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]

theorem ladder7 (x : Nat) : x / 256 ^ 7 = ((((((x / 256) / 256) / 256) / 256) / 256) / 256) / 256 := by
  have e : (256 : Nat) ^ 7 = 256 * 256 * 256 * 256 * 256 * 256 * 256 := by decide
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]

/-- Eight-byte split from the `u64` bound. Uses `hx` (value fits). -/
theorem split8 (x : Nat) (hx : x < 256 ^ 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      b4 < 256 ∧ b5 < 256 ∧ b6 < 256 ∧ b7 < 256 ∧
      x = ((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0 := by
  refine ⟨x % 256, (x / 256) % 256, (x / 256 / 256) % 256, (x / 256 / 256 / 256) % 256,
    (x / 256 / 256 / 256 / 256) % 256, (x / 256 / 256 / 256 / 256 / 256) % 256,
    (x / 256 / 256 / 256 / 256 / 256 / 256) % 256, x / 256 / 256 / 256 / 256 / 256 / 256 / 256,
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), ?_, ?_⟩
  · have h256 : (256 : Nat) ^ 8
        = 256 * (256 * (256 * (256 * (256 * (256 * (256 * 256)))))) := by decide
    rw [h256] at hx
    have h1 := Nat.div_lt_of_lt_mul hx
    have h2 := Nat.div_lt_of_lt_mul h1
    have h3 := Nat.div_lt_of_lt_mul h2
    have h4 := Nat.div_lt_of_lt_mul h3
    have h5 := Nat.div_lt_of_lt_mul h4
    have h6 := Nat.div_lt_of_lt_mul h5
    exact Nat.div_lt_of_lt_mul h6
  · have h := Nat.div_add_mod x 256
    have h2 := Nat.div_add_mod (x / 256) 256
    have h3 := Nat.div_add_mod (x / 256 / 256) 256
    have h4 := Nat.div_add_mod (x / 256 / 256 / 256) 256
    have h5 := Nat.div_add_mod (x / 256 / 256 / 256 / 256) 256
    have h6 := Nat.div_add_mod (x / 256 / 256 / 256 / 256 / 256) 256
    have h7 := Nat.div_add_mod (x / 256 / 256 / 256 / 256 / 256 / 256) 256
    omega

/-- Eight-byte nest reads back all bytes. -/
theorem byteOf_nest8 (b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    byteOf (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) 0 = b0 ∧
    byteOf (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) 1 = b1 ∧
    byteOf (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) 2 = b2 ∧
    byteOf (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) 3 = b3 ∧
    byteOf (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) 4 = b4 ∧
    byteOf (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) 5 = b5 ∧
    byteOf (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) 6 = b6 ∧
    byteOf (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) 7 = b7 := by
  have d1 : (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0) / 256
      = (((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1 :=
    pkt_div _ _ h0
  have d2 : ((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) / 256
      = (((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) :=
    pkt_div _ _ h1
  have d3 : ((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2)) / 256
      = ((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) :=
    pkt_div _ _ h2
  have d4 : (((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3)) / 256
      = ((((b7 * 256 + b6) * 256 + b5) * 256 + b4)) :=
    pkt_div _ _ h3
  have d5 : ((((b7 * 256 + b6) * 256 + b5) * 256 + b4)) / 256
      = (((b7 * 256 + b6) * 256 + b5)) :=
    pkt_div _ _ h4
  have d6 : ((((b7 * 256 + b6) * 256 + b5))) / 256
      = ((b7 * 256 + b6)) :=
    pkt_div _ _ h5
  have d7 : (((b7 * 256 + b6))) / 256 = b7 :=
    pkt_div _ _ h6
  simp only [byteOf, ladder0, d1, d2, d3, d4, d5, d6, d7, ladder2, ladder3,
    ladder4, ladder5, ladder6, ladder7]
  refine ⟨pkt_mod _ _ h0, pkt_mod _ _ h1, pkt_mod _ _ h2, pkt_mod _ _ h3,
    pkt_mod _ _ h4, pkt_mod _ _ h5, pkt_mod _ _ h6, Nat.mod_eq_of_lt h7⟩

/-- One Horner fold step: factor a shared `256 ^ k` out of the head pair. -/
theorem horner_step (a b k : Nat) :
    a * 256 ^ (k + 1) + b * 256 ^ k = (a * 256 + b) * 256 ^ k := by
  calc a * 256 ^ (k + 1) + b * 256 ^ k
      = a * (256 ^ k * 256) + b * 256 ^ k := by rw [Nat.pow_succ]
    _ = (a * 256 ^ k) * 256 + b * 256 ^ k := by rw [Nat.mul_assoc a]
    _ = ((a * 256 ^ k) * 256 + b * 256 ^ k) := rfl
    _ = ((a * 256) * 256 ^ k + b * 256 ^ k) := by
        have h : (a * 256 ^ k) * 256 = (a * 256) * 256 ^ k := by
          calc (a * 256 ^ k) * 256 = a * (256 ^ k * 256) := by rw [Nat.mul_assoc]
            _ = a * (256 * 256 ^ k) := by rw [Nat.mul_comm (256 ^ k) 256]
            _ = (a * 256) * 256 ^ k := by rw [Nat.mul_assoc]
        rw [h]
    _ = (a * 256 + b) * 256 ^ k := by rw [Nat.add_mul]

/-- 64-bit nest folds to the packet form. -/
theorem bswap64n_nest (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    b0 * 256 ^ 7 + b1 * 256 ^ 6 + b2 * 256 ^ 5 + b3 * 256 ^ 4
      + b4 * 256 ^ 3 + b5 * 256 ^ 2 + b6 * 256 + b7
      = ((((((b0 * 256 + b1) * 256 + b2) * 256 + b3) * 256 + b4) * 256 + b5) * 256 + b6) * 256 + b7 := by
  have e6 : (6 : Nat) + 1 = 7 := rfl
  have e5 : (5 : Nat) + 1 = 6 := rfl
  have e4 : (4 : Nat) + 1 = 5 := rfl
  have e3 : (3 : Nat) + 1 = 4 := rfl
  have e2 : (2 : Nat) + 1 = 3 := rfl
  have e1 : (1 : Nat) + 1 = 2 := rfl
  have h7 : b7 = b7 * 256 ^ 0 := by simp
  rw [h7, ← e6, horner_step, ← e5, horner_step, ← e4, horner_step, ← e3,
    horner_step, ← e2, horner_step, ← e1, horner_step, horner_step]

/-- `bswap64` stays in range. Uses the byte bounds. -/
theorem bswap64n_lt (x : Nat) : bswap64n x < 256 ^ 8 := by
  have h0 : byteOf x 0 < 256 := byteOf_lt x 0
  have h1 : byteOf x 1 < 256 := byteOf_lt x 1
  have h2 : byteOf x 2 < 256 := byteOf_lt x 2
  have h3 : byteOf x 3 < 256 := byteOf_lt x 3
  have h4 : byteOf x 4 < 256 := byteOf_lt x 4
  have h5 : byteOf x 5 < 256 := byteOf_lt x 5
  have h6 : byteOf x 6 < 256 := byteOf_lt x 6
  have h7 : byteOf x 7 < 256 := byteOf_lt x 7
  have h0' : byteOf x 0 < 256 ^ 1 := by
    have e : (256 : Nat) ^ 1 = 256 := Nat.pow_one 256
    rw [e]; exact h0
  have hA := pkt_lt (byteOf x 0) (byteOf x 1) 1 h0' h1
  rw [show (1 : Nat) + 1 = 2 from rfl] at hA
  have hB := pkt_lt _ (byteOf x 2) 2 hA h2
  rw [show (2 : Nat) + 1 = 3 from rfl] at hB
  have hC := pkt_lt _ (byteOf x 3) 3 hB h3
  rw [show (3 : Nat) + 1 = 4 from rfl] at hC
  have hD := pkt_lt _ (byteOf x 4) 4 hC h4
  rw [show (4 : Nat) + 1 = 5 from rfl] at hD
  have hE := pkt_lt _ (byteOf x 5) 5 hD h5
  rw [show (5 : Nat) + 1 = 6 from rfl] at hE
  have hF := pkt_lt _ (byteOf x 6) 6 hE h6
  rw [show (6 : Nat) + 1 = 7 from rfl] at hF
  have hG := pkt_lt _ (byteOf x 7) 7 hF h7
  rw [show (7 : Nat) + 1 = 8 from rfl] at hG
  have hnest := bswap64n_nest (byteOf x 0) (byteOf x 1) (byteOf x 2) (byteOf x 3)
    (byteOf x 4) (byteOf x 5) (byteOf x 6) (byteOf x 7)
  simp only [bswap64n] at hnest ⊢
  rw [hnest]
  exact hG

/-- `bswap64` is an involution on `u64`. Uses `hx` (value fits). -/
theorem bswap64n_invol (x : Nat) (hx : x < 256 ^ 8) :
    bswap64n (bswap64n x) = x := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, hsplit⟩ :=
    split8 x hx
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ :=
    byteOf_nest8 b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7
  have hswap : bswap64n (((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0)
      = ((((((b0 * 256 + b1) * 256 + b2) * 256 + b3) * 256 + b4) * 256 + b5) * 256 + b6) * 256 + b7 := by
    simp only [bswap64n, e0, e1, e2, e3, e4, e5, e6, e7]
    exact bswap64n_nest b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ :=
    byteOf_nest8 b7 b6 b5 b4 b3 b2 b1 b0 h7 h6 h5 h4 h3 h2 h1 h0
  have hfin : bswap64n (((((((b0 * 256 + b1) * 256 + b2) * 256 + b3) * 256 + b4) * 256 + b5) * 256 + b6) * 256 + b7)
      = ((((((b7 * 256 + b6) * 256 + b5) * 256 + b4) * 256 + b3) * 256 + b2) * 256 + b1) * 256 + b0 := by
    simp only [bswap64n, f0, f1, f2, f3, f4, f5, f6, f7]
    exact bswap64n_nest b7 b6 b5 b4 b3 b2 b1 b0
  rw [hsplit, hswap, hfin]

/-! ## `Zahl` wrappers: the PLAN-BITS.md section 3 signatures.

    Width is `w + 1` (never `w - 1`), so `w = 0` gives width 1, not a
    truncation. `clz` / `ctz` / `log2` take `Zahl 1 (2^(w+1) - 1)`: zero is
    inexpressible, so the C lowering never reaches `__builtin_clz(0)`. -/

/-- The `Nat` value inside a nonzero field element. -/
def zahlNat (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) : Nat :=
  x.n.toNat

/-- The `Nat` value is positive and in range. -/
theorem zahlNat_bounds (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    0 < zahlNat w x ∧ zahlNat w x < 2 ^ (w + 1) := by
  have hlo := x.lo_le
  have hhi := x.le_hi
  have hcast : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
  simp only [zahlNat]
  constructor
  · have hpos : (0 : Int) < x.n := by omega
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ x.n by omega)
    omega
  · have hlt : x.n < ((2 ^ (w + 1) : Nat) : Int) := by omega
    exact (Int.toNat_lt (show (0 : Int) ≤ x.n by omega)).mpr hlt

/-- `Nat.log2` of a field element fits the index range. -/
theorem log2n_le_of_bounds (w xn : Nat) (hx0 : 0 < xn)
    (hxW : xn < 2 ^ (w + 1)) : Nat.log2 xn ≤ w := by
  cases Decidable.em (Nat.log2 xn ≤ w) with
  | inl h => exact h
  | inr h =>
    exfalso
    have hne : xn ≠ 0 := Nat.ne_of_gt hx0
    have hge : w + 1 ≤ Nat.log2 xn := by omega
    have hmono : 2 ^ (w + 1) ≤ 2 ^ Nat.log2 xn :=
      Nat.pow_le_pow_right (by decide) hge
    have hspec := (Nat.log2_eq_iff hne).mp rfl
    omega

/-- `Zahl.clz`: leading zeros over width `w + 1`. -/
def Zahl.clz (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 (w : Int) :=
  ⟨(clzn w (zahlNat w x) : Nat), by simp,
    Int.ofNat_le.mpr (Nat.sub_le w (Nat.log2 (zahlNat w x)))⟩

/-- `Zahl.ctz`: trailing zeros over width `w + 1`. -/
def Zahl.ctz (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 (w : Int) :=
  ⟨(ctzn w (zahlNat w x) : Nat), by simp,
    Int.ofNat_le.mpr
      (ctzn_le (zahlNat_bounds w x).1 (zahlNat_bounds w x).2)⟩

/-- `Zahl.log2_floor`: floor log2 over width `w + 1`. -/
def Zahl.log2_floor (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 (w : Int) :=
  ⟨(Nat.log2 (zahlNat w x) : Nat), by simp,
    Int.ofNat_le.mpr
      (log2n_le_of_bounds w _ (zahlNat_bounds w x).1 (zahlNat_bounds w x).2)⟩

/-- Rotation amount as a `Nat` bounded by `w`. Uses the amount range. -/
theorem zahlAmt_le (w : Nat) (s : Zahl 0 (w : Int)) : s.n.toNat ≤ w := by
  have hlo := s.lo_le
  have hhi := s.le_hi
  have hnn : 0 ≤ s.n := by omega
  exact (Int.toNat_le).mpr hhi

/-- Full-range (`uN`) value as a `Nat` under `2 ^ (w+1)`. -/
theorem zahlFull_bounds (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    x.n.toNat < 2 ^ (w + 1) := by
  have hhi := x.le_hi
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have hcast : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
  have hlt : x.n < ((2 ^ (w + 1) : Nat) : Int) := by omega
  exact (Int.toNat_lt hnn).mpr hlt

/-- `rotr ∘ rotl = id` helper: right rotation stays in range. -/
theorem rotrn_lt (w s x : Nat) (hs : s ≤ w) (hx : x < 2 ^ (w + 1)) :
    rotrn w s x < 2 ^ (w + 1) := by
  have hW : s + (w + 1 - s) = w + 1 := by omega
  have hpowW : 2 ^ s * 2 ^ (w + 1 - s) = 2 ^ (w + 1) := by
    rw [← Nat.pow_add, hW]
  have hmod : x % 2 ^ s < 2 ^ s :=
    Nat.mod_lt x (Nat.pow_pos (by decide))
  have hdiv : x / 2 ^ s < 2 ^ (w + 1 - s) := by
    have hxW : x < 2 ^ s * 2 ^ (w + 1 - s) := by omega
    exact Nat.div_lt_of_lt_mul hxW
  have hmul1 : (x % 2 ^ s + 1) * 2 ^ (w + 1 - s)
      ≤ 2 ^ s * 2 ^ (w + 1 - s) :=
    Nat.mul_le_mul_right _ hmod
  have hexpand : (x % 2 ^ s + 1) * 2 ^ (w + 1 - s)
      = (x % 2 ^ s) * 2 ^ (w + 1 - s) + 2 ^ (w + 1 - s) := by
    rw [Nat.add_mul, Nat.one_mul]
  have hstep : (x % 2 ^ s) * 2 ^ (w + 1 - s) + x / 2 ^ s
      < (x % 2 ^ s) * 2 ^ (w + 1 - s) + 2 ^ (w + 1 - s) :=
    Nat.add_lt_add_left hdiv _
  have h2 : (x % 2 ^ s) * 2 ^ (w + 1 - s) + 2 ^ (w + 1 - s) ≤ 2 ^ (w + 1) := by
    rw [← hexpand]
    exact Nat.le_trans hmul1 (Nat.le_of_eq hpowW)
  have hchain : (x % 2 ^ s) * 2 ^ (w + 1 - s) + x / 2 ^ s < 2 ^ (w + 1) :=
    Nat.lt_of_lt_of_le hstep h2
  show rotrn w s x < 2 ^ (w + 1)
  unfold rotrn
  exact hchain

/-- `Zahl.popcount`: population count over width `w + 1`. -/
def Zahl.popcount (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 ((w : Int) + 1) :=
  ⟨(popcountn w x.n.toNat : Nat), by simp,
    Int.ofNat_le.mpr (popcountn_le w _)⟩

/-- `Zahl.rotl`: rotate left over width `w + 1`. -/
def Zahl.rotl (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) : Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(rotln w s.n.toNat x.n.toNat : Nat), by
      have := x.lo_le; simp,
    by
      have hcast : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
      have hlt : rotln w s.n.toNat x.n.toNat < 2 ^ (w + 1) :=
        rotln_lt w _ _ (zahlAmt_le w s) (zahlFull_bounds w x)
      have hle : ((rotln w s.n.toNat x.n.toNat : Nat) : Int)
          < ((2 ^ (w + 1) : Nat) : Int) := Int.ofNat_lt.mpr hlt
      omega⟩

/-- `Zahl.rotr`: rotate right over width `w + 1`. -/
def Zahl.rotr (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) : Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(rotrn w s.n.toNat x.n.toNat : Nat), by
      have := x.lo_le; simp,
    by
      have hcast : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
      have hlt : rotrn w s.n.toNat x.n.toNat < 2 ^ (w + 1) :=
        rotrn_lt w _ _ (zahlAmt_le w s) (zahlFull_bounds w x)
      have hle : ((rotrn w s.n.toNat x.n.toNat : Nat) : Int)
          < ((2 ^ (w + 1) : Nat) : Int) := Int.ofNat_lt.mpr hlt
      omega⟩

/-- 256-power / 2-power bridges for the three widths. -/
theorem pow256_eq_pow2_16 : (256 : Nat) ^ 2 = 2 ^ 16 := by decide

theorem pow256_eq_pow2_32 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide

theorem pow256_eq_pow2_64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide

/-- `Zahl.bswap16`: byte reversal on `u16`. -/
def Zahl.bswap16 (x : Zahl 0 ((2 : Int) ^ 16 - 1)) :
    Zahl 0 ((2 : Int) ^ 16 - 1) :=
  ⟨((bswap16n x.n.toNat : Nat) : Int), by
    have := x.lo_le; simp,
   by
    have hlt : bswap16n x.n.toNat < 256 ^ 2 := bswap16n_lt _
    rw [pow256_eq_pow2_16] at hlt
    have hcast : ((2 ^ 16 : Nat) : Int) = (2 : Int) ^ 16 := by simp
    have hltI : ((bswap16n x.n.toNat : Nat) : Int) < ((2 ^ 16 : Nat) : Int) :=
      Int.ofNat_lt.mpr hlt
    omega⟩

/-- `Zahl.bswap32`: byte reversal on `u32`. -/
def Zahl.bswap32 (x : Zahl 0 ((2 : Int) ^ 32 - 1)) :
    Zahl 0 ((2 : Int) ^ 32 - 1) :=
  ⟨((bswap32n x.n.toNat : Nat) : Int), by
    have := x.lo_le; simp,
   by
    have hlt : bswap32n x.n.toNat < 256 ^ 4 := bswap32n_lt _
    rw [pow256_eq_pow2_32] at hlt
    have hcast : ((2 ^ 32 : Nat) : Int) = (2 : Int) ^ 32 := by simp
    have hltI : ((bswap32n x.n.toNat : Nat) : Int) < ((2 ^ 32 : Nat) : Int) :=
      Int.ofNat_lt.mpr hlt
    omega⟩

/-- `Zahl.bswap64`: byte reversal on `u64`. -/
def Zahl.bswap64 (x : Zahl 0 ((2 : Int) ^ 64 - 1)) :
    Zahl 0 ((2 : Int) ^ 64 - 1) :=
  ⟨((bswap64n x.n.toNat : Nat) : Int), by
    have := x.lo_le; simp,
   by
    have hlt : bswap64n x.n.toNat < 256 ^ 8 := bswap64n_lt _
    rw [pow256_eq_pow2_64] at hlt
    have hcast : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by simp
    have hltI : ((bswap64n x.n.toNat : Nat) : Int) < ((2 ^ 64 : Nat) : Int) :=
      Int.ofNat_lt.mpr hlt
    omega⟩

/-! ## Target theorems at `Zahl` level (PLAN-BITS.md section 3).

    `r` is named as a `Nat` (`Nat.log2` / `ctzn` of the unwrapped value) and
    tied to the wrapper by `rfl`: `(Zahl.log2_floor w x).n` IS
    `Nat.log2 (zahlNat w x)` definitionally, and similarly for `clz`/`ctz`.
    Every premise is consumed: the Nat specs need positivity and the upper
    bound, both from `zahlNat_bounds`. -/

/-- `log2_floor_spez`: `2 ^ r ≤ x < 2 ^ (r+1)` for `r = log2_floor x`. -/
theorem log2_floor_spez (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    (2 : Int) ^ Nat.log2 (zahlNat w x) ≤ x.n
      ∧ x.n < (2 : Int) ^ (Nat.log2 (zahlNat w x) + 1) := by
  have hb := zahlNat_bounds w x
  have hne : zahlNat w x ≠ 0 := Nat.ne_of_gt hb.1
  obtain ⟨h1, h2⟩ := log2n_spez hne
  simp only [log2n] at h1 h2
  have hcast1 : (((2 ^ Nat.log2 (zahlNat w x) : Nat)) : Int)
      = (2 : Int) ^ Nat.log2 (zahlNat w x) := by simp
  have hcast2 : (((2 ^ (Nat.log2 (zahlNat w x) + 1) : Nat)) : Int)
      = (2 : Int) ^ (Nat.log2 (zahlNat w x) + 1) := by simp
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have h2n : (x.n.toNat : Int) = x.n := Int.toNat_of_nonneg hnn
  have hval : x.n.toNat = zahlNat w x := rfl
  constructor
  · have hle : ((2 ^ Nat.log2 (zahlNat w x) : Nat) : Int)
        ≤ ((zahlNat w x : Nat) : Int) := Int.ofNat_le.mpr h1
    rw [hcast1, ← hval, h2n] at hle
    exact hle
  · have hlt : ((x.n.toNat : Nat) : Int)
        < ((2 ^ (Nat.log2 (zahlNat w x) + 1) : Nat) : Int) := by
      rw [hval]; exact Int.ofNat_lt.mpr h2
    rw [hcast2, h2n] at hlt
    exact hlt

end Gabbro.Grammatik
