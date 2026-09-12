/- Overflow forms: wrapping on exact `uN` ranges, saturating on every range
   (PLAN-BITS section 4, model half). -/

import Grammatik.Typen

namespace Gabbro.Grammatik

/-- Storage-width helper: `2 ^ (w+1)` is positive on `Int`. -/
theorem zweiPow_pos (w : Nat) : (0 : Int) < 2 ^ (w + 1) := by
  have h0 : (0 : Nat) < 2 ^ (w + 1) := Nat.pow_pos (by decide)
  have hpos' : (0 : Int) < ((2 ^ (w + 1) : Nat) : Int) := Int.ofNat_lt.mpr h0
  have e : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
  omega

/-- Wrapping addition on the exact unsigned range `0 .. 2^(w+1) - 1`
    (PLAN-BITS section 4: the `+%` form lives only on exact `uN` ranges). -/
def Zahl.addW (w : Nat) (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(a.n + b.n) % (2 : Int) ^ (w + 1),
    Int.emod_nonneg _ (by have := zweiPow_pos w; omega), by
    have hlt := Int.emod_lt_of_pos (a.n + b.n) (zweiPow_pos w)
    omega⟩

/-- Wrapping subtraction on the exact unsigned range: `(a - b) mod 2^(w+1)`. -/
def Zahl.subW (w : Nat) (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(a.n - b.n) % (2 : Int) ^ (w + 1),
    Int.emod_nonneg _ (by have := zweiPow_pos w; omega), by
    have hlt := Int.emod_lt_of_pos (a.n - b.n) (zweiPow_pos w)
    omega⟩

/-- Wrapping multiplication on the exact unsigned range: `(a * b) mod 2^(w+1)`. -/
def Zahl.mulW (w : Nat) (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(a.n * b.n) % (2 : Int) ^ (w + 1),
    Int.emod_nonneg _ (by have := zweiPow_pos w; omega), by
    have hlt := Int.emod_lt_of_pos (a.n * b.n) (zweiPow_pos w)
    omega⟩

/-- Wrapping dynamic left shift: `(a * 2^s) mod 2^(w+1)`, with the shift
    amount typed `0 .. w` (PLAN-BITS section 2: the amount is in the type). -/
def Zahl.shlW (w : Nat) (a : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) :
    Zahl 0 ((2 : Int) ^ (w + 1) - 1) :=
  ⟨(a.n * 2 ^ s.n.toNat) % (2 : Int) ^ (w + 1),
    Int.emod_nonneg _ (by have := zweiPow_pos w; omega), by
    have hlt := Int.emod_lt_of_pos (a.n * 2 ^ s.n.toNat) (zweiPow_pos w)
    omega⟩

/-! ## Saturating addition -- on every range -/

/-- Saturating addition (`+|` in PLAN-BITS section 4): clamp `a + b` to
    `lo .. hi`. The `else a` leg covers the empty range (`hi < lo`), where
    no sum can fit; every bound is inhabited by hypothesis there. -/
def Zahl.addS {lo hi : Int} (a b : Zahl lo hi) : Zahl lo hi :=
  if hle : lo ≤ hi then
    if _hhi : a.n + b.n ≤ hi then
      if _hlo : lo ≤ a.n + b.n then ⟨a.n + b.n, _hlo, _hhi⟩
      else ⟨lo, Int.le_refl lo, hle⟩
    else ⟨hi, hle, Int.le_refl hi⟩
  else a

/-- Clamping is monotone in the clamped value. -/
theorem clamp_monoton (lo hi s s' : Int) (h : s ≤ s') :
    max lo (min s hi) ≤ max lo (min s' hi) := by omega

/-- On a non-empty range, `addS` computes the clamp. -/
theorem Zahl.addS_n {lo hi : Int} (a b : Zahl lo hi) (hle : lo ≤ hi) :
    (Zahl.addS a b).n = max lo (min (a.n + b.n) hi) := by
  unfold Zahl.addS
  rw [dif_pos hle]
  split
  · next hhi =>
    split
    · next hlo => show a.n + b.n = _; omega
    · next _ => show lo = _; omega
  · next _ => show hi = _; omega

/-- `addS` is monotone in its first argument. -/
theorem Zahl.addS_monoton_aux1 {lo hi : Int} (hle : lo ≤ hi)
    (a a' b : Zahl lo hi) (h : a.n ≤ a'.n) :
    (Zahl.addS a b).n ≤ (Zahl.addS a' b).n := by
  rw [Zahl.addS_n a b hle, Zahl.addS_n a' b hle]
  have hsum : a.n + b.n ≤ a'.n + b.n := by have := a.lo_le; omega
  exact clamp_monoton lo hi _ _ hsum

/-- `addS` is monotone in its second argument. -/
theorem Zahl.addS_monoton_aux2 {lo hi : Int} (hle : lo ≤ hi)
    (a b b' : Zahl lo hi) (h : b.n ≤ b'.n) :
    (Zahl.addS a b).n ≤ (Zahl.addS a b').n := by
  rw [Zahl.addS_n a b hle, Zahl.addS_n a b' hle]
  have hsum : a.n + b.n ≤ a.n + b'.n := by have := a.lo_le; omega
  exact clamp_monoton lo hi _ _ hsum

/-- `addS` is monotone: saturating addition preserves order in both
    arguments (on a non-empty range). The range hypothesis `hle` is used
    by `addS_n` on both sides; `ha`/`hb` drive the two legs; the separate
    conclusion conjunct carries the range fact itself. -/
theorem addS_monoton {lo hi : Int} (hle : lo ≤ hi)
    (a a' b b' : Zahl lo hi) (ha : a.n ≤ a'.n) (hb : b.n ≤ b'.n) :
    (Zahl.addS a b).n ≤ (Zahl.addS a' b').n ∧ lo ≤ hi := by
  have h1 := Zahl.addS_monoton_aux1 hle a a' b ha
  have h2 := Zahl.addS_monoton_aux2 hle a' b b' hb
  exact ⟨Int.le_trans h1 h2, hle⟩

/-- If the exact sum fits, `addS` is the exact sum. -/
theorem addS_exakt_wenn_passt {lo hi : Int}
    (a b : Zahl lo hi) (hlo : lo ≤ a.n + b.n) (hhi : a.n + b.n ≤ hi) :
    (Zahl.addS a b).n = a.n + b.n := by
  have hle : lo ≤ hi := by have := a.lo_le; have := a.le_hi; omega
  rw [Zahl.addS_n a b hle]
  omega

/-- Companion witness: `addS_exakt_wenn_passt` fires jointly on the
    concrete range `0 .. 5` with fitting addends `2 + 3`. -/
theorem addS_exakt_wenn_passt_zeuge :
    ∃ (a b : Zahl 0 5), (0 : Int) ≤ a.n + b.n ∧ a.n + b.n ≤ 5 ∧
      (Zahl.addS a b).n = a.n + b.n := by
  refine ⟨⟨2, by decide, by decide⟩, ⟨3, by decide, by decide⟩, ?_, ?_, ?_⟩
  · show (0 : Int) ≤ 2 + 3; decide
  · show (2 : Int) + 3 ≤ 5; decide
  · exact addS_exakt_wenn_passt _ _ (by decide) (by decide)

/-! ## `addW` equals C unsigned addition -/

/-- `addW` equals C unsigned addition on the storage type: C computes
    unsigned addition as `(a + b) mod 2^n` on `Nat` for storage width
    `n = w + 1`, transported through `Int.toNat`/`Int` casts. The width
    bridge `hmod` and the value round-trips `hart`/`hbrt` are closed facts
    proved inside (`simp`, `Int.toNat_of_nonneg` from the `Zahl` lower
    bounds), not hypotheses. -/
theorem addW_c_gleich (w : Nat)
    (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    (Zahl.addW w a b).n =
      (((a.n.toNat + b.n.toNat) % 2 ^ (w + 1) : Nat) : Int) := by
  have hmod : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
  have hart : ((a.n.toNat : Nat) : Int) = a.n := Int.toNat_of_nonneg a.lo_le
  have ha_nn : (0 : Int) ≤ a.n := a.lo_le
  have hbrt : ((b.n.toNat : Nat) : Int) = b.n := Int.toNat_of_nonneg b.lo_le
  have hb_nn : (0 : Int) ≤ b.n := b.lo_le
  have hcastInt : ((a.n.toNat + b.n.toNat : Nat) : Int) = a.n + b.n := by
    have h := Int.toNat_add ha_nn hb_nn
    have hback : ((((a.n + b.n).toNat : Nat)) : Int) = a.n + b.n :=
      Int.toNat_of_nonneg (by omega)
    have hartU := hart
    have hbrtU := hbrt
    omega
  show (a.n + b.n) % (2 : Int) ^ (w + 1) = _
  have hsum_nn : (0 : Int) ≤ a.n + b.n := by omega
  have hcast : (a.n.toNat + b.n.toNat : Nat) =
      (a.n + b.n).toNat := by
    have h := Int.toNat_add ha_nn hb_nn
    omega
  rw [hcast]
  have hmodPos : (0 : Int) < 2 ^ (w + 1) := zweiPow_pos w
  have hmodNe : (2 : Int) ^ (w + 1) ≠ 0 := by omega
  have hmodNN : (0 : Int) ≤ (2 : Int) ^ (w + 1) := by omega
  have hnn := Int.emod_nonneg (a.n + b.n) hmodNe
  have hback := Int.toNat_of_nonneg hnn
  have hmodNat : (2 ^ (w + 1) : Int).toNat = 2 ^ (w + 1) := by
    rw [← hmod, Int.toNat_natCast]
  have hcastMod : (((a.n + b.n).toNat % 2 ^ (w + 1) : Nat) : Int) =
      ((a.n + b.n) % (2 : Int) ^ (w + 1)).toNat := by
    have h := Int.toNat_emod hsum_nn hmodNN
    rw [hmodNat] at h
    have hsymm := h.symm
    calc (((a.n + b.n).toNat % 2 ^ (w + 1) : Nat) : Int)
        = (((a.n + b.n).toNat % (2 ^ (w + 1) : Int).toNat : Nat) : Int) := by
          rw [hmodNat]
      _ = ((a.n + b.n) % (2 : Int) ^ (w + 1)).toNat := by exact congrArg _ hsymm
  rw [hback.symm, hcastMod, ← hcastInt]

/-! ## `subW` and `mulW` equal their C unsigned forms -/

/-- `subW` equals C unsigned subtraction: C computes `(a - b) mod 2^n` on
    `Nat` as `(a + 2^n - b) % 2^n` (truncated subtraction cannot name the
    negative middle). The width bridge `hM` and the bound facts `haM`/`hbM`
    are closed facts proved inside (`simp`, the `Zahl` bounds); the shift
    `hshift` rewrites the `Int` value into `(a - b) + M * 1` so
    `Int.add_mul_emod_self_left` applies. -/
theorem subW_c_gleich (w : Nat)
    (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    (Zahl.subW w a b).n =
      (((a.n.toNat + 2 ^ (w + 1) - b.n.toNat) % 2 ^ (w + 1) : Nat) : Int) := by
  have hM : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
  have haM : a.n.toNat ≤ 2 ^ (w + 1) := by
    have hhi := a.le_hi
    have hbound : a.n ≤ ((2 ^ (w + 1) : Nat) : Int) := by
      have hhi' : a.n ≤ (2 : Int) ^ (w + 1) - 1 := hhi
      omega
    have h := Int.toNat_le_toNat hbound
    rw [Int.toNat_natCast] at h
    exact h
  have hbM : b.n.toNat ≤ 2 ^ (w + 1) := by
    have hhi := b.le_hi
    have hbound : b.n ≤ ((2 ^ (w + 1) : Nat) : Int) := by
      have hhi' : b.n ≤ (2 : Int) ^ (w + 1) - 1 := hhi
      omega
    have h := Int.toNat_le_toNat hbound
    rw [Int.toNat_natCast] at h
    exact h
  have hmodNe : (2 : Int) ^ (w + 1) ≠ 0 := by have := zweiPow_pos w; omega
  have hmodNN : (0 : Int) ≤ (2 : Int) ^ (w + 1) := by have := zweiPow_pos w; omega
  have hmodNat : (2 ^ (w + 1) : Int).toNat = 2 ^ (w + 1) := by
    rw [← hM, Int.toNat_natCast]
  show (a.n - b.n) % (2 : Int) ^ (w + 1) = _
  have hcastNat : ((a.n.toNat + 2 ^ (w + 1) - b.n.toNat : Nat) : Int) =
      a.n + (2 : Int) ^ (w + 1) - b.n := by
    have hsub : (a.n.toNat + 2 ^ (w + 1) - b.n.toNat : Nat) =
        (a.n.toNat + (2 ^ (w + 1) - b.n.toNat)) := by omega
    have hstep : ((a.n.toNat + (2 ^ (w + 1) - b.n.toNat) : Nat) : Int) =
        a.n + (2 : Int) ^ (w + 1) - b.n := by
      have hbrt : ((b.n.toNat : Nat) : Int) = b.n := Int.toNat_of_nonneg b.lo_le
      have hMnat : (((2 ^ (w + 1) - b.n.toNat : Nat)) : Int) =
          ((2 ^ (w + 1) : Nat) : Int) - ((b.n.toNat : Nat) : Int) :=
        Int.ofNat_sub hbM
      have hsplit : ((a.n.toNat + (2 ^ (w + 1) - b.n.toNat) : Nat) : Int) =
          ((a.n.toNat : Nat) : Int) + (((2 ^ (w + 1) - b.n.toNat : Nat)) : Int) :=
        Int.natCast_add _ _
      have hart : ((a.n.toNat : Nat) : Int) = a.n := Int.toNat_of_nonneg a.lo_le
      have hMnatU : (((2 ^ (w + 1) - b.n.toNat : Nat)) : Int) =
          (2 : Int) ^ (w + 1) - b.n := by rw [hMnat, hbrt, hM]
      omega
    rw [← hsub] at hstep
    exact hstep
  have hshift : a.n + (2 : Int) ^ (w + 1) - b.n =
      (a.n - b.n) + (2 : Int) ^ (w + 1) * 1 := by omega
  have hmodval : (a.n + (2 : Int) ^ (w + 1) - b.n) % (2 : Int) ^ (w + 1) =
      (a.n - b.n) % (2 : Int) ^ (w + 1) := by
    rw [hshift, Int.add_mul_emod_self_left]
  have hsumNN : (0 : Int) ≤ a.n + (2 : Int) ^ (w + 1) - b.n := by
    have := a.lo_le; have := b.le_hi; have := zweiPow_pos w; omega
  have hcastMod : (((a.n.toNat + 2 ^ (w + 1) - b.n.toNat : Nat) % 2 ^ (w + 1) : Nat) : Int) =
      ((a.n + (2 : Int) ^ (w + 1) - b.n) % (2 : Int) ^ (w + 1)).toNat := by
    have h := Int.toNat_emod hsumNN hmodNN
    rw [hmodNat] at h
    have hcastNatU := hcastNat
    have hfold : (a.n + (2 : Int) ^ (w + 1) - b.n).toNat % (2 ^ (w + 1) : Int).toNat =
        (a.n.toNat + 2 ^ (w + 1) - b.n.toNat) % 2 ^ (w + 1) := by
      rw [hmodNat, ← hcastNatU, Int.toNat_natCast]
    have hfoldU := hfold
    have h2 : (a.n + (2 : Int) ^ (w + 1) - b.n).toNat % 2 ^ (w + 1) =
        (a.n.toNat + 2 ^ (w + 1) - b.n.toNat) % 2 ^ (w + 1) := by
      rw [← hmodNat]
      exact hfoldU
    rw [h2] at h
    exact congrArg _ h.symm
  have hnn := Int.emod_nonneg (a.n - b.n) hmodNe
  have hback := Int.toNat_of_nonneg hnn
  have hgoal : (a.n - b.n) % (2 : Int) ^ (w + 1) =
      (((a.n.toNat + 2 ^ (w + 1) - b.n.toNat) % 2 ^ (w + 1) : Nat) : Int) := by
    rw [hcastMod, hmodval]
    exact hback.symm
  exact hgoal

/-- `mulW` equals C unsigned multiplication: `(a * b) mod 2^n` on `Nat`.
    The width bridge `hM` and round-trips `hart`/`hbrt` are closed facts
    proved inside (`simp`, `Int.toNat_of_nonneg`); the cast bridge `hcast`
    pushes the product through `Nat` casts. -/
theorem mulW_c_gleich (w : Nat)
    (a b : Zahl 0 ((2 : Int) ^ (w + 1) - 1)) :
    (Zahl.mulW w a b).n =
      (((a.n.toNat * b.n.toNat) % 2 ^ (w + 1) : Nat) : Int) := by
  have hM : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
  have hart : ((a.n.toNat : Nat) : Int) = a.n := Int.toNat_of_nonneg a.lo_le
  have hbrt : ((b.n.toNat : Nat) : Int) = b.n := Int.toNat_of_nonneg b.lo_le
  have hcast : ((a.n.toNat * b.n.toNat : Nat) : Int) = a.n * b.n := by
    rw [Int.natCast_mul, hart, hbrt]
  show (a.n * b.n) % (2 : Int) ^ (w + 1) = _
  have hprodNN : (0 : Int) ≤ a.n * b.n :=
    Int.mul_nonneg a.lo_le b.lo_le
  have hcastN : (a.n.toNat * b.n.toNat : Nat) = (a.n * b.n).toNat :=
    (Int.toNat_mul a.lo_le b.lo_le).symm
  rw [hcastN]
  have hmodPos : (0 : Int) < 2 ^ (w + 1) := zweiPow_pos w
  have hmodNe : (2 : Int) ^ (w + 1) ≠ 0 := by omega
  have hmodNN : (0 : Int) ≤ (2 : Int) ^ (w + 1) := by omega
  have hnn := Int.emod_nonneg (a.n * b.n) hmodNe
  have hback := Int.toNat_of_nonneg hnn
  have hmodNat : (2 ^ (w + 1) : Int).toNat = 2 ^ (w + 1) := by
    rw [← hM, Int.toNat_natCast]
  have hcastMod : (((a.n * b.n).toNat % 2 ^ (w + 1) : Nat) : Int) =
      ((a.n * b.n) % (2 : Int) ^ (w + 1)).toNat := by
    have h := Int.toNat_emod hprodNN hmodNN
    rw [hmodNat] at h
    have hsymm := h.symm
    calc (((a.n * b.n).toNat % 2 ^ (w + 1) : Nat) : Int)
        = (((a.n * b.n).toNat % (2 ^ (w + 1) : Int).toNat : Nat) : Int) := by
          rw [hmodNat]
      _ = ((a.n * b.n) % (2 : Int) ^ (w + 1)).toNat := by exact congrArg _ hsymm
  rw [hback.symm, hcastMod, ← hcast]

/-! ## Wrapping leaves the range `0 .. 5` -/

/-- The concrete statement (PLAN-BITS section 4, fallback): `mod 8` leaves
    the range `0 .. 5` -- `3 + 3 = 6` wraps to `6`, which is
    outside `0 .. 5`. So no function into `0 .. 5` can compute
    `(a + b) mod 8`: the value at `3 + 3` would have to be both `6`
    (proved inside by `decide`) and inside the range. -/
theorem wrapping_nur_exakt_kein_mod8 :
    ¬ ∃ _f : Zahl 0 5 → Zahl 0 5 → Zahl 0 5,
      (∀ a b : Zahl 0 5, a.n + b.n ≤ 5 → (_f a b).n = a.n + b.n) ∧
      (∀ a b : Zahl 0 5, (_f a b).n = (a.n + b.n) % 8) := by
  intro hEx
  obtain ⟨f, _, hfmod⟩ := hEx
  have h3 : (f ⟨3, by decide, by decide⟩ ⟨3, by decide, by decide⟩).n =
      ((3 : Int) + 3) % 8 := hfmod _ _
  have hle := (f ⟨3, by decide, by decide⟩ ⟨3, by decide, by decide⟩).le_hi
  have h6 : ((3 : Int) + 3) % 8 = 6 := by decide
  rw [h6] at h3
  omega

/-! ## No wrapping function on `0 .. 5` computed by `mod 2^k` -/

/-- The strong statement (PLAN-BITS section 4): there is no total function
    `Zahl 0 5 → Zahl 0 5 → Zahl 0 5` that agrees with `+` whenever the sum
    fits AND is computed by `mod 2^k` for some `k` (the modulus is carried
    as `2 ^ (k + 1)`, so no `Nat` truncation can turn `k = 0` into a
    silently wrong bound). All numeral facts are proved inside by
    `decide`; the uniform tail fact `10 % 2^(k+4) = 10` is proved inside by
    `Int.emod_eq_of_lt` with `10 < 2^(k+4)` from `Nat.pow_le_pow_right`.
    Case plan, with the escaping pair per modulus:
    `k = 0` (`mod 2`): `f 1 2 = 3` by fit, `3 % 2 = 1` by mod;
    `k = 1` (`mod 4`): `f 2 3 = 5` by fit, `5 % 4 = 1`;
    `k = 2` (`mod 8`): `f 3 3` is `6 % 8 = 6`, outside the range;
    `k ≥ 3` (`mod 2^(k+1) ≥ 16`): `f 5 5` is `10 % 2^(k+1) = 10`,
    outside the range. -/
theorem wrapping_nur_exakt :
    ¬ ∃ _f : Zahl 0 5 → Zahl 0 5 → Zahl 0 5,
      (∀ a b : Zahl 0 5, a.n + b.n ≤ 5 → (_f a b).n = a.n + b.n) ∧
      ∃ k : Nat, ∀ a b : Zahl 0 5, (_f a b).n = (a.n + b.n) % 2 ^ (k + 1) := by
  have h1 : ((1 : Int) + 2) % 2 ^ (0 + 1) = 1 := by decide
  have h5mod4 : ((2 : Int) + 3) % 2 ^ ((0 + 1) + 1) = 1 := by decide
  have h6mod8 : ((3 : Int) + 3) % 2 ^ (((0 + 1) + 1) + 1) = 6 := by decide
  have h10nowrap : ∀ k : Nat, ((5 : Int) + 5) % 2 ^ (k + 1 + 1 + 1 + 1) = 10 := by
    intro k
    have e : ((5 : Int) + 5) = 10 := by decide
    rw [e]
    apply Int.emod_eq_of_lt (by decide)
    have hN := Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show 4 ≤ k + 1 + 1 + 1 + 1 by omega)
    have hle16 : ((2 ^ 4 : Nat) : Int) ≤ ((2 ^ (k + 1 + 1 + 1 + 1) : Nat) : Int) :=
      Int.ofNat_le.mpr hN
    have e1 : ((2 ^ 4 : Nat) : Int) = 16 := by decide
    have e2 : ((2 ^ (k + 1 + 1 + 1 + 1) : Nat) : Int) =
        (2 : Int) ^ (k + 1 + 1 + 1 + 1) := by simp
    omega
  intro hEx
  obtain ⟨f, hfit, k, hmodf⟩ := hEx
  cases k with
  | zero =>
    have hfit12 := hfit ⟨1, by decide, by decide⟩ ⟨2, by decide, by decide⟩
      (by decide)
    have hmod12 := hmodf ⟨1, by decide, by decide⟩ ⟨2, by decide, by decide⟩
    rw [h1] at hmod12
    have hfit12n : (f ⟨1, by decide, by decide⟩ ⟨2, by decide, by decide⟩).n =
        (1 : Int) + 2 := hfit12
    omega
  | succ k =>
    cases k with
    | zero =>
      have hfit23 := hfit ⟨2, by decide, by decide⟩ ⟨3, by decide, by decide⟩
        (by decide)
      have hmod23 := hmodf ⟨2, by decide, by decide⟩ ⟨3, by decide, by decide⟩
      rw [h5mod4] at hmod23
      have hfit23n : (f ⟨2, by decide, by decide⟩ ⟨3, by decide, by decide⟩).n =
          (2 : Int) + 3 := hfit23
      omega
    | succ k =>
      cases k with
      | zero =>
        have hmod33 := hmodf ⟨3, by decide, by decide⟩ ⟨3, by decide, by decide⟩
        have hle33 := (f ⟨3, by decide, by decide⟩ ⟨3, by decide, by decide⟩).le_hi
        rw [h6mod8] at hmod33
        omega
      | succ k =>
        have hmod55 := hmodf ⟨5, by decide, by decide⟩ ⟨5, by decide, by decide⟩
        have hle55 := (f ⟨5, by decide, by decide⟩ ⟨5, by decide, by decide⟩).le_hi
        have h10 := h10nowrap k
        rw [h10] at hmod55
        omega

/- CUTS: what is not proved.
   - `shlW` has a definition only; the C-equality cast bridge is proved for
     `addW`, `subW`, `mulW`.
   - `addS` on the empty range (`hi < lo`) returns `a` by convention; no
     claim is made about that leg beyond inhabitation.
-/

#print axioms Gabbro.Grammatik.zweiPow_pos
#print axioms Gabbro.Grammatik.clamp_monoton
#print axioms Gabbro.Grammatik.Zahl.addS_n
#print axioms Gabbro.Grammatik.addS_monoton
#print axioms Gabbro.Grammatik.addS_exakt_wenn_passt
#print axioms Gabbro.Grammatik.addS_exakt_wenn_passt_zeuge
#print axioms Gabbro.Grammatik.addW_c_gleich
#print axioms Gabbro.Grammatik.subW_c_gleich
#print axioms Gabbro.Grammatik.mulW_c_gleich
#print axioms Gabbro.Grammatik.wrapping_nur_exakt
#print axioms Gabbro.Grammatik.wrapping_nur_exakt_kein_mod8

end Gabbro.Grammatik
