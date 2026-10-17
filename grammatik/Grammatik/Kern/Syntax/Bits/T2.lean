/- Part 2 of 3 of `Bits` (split by instrumente/teile/lean-teilen.py; the umbrella `Bits.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Bits.T1

namespace Gabbro.Grammatik

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

/-- `clz_log2`: `clz x + log2_floor x = w`, as values. -/
theorem clz_log2 (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    (Zahl.clz w x).n + (Zahl.log2_floor w x).n = (w : Int) := by
  have hb := zahlNat_bounds w x
  have h := clzn_log2n hb.1 hb.2
  show ((clzn w (zahlNat w x) : Nat) : Int)
    + ((Nat.log2 (zahlNat w x) : Nat) : Int) = (w : Int)
  have hle : ((clzn w (zahlNat w x) + Nat.log2 (zahlNat w x) : Nat) : Int)
      ≤ (w : Int) := Int.ofNat_le.mpr (Nat.le_of_eq h)
  have hge : (w : Int)
      ≤ ((clzn w (zahlNat w x) : Nat) : Int)
        + ((Nat.log2 (zahlNat w x) : Nat) : Int) := by
    have e : ((clzn w (zahlNat w x) + Nat.log2 (zahlNat w x) : Nat) : Int)
        = ((clzn w (zahlNat w x) : Nat) : Int)
          + ((Nat.log2 (zahlNat w x) : Nat) : Int) := by simp
    omega
  omega

/-- `ctz_spez`: `2 ^ r ∣ x` and `¬ 2 ^ (r+1) ∣ x` for `r = ctz x`. -/
theorem ctz_spez (w : Nat) (x : Zahl 1 ((2 : Int) ^ (w + 1) - 1)) :
    ((2 : Int) ^ ctzn w (zahlNat w x)) ∣ x.n
      ∧ ¬ ((2 : Int) ^ (ctzn w (zahlNat w x) + 1)) ∣ x.n := by
  have hb := zahlNat_bounds w x
  obtain ⟨hdvd, hnd⟩ := ctzn_spez hb.1 hb.2
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have h2n : (x.n.toNat : Int) = x.n := Int.toNat_of_nonneg hnn
  have hval : x.n.toNat = zahlNat w x := rfl
  constructor
  · have hcast : ((2 ^ ctzn w (zahlNat w x) : Nat) : Int)
        = (2 : Int) ^ ctzn w (zahlNat w x) := by simp
    have h1 : ((2 ^ ctzn w (zahlNat w x) : Nat) : Int)
        ∣ ((zahlNat w x : Nat) : Int) := Int.natCast_dvd_natCast.mpr hdvd
    rw [hcast, ← hval, h2n] at h1
    exact h1
  · intro hdvdI
    apply hnd
    have hcast : ((2 ^ (ctzn w (zahlNat w x) + 1) : Nat) : Int)
        = (2 : Int) ^ (ctzn w (zahlNat w x) + 1) := by simp
    have hnat : ((2 ^ (ctzn w (zahlNat w x) + 1) : Nat) : Int)
        ∣ ((x.n.toNat : Nat) : Int) := by
      rw [hcast, h2n]
      exact hdvdI
    have hnat2 : 2 ^ (ctzn w (zahlNat w x) + 1) ∣ x.n.toNat :=
      Int.natCast_dvd_natCast.mp hnat
    rw [hval] at hnat2
    exact hnat2

/-- `popcount_rotl`: popcount is invariant under rotation, as values. -/
theorem popcount_rotl (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) :
    (Zahl.popcount w (Zahl.rotl w x s)).n = (Zahl.popcount w x).n := by
  have hs : s.n.toNat ≤ w := zahlAmt_le w s
  have hx : x.n.toNat < 2 ^ (w + 1) := zahlFull_bounds w x
  have h := popcountn_rotln w s.n.toNat x.n.toNat hs hx
  show ((popcountn w (rotln w s.n.toNat x.n.toNat) : Nat) : Int)
    = ((popcountn w x.n.toNat : Nat) : Int)
  rw [h]

/-- `rotl_rotr`: `rotr ∘ rotl = id`, as values. -/
theorem rotl_rotr (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) :
    (Zahl.rotr w (Zahl.rotl w x s) s).n = x.n := by
  have hs : s.n.toNat ≤ w := zahlAmt_le w s
  have hx : x.n.toNat < 2 ^ (w + 1) := zahlFull_bounds w x
  have hnn : 0 ≤ x.n := by have := x.lo_le; omega
  have h2n : (x.n.toNat : Int) = x.n := Int.toNat_of_nonneg hnn
  have h := rotrn_rotln w s.n.toNat x.n.toNat hs hx
  show ((rotrn w s.n.toNat (rotln w s.n.toNat x.n.toNat) : Nat) : Int) = x.n
  rw [h, h2n]


end Gabbro.Grammatik
