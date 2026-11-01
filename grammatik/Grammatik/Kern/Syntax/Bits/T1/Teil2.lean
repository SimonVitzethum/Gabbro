module

public import Grammatik.Kern.Syntax.Typen.Teil2
public import Grammatik.Kern.Syntax.Bits.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik

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
  simp only [bswap16n, Nat.reducePow, gt_iff_lt]
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


end Gabbro.Grammatik
