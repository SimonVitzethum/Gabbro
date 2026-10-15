/-
  File:      Grammatik/X86/ByteSwap.lean
  Subject:   Canonical 32/64-bit byte-swap helpers (lane 420).

  Pure byte-permutation value helpers over the canonical `Wort`
  (`Grammatik/X86/Typen.lean`), reusing `wortByte` from `Speicher.lean`.
  No `Befehl` constructor, no codec bytes, no `schritt` change, no
  source correspondence is claimed here; see CUTS.
-/
import Grammatik.X86.Speicher
import Grammatik.Bits

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Canonical 64-bit byte reversal (future BSWAP r64 value shape). -/
def bswap64 (v : Wort) : Wort :=
  BitVec.ofNat 64 ((wortByte v 7).toNat + (wortByte v 6).toNat * 256 +
    (wortByte v 5).toNat * 65536 + (wortByte v 4).toNat * 16777216 +
    (wortByte v 3).toNat * 4294967296 +
    (wortByte v 2).toNat * 1099511627776 +
    (wortByte v 1).toNat * 281474976710656 +
    (wortByte v 0).toNat * 72057594037927936)

/-- Every canonical byte value fits in eight bits. -/
theorem wortByte_lt (v : Wort) (i : Nat) : (wortByte v i).toNat < 256 := by
  unfold wortByte
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_lt _ (by decide)

/-- Canonical 32-bit byte reversal with zero extension (BSWAP r32 value
    shape: the low four bytes reverse, the upper four clear, matching the
    architectural zero-extension of 32-bit register writes). -/
def bswap32 (v : Wort) : Wort :=
  BitVec.ofNat 64 ((wortByte v 3).toNat + (wortByte v 2).toNat * 256 +
    (wortByte v 1).toNat * 65536 + (wortByte v 0).toNat * 16777216)

/-- Closed power values used to normalise byte-index arithmetic to
    literals before `omega`. Each is `rfl`: kernel evaluation only. -/
private theorem pow2_8 : (2 : Nat) ^ 8 = 256 := rfl
private theorem pow2_64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
private theorem pow256_0 : (256 : Nat) ^ 0 = 1 := rfl
private theorem pow256_1 : (256 : Nat) ^ 1 = 256 := rfl
private theorem pow256_2 : (256 : Nat) ^ 2 = 65536 := rfl
private theorem pow256_3 : (256 : Nat) ^ 3 = 16777216 := rfl
private theorem pow256_4 : (256 : Nat) ^ 4 = 4294967296 := rfl
private theorem pow256_5 : (256 : Nat) ^ 5 = 1099511627776 := rfl
private theorem pow256_6 : (256 : Nat) ^ 6 = 281474976710656 := rfl
private theorem pow256_7 : (256 : Nat) ^ 7 = 72057594037927936 := rfl

/-- Canonical bytes read back as `Nat` bytes: the eight-bit wrapper adds
    nothing. -/
theorem wortByte_byteOf (v : Wort) (k : Nat) :
    (wortByte v k).toNat = byteOf v.toNat k := by
  simp only [wortByte, byteOf, BitVec.toNat_ofNat]
  omega

/-- The 64-bit helper computes the accepted `Nat`-level `bswap64n` (from
    `Grammatik.Bits`): the `ofNat 64` wrapper adds nothing since the
    swapped value fits (by `bswap64n_lt`, rewritten to `2 ^ 64`). -/
theorem bswap64_nat (v : Wort) : (bswap64 v).toNat = bswap64n v.toNat := by
  have hlt := bswap64n_lt v.toNat
  have e8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [e8] at hlt
  simp only [bswap64, BitVec.toNat_ofNat, bswap64n, wortByte_byteOf,
    pow256_2, pow256_3, pow256_4, pow256_5, pow256_6,
    pow256_7, pow2_64] at hlt ⊢
  omega

/-- The 32-bit helper computes the accepted `Nat`-level `bswap32n`: the
    `ofNat 64` wrapper adds nothing since the swapped value fits in four
    bytes (by `bswap32n_lt`). -/
theorem bswap32_nat (v : Wort) : (bswap32 v).toNat = bswap32n v.toNat := by
  have hlt := bswap32n_lt v.toNat
  have e4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rw [e4] at hlt
  have e32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  simp only [bswap32, BitVec.toNat_ofNat, bswap32n, wortByte_byteOf,
    pow256_2, pow256_3, pow2_64, e32] at hlt ⊢
  omega

/-- Every canonical word fits in eight bytes. -/
theorem toNat_lt256_8 (v : Wort) : v.toNat < 256 ^ 8 := by
  have h := v.isLt
  have e8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  omega

/-- `Nat`-level byte projection of the 64-bit reversal, through the
    accepted split/nest lemmas of `Grammatik.Bits` (same shape as
    `bswap64n_invol` there). Uses `hx` (the value fits) and `hi` (the
    index is in range; the impossible tail past 7 is discharged by it). -/
theorem byteOf_bswap64n (x : Nat) (hx : x < 256 ^ 8) (i : Nat) (hi : i < 8) :
    byteOf (bswap64n x) i = byteOf x (7 - i) := by
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
  rw [hsplit, hswap]
  cases i with
  | zero => exact f0.trans e7.symm
  | succ n1 =>
    cases n1 with
    | zero => exact f1.trans e6.symm
    | succ n2 =>
      cases n2 with
      | zero => exact f2.trans e5.symm
      | succ n3 =>
        cases n3 with
        | zero => exact f3.trans e4.symm
        | succ n4 =>
          cases n4 with
          | zero => exact f4.trans e3.symm
          | succ n5 =>
            cases n5 with
            | zero => exact f5.trans e2.symm
            | succ n6 =>
              cases n6 with
              | zero => exact f6.trans e1.symm
              | succ n7 =>
                cases n7 with
                | zero => exact f7.trans e0.symm
                | succ n8 => exact absurd hi (by omega)

/-- Byte projection of the 64-bit reversal: byte `i` of the result is
    byte `7 - i` of the operand. Uses `hi` (the index is in range). -/
theorem wortByte_bswap64 (v : Wort) (i : Nat) (hi : i < 8) :
    wortByte (bswap64 v) i = wortByte v (7 - i) := by
  have hx := toNat_lt256_8 v
  have h := byteOf_bswap64n v.toNat hx i hi
  apply BitVec.eq_of_toNat_eq
  simp only [wortByte_byteOf, bswap64_nat]
  exact h

/-- The 64-bit reversal is an involution, through the accepted
    `bswap64n_invol`. -/
theorem bswap64_invol (v : Wort) : bswap64 (bswap64 v) = v := by
  apply BitVec.eq_of_toNat_eq
  have hx := toNat_lt256_8 v
  have hinv := bswap64n_invol v.toNat hx
  calc (bswap64 (bswap64 v)).toNat
      = bswap64n (bswap64 v).toNat := bswap64_nat (bswap64 v)
    _ = bswap64n (bswap64n v.toNat) := by rw [bswap64_nat v]
    _ = v.toNat := hinv

/-- The 32-bit value in nested packet form over canonical bytes. -/
theorem bswap32_nest_wort (v : Wort) : (bswap32 v).toNat =
    (((wortByte v 0).toNat * 256 + (wortByte v 1).toNat) * 256
      + (wortByte v 2).toNat) * 256 + (wortByte v 3).toNat := by
  have h0 : (wortByte v 0).toNat = byteOf v.toNat 0 := wortByte_byteOf v 0
  have h1 : (wortByte v 1).toNat = byteOf v.toNat 1 := wortByte_byteOf v 1
  have h2 : (wortByte v 2).toNat = byteOf v.toNat 2 := wortByte_byteOf v 2
  have h3 : (wortByte v 3).toNat = byteOf v.toNat 3 := wortByte_byteOf v 3
  rw [bswap32_nat]
  simp only [bswap32n]
  rw [← h0, ← h1, ← h2, ← h3]
  omega

/-- `Nat`-level byte projection of the 32-bit reversal, through the
    accepted split/nest lemmas (same shape as `bswap32n_invol` in
    `Grammatik.Bits`). Uses `hx` (the value fits in four bytes) and `hi`
    (the index is in range; the impossible tail past 3 is discharged
    by it). -/
theorem byteOf_bswap32n (x : Nat) (hx : x < 256 ^ 4) (i : Nat) (hi : i < 4) :
    byteOf (bswap32n x) i = byteOf x (3 - i) := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, hsplit⟩ := split4 x hx
  obtain ⟨e0, e1, e2, e3⟩ := byteOf_nest b0 b1 b2 b3 h0 h1 h2 h3
  have hswap : bswap32n (((b3 * 256 + b2) * 256 + b1) * 256 + b0)
      = ((b0 * 256 + b1) * 256 + b2) * 256 + b3 := by
    simp only [bswap32n, e0, e1, e2, e3]
    exact bswap32n_nest b0 b1 b2 b3
  obtain ⟨g0, g1, g2, g3⟩ := byteOf_nest b3 b2 b1 b0 h3 h2 h1 h0
  rw [hsplit, hswap]
  cases i with
  | zero => exact g0.trans e3.symm
  | succ n1 =>
    cases n1 with
    | zero => exact g1.trans e2.symm
    | succ n2 =>
      cases n2 with
      | zero => exact g2.trans e1.symm
      | succ n3 =>
        cases n3 with
        | zero => exact g3.trans e0.symm
        | succ n4 => exact absurd hi (by omega)

/-- Low byte projection of the 32-bit reversal: byte `i` of the result
    is byte `3 - i` of the operand. Uses `hi` (the index is in range). -/
theorem wortByte_bswap32_lo (v : Wort) (i : Nat) (hi : i < 4) :
    wortByte (bswap32 v) i = wortByte v (3 - i) := by
  have h0 := wortByte_lt v 0
  have h1 := wortByte_lt v 1
  have h2 := wortByte_lt v 2
  have h3 := wortByte_lt v 3
  have hval := bswap32_nest_wort v
  have hbytes := byteOf_nest (wortByte v 3).toNat (wortByte v 2).toNat
    (wortByte v 1).toNat (wortByte v 0).toNat h3 h2 h1 h0
  obtain ⟨g0, g1, g2, g3⟩ := hbytes
  simp only [wortByte_byteOf] at g0 g1 g2 g3
  cases i with
  | zero =>
      show wortByte (bswap32 v) 0 = wortByte v 3
      apply BitVec.eq_of_toNat_eq
      simp only [wortByte_byteOf, hval]
      exact g0
  | succ n1 =>
    cases n1 with
    | zero =>
        show wortByte (bswap32 v) 1 = wortByte v 2
        apply BitVec.eq_of_toNat_eq
        simp only [wortByte_byteOf, hval]
        exact g1
    | succ n2 =>
      cases n2 with
      | zero =>
          show wortByte (bswap32 v) 2 = wortByte v 1
          apply BitVec.eq_of_toNat_eq
          simp only [wortByte_byteOf, hval]
          exact g2
      | succ n3 =>
        cases n3 with
        | zero =>
            show wortByte (bswap32 v) 3 = wortByte v 0
            apply BitVec.eq_of_toNat_eq
            simp only [wortByte_byteOf, hval]
            exact g3
        | succ n4 => exact absurd hi (by omega)

/-- Upper bytes of the 32-bit reversal are clear (zero extension): byte
    `i` is `0` for `4 ≤ i`. Uses `hlo` (lower bound) and `hi` (upper
    bound; the impossible tail past 7 is discharged by it). -/
theorem wortByte_bswap32_hi (v : Wort) (i : Nat) (hlo : 4 ≤ i) (hi : i < 8) :
    wortByte (bswap32 v) i = 0 := by
  have hval := bswap32_nest_wort v
  have hlt : (((wortByte v 0).toNat * 256 + (wortByte v 1).toNat) * 256 + (wortByte v 2).toNat) * 256 + (wortByte v 3).toNat < 4294967296 := by
    have h4 := bswap32n_lt v.toNat
    have e4 : (256 : Nat) ^ 4 = 4294967296 := by decide
    rw [e4] at h4
    rw [← hval, bswap32_nat]
    exact h4
  have hz : (0 : Byte).toNat = 0 := rfl
  have e4 : (256 : Nat) ^ 4 = 4294967296 := by decide
  obtain ⟨j, hj⟩ : ∃ j, i = 4 + j := ⟨i - 4, by omega⟩
  subst hj
  cases j with
  | zero =>
      show wortByte (bswap32 v) 4 = 0
      apply BitVec.eq_of_toNat_eq
      rw [wortByte_byteOf (bswap32 v) 4, hval]
      simp only [byteOf, e4]
      omega
  | succ n1 =>
    cases n1 with
    | zero =>
        show wortByte (bswap32 v) 5 = 0
        apply BitVec.eq_of_toNat_eq
        rw [wortByte_byteOf (bswap32 v) 5, hval]
        simp only [byteOf, pow256_5]
        omega
    | succ n2 =>
      cases n2 with
      | zero =>
          show wortByte (bswap32 v) 6 = 0
          apply BitVec.eq_of_toNat_eq
          rw [wortByte_byteOf (bswap32 v) 6, hval]
          simp only [byteOf, pow256_6]
          omega
      | succ n3 =>
        cases n3 with
        | zero =>
            show wortByte (bswap32 v) 7 = 0
            apply BitVec.eq_of_toNat_eq
            rw [wortByte_byteOf (bswap32 v) 7, hval]
            simp only [byteOf, pow256_7]
            omega
        | succ n4 => exact absurd hi (by omega)

/-- The 32-bit reversal zero-extends: its value fits in four bytes. -/
theorem bswap32_zeroExt (v : Wort) : (bswap32 v).toNat < 2 ^ 32 := by
  have hlt := bswap32n_lt v.toNat
  have e4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
  rw [e4] at hlt
  rw [bswap32_nat v]
  exact hlt

/-- The 32-bit reversal is an involution on values that fit in four
    bytes, through the accepted `bswap32n_invol`. Uses `hv` (the value
    fits; without it the upper bytes are cleared and the round trip
    would not hold). -/
theorem bswap32_invol_bounded (v : Wort) (hv : v.toNat < 2 ^ 32) :
    bswap32 (bswap32 v) = v := by
  apply BitVec.eq_of_toNat_eq
  have hx : v.toNat < 256 ^ 4 := by
    have e4 : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
    omega
  have hinv := bswap32n_invol v.toNat hx
  calc (bswap32 (bswap32 v)).toNat
      = bswap32n (bswap32 v).toNat := bswap32_nat (bswap32 v)
    _ = bswap32n (bswap32n v.toNat) := by rw [bswap32_nat v]
    _ = v.toNat := hinv

/-- Byte-order store correspondence: storing the 64-bit reversal writes
    the operand's bytes in reverse order, through the actual `write64`.
    Uses `hwr` (the store succeeds) and `hk` (the index is in range). -/
theorem bswap64_store_bytes (m : Speicher) (a : Adresse) (v : Wort)
    (m' : Speicher) (hwr : write64 m a (bswap64 v) = some m')
    (k : Nat) (hk : k < 8) :
    m'.bytes (addrOff a k) = wortByte v (7 - k) := by
  unfold write64 at hwr
  by_cases hc : schreibbar8 m a = true
  · rw [if_pos hc] at hwr
    cases hwr
    show writeBytes m a (bswap64 v) (addrOff a k) = _
    unfold writeBytes
    rw [writeBytesN_hit m a (bswap64 v) 8 k hk (Nat.le_refl 8)]
    exact wortByte_bswap64 v k hk
  · rw [if_neg hc] at hwr
    cases hwr

/-- Read-back of a stored 64-bit reversal, through the actual `read64`. -/
theorem read64_nach_bswap64 (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write64 m a (bswap64 v) = some m')
    (hrd : lesbar8 m a = true) :
    read64 m' a = some (bswap64 v) :=
  read64_nach_write64 m m' a (bswap64 v) hwr hrd

/-- A stored 64-bit reversal changes nothing outside its footprint. -/
theorem bswap64_write_rahmen (m m' : Speicher) (a x : Adresse) (v : Wort)
    (hwr : write64 m a (bswap64 v) = some m')
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x :=
  write64_rahmen m m' a x (bswap64 v) hwr haussen

/-- A read at a disjoint footprint survives a stored 64-bit reversal. -/
theorem bswap64_read_rahmen (m m' : Speicher) (a b : Adresse) (v : Wort)
    (hwr : write64 m a (bswap64 v) = some m') (hdis : Disjunkt a b) :
    read64 m' b = read64 m b :=
  read64_rahmen m m' a b (bswap64 v) hwr hdis

/-- Read-back of a stored 32-bit reversal, through the actual `read32`:
    the low four bytes hold the reversed value with zero extension. -/
theorem read32_nach_bswap32 (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write32 m a (bswap32 v) = some m')
    (hrd : lesbarN m a 4 = true) :
    read32 m' a = some (bswap32 v) := by
  have h := read32_nach_write32 m m' a (bswap32 v) hwr hrd
  have hz : (bswap32 v).toNat % 4294967296 = (bswap32 v).toNat := by
    have hzx := bswap32_zeroExt v
    have e32 : (2 : Nat) ^ 32 = 4294967296 := by decide
    omega
  have hof : BitVec.ofNat 64 (bswap32 v).toNat = bswap32 v := by
    apply BitVec.eq_of_toNat_eq
    have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    simp only [BitVec.toNat_ofNat, e64]
    have hzx := bswap32_zeroExt v
    have e32 : (2 : Nat) ^ 32 = 4294967296 := by decide
    omega
  rw [hz, hof] at h
  exact h

/-! ## Flag preservation at the intended target interface.

    BSWAP leaves every architectural flag unchanged. The value helpers
    therefore pair with the incoming snapshot; a future native form must
    thread `Flags` through untouched (no flag is set, cleared, or left
    undefined by the swap). -/

/-- Flag threading for a future 64-bit native form. -/
def bswap64f (v : Wort) (f : Flags) : Wort × Flags := (bswap64 v, f)

/-- The 64-bit snapshot passes through unchanged, with the swapped value. -/
theorem bswap64f_wert_flags (v : Wort) (f : Flags) :
    (bswap64f v f).1 = bswap64 v ∧ (bswap64f v f).2 = f :=
  ⟨rfl, rfl⟩

/-- Flag threading for a future 32-bit native form. -/
def bswap32f (v : Wort) (f : Flags) : Wort × Flags := (bswap32 v, f)

/-- The 32-bit snapshot passes through unchanged, with the swapped value. -/
theorem bswap32f_wert_flags (v : Wort) (f : Flags) :
    (bswap32f v f).1 = bswap32 v ∧ (bswap32f v f).2 = f :=
  ⟨rfl, rfl⟩

/-! ## Width refusal: no invented 16-bit (or 8-bit) form.

    x86 has BSWAP r32/r64 only. The dispatch maps exactly those widths
    to helpers and refuses everything else, so no 16-bit value shape is
    invented here. -/

/-- Width-indexed value dispatch for a future native form. -/
def bswapBreite : Breite → Option (Wort → Wort)
  | .b32 => some bswap32
  | .b64 => some bswap64
  | _ => none

/-- Eight bits have no byte order to reverse: refused. -/
theorem bswapBreite_b8 : bswapBreite .b8 = none := rfl

/-- Sixteen bits have no native BSWAP form: refused, nothing invented. -/
theorem bswapBreite_b16 : bswapBreite .b16 = none := rfl

/-- Thirty-two bits dispatch to the zero-extending helper. -/
theorem bswapBreite_b32 : bswapBreite .b32 = some bswap32 := rfl

/-- Sixty-four bits dispatch to the full reversal. -/
theorem bswapBreite_b64 : bswapBreite .b64 = some bswap64 := rfl

/-! ## Concrete probes and joint memory witnesses.

    All probes run on the nonzero witness word `0x0102030405060708`
    (every byte distinct) over the fully permissive `zeugenSpeicher`
    from `Speicher.lean`. The memory witnesses store through the actual
    `write64`/`write32`, read back through the actual `read64`/`read32`,
    and observably change memory. -/

/-- Witness word: every byte distinct. -/
def bswapZeugenWort : Wort := BitVec.ofNat 64 0x0102030405060708

/-- Witness memory after storing the 64-bit reversal at address zero. -/
def bswapZeugenNach64 : Speicher :=
  { zeugenSpeicher with bytes := (writeBytes zeugenSpeicher 0 (bswap64 bswapZeugenWort)) }

/-- Witness memory after storing the 32-bit reversal at address zero. -/
def bswapZeugenNach32 : Speicher :=
  { zeugenSpeicher with bytes := (writeBytesN zeugenSpeicher 0 (bswap32 bswapZeugenWort) 4) }

/-- The witness is nonzero. -/
theorem bswapZeuge_ne : bswapZeugenWort ≠ 0 := by
  decide

/-- 64-bit reversal of the witness value. -/
theorem probe_bswap64_wert :
    bswap64 bswapZeugenWort = BitVec.ofNat 64 0x0807060504030201 := by
  decide

/-- 32-bit reversal of the witness value (low bytes reversed, zero
    extended). -/
theorem probe_bswap32_wert :
    bswap32 bswapZeugenWort = BitVec.ofNat 64 0x08070605 := by
  decide

/-- A value with only high bytes set swaps to zero: the upper bytes do
    not survive the 32-bit form. -/
theorem probe_bswap32_verwirft_oben :
    bswap32 0xFFFFFFFF00000000 = 0 := by
  decide

/-- Double 64-bit reversal of the witness is the witness. -/
theorem probe_bswap64_invol :
    bswap64 (bswap64 bswapZeugenWort) = bswapZeugenWort :=
  bswap64_invol bswapZeugenWort

/-- A stored 64-bit reversal goes through, reads back, and observably
    changes memory (base byte `0x00` becomes `0x01`). -/
theorem probe_bswap64_speicher :
    ∃ (m m' : Speicher) (a : Adresse),
      write64 m a (bswap64 bswapZeugenWort) = some m' ∧
      read64 m' a = some (bswap64 bswapZeugenWort) ∧
      m.bytes a ≠ m'.bytes a := by
  refine ⟨zeugenSpeicher, bswapZeugenNach64, 0, ?_, ?_, ?_⟩
  · unfold write64
    have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
    exact if_pos hc
  · exact read64_nach_bswap64 zeugenSpeicher _ 0 bswapZeugenWort
      (by unfold write64
          have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
          exact if_pos hc) rfl
  · have hhit := writeBytesN_hit zeugenSpeicher 0 (bswap64 bswapZeugenWort)
      8 0 (by decide) (by decide)
    rw [addrOff_null] at hhit
    have hproj := wortByte_bswap64 bswapZeugenWort 0 (by decide)
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0
      (bswap64 bswapZeugenWort) 0
    unfold writeBytes
    rw [hhit, hproj]
    decide

/-- Two concrete footprints are disjoint (alias witness with explicit
    no-wrap bounds). -/
theorem probe_disjunkt : Disjunkt 0 4096 :=
  disjunkt_von_intervallen 0 4096 (by unfold OhneUmbruch; decide)
    (by unfold OhneUmbruch; decide) (by decide)

/-- A stored 64-bit reversal leaves a disjoint footprint's read
    untouched while changing its own (aliasing + change, jointly). -/
theorem probe_bswap64_alias :
    ∃ (m m' : Speicher),
      write64 m 0 (bswap64 bswapZeugenWort) = some m' ∧
      read64 m' 4096 = read64 m 4096 ∧
      m.bytes 0 ≠ m'.bytes 0 := by
  refine ⟨zeugenSpeicher, bswapZeugenNach64, ?_, ?_, ?_⟩
  · unfold write64
    have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
    exact if_pos hc
  · exact bswap64_read_rahmen zeugenSpeicher _ 0 4096 bswapZeugenWort
      (by unfold write64
          have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
          exact if_pos hc) probe_disjunkt
  · have hhit := writeBytesN_hit zeugenSpeicher 0 (bswap64 bswapZeugenWort)
      8 0 (by decide) (by decide)
    rw [addrOff_null] at hhit
    have hproj := wortByte_bswap64 bswapZeugenWort 0 (by decide)
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0
      (bswap64 bswapZeugenWort) 0
    unfold writeBytes
    rw [hhit, hproj]
    decide

/-- A stored 32-bit reversal reads back through the actual `read32`. -/
theorem probe_bswap32_speicher :
    ∃ (m m' : Speicher) (a : Adresse),
      write32 m a (bswap32 bswapZeugenWort) = some m' ∧
      read32 m' a = some (bswap32 bswapZeugenWort) := by
  refine ⟨zeugenSpeicher, bswapZeugenNach32, 0, ?_, ?_⟩
  · unfold write32
    have hc : schreibbarN zeugenSpeicher 0 4 = true := rfl
    exact if_pos hc
  · exact read32_nach_bswap32 zeugenSpeicher _ 0 bswapZeugenWort
      (by unfold write32
          have hc : schreibbarN zeugenSpeicher 0 4 = true := rfl
          exact if_pos hc) rfl

/- CUTS:
    - No `Befehl` constructor, no codec bytes, no `schritt` change: this
      file is value helpers plus their memory/flag interface only. A
      future native BSWAP form must add the instruction, its encoding,
      and its step rule with these helpers as the value side; none of
      that is claimed here.
    - No source correspondence: no claim links a source `bswap` call to
      these helpers (that is the bridge lane's business).
    - No 16-bit (or 8-bit) value shape is provided: `bswapBreite` refuses
      `.b8`/`.b16` by `none`. The source-level `u16` intrinsic
      (`bswap16n` in `Grammatik.Bits`) is untouched.
    - No atomicity claim for multi-byte accesses under concurrency: the
      store/load lemmas are sequential over one `Speicher` (per-access
      TSO granularity stays with the TSO-bridge lane).
    - No timing, cost, or physical-hardware claim.
    - Flag preservation is stated as pure value/flag threading
      (`bswap64f`/`bswap32f`); no flag snapshot of a machine step is
      claimed.
    - `bswap32` is an involution only on values that fit in four bytes
      (`bswap32_invol_bounded` states the bound); the upper bytes are
      cleared, never preserved.
-/

#print axioms bswap64_invol
#print axioms bswap32_invol_bounded
#print axioms wortByte_bswap64
#print axioms wortByte_bswap32_lo
#print axioms wortByte_bswap32_hi
#print axioms bswap64_store_bytes
#print axioms read64_nach_bswap64
#print axioms read32_nach_bswap32
#print axioms bswap64_read_rahmen
#print axioms bswap64f_wert_flags
#print axioms bswap32f_wert_flags
#print axioms probe_bswap64_speicher
#print axioms probe_bswap64_alias

end Gabbro.Grammatik.X86
