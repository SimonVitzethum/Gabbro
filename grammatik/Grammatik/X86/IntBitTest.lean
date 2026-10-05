/-
  File:      Grammatik/X86/IntBitTest.lean
  Subject:   Bit test family BT/BTS/BTR/BTC over canonical words,
             connected to the coherent machine.

  Lane 1277: BT/BTS/BTR/BTC (0F A3/AB/B3/BB, 0F BA /4../7 ib) on
  registers (bit offset modulo width) and on memory with a register
  bit offset (signed offset moves the effective address; exact
  footprint as TSO byte events; LOCK-prefixed memory refused).
  CF = selected bit, OF/SF/AF/PF undefined (free, never false),
  ZF unaffected. Widths 16/32/64 (no 8-bit form exists: refused).
  Structure follows ShiftCodec (decode/encode/round-trip/value/step)
  and HwMulDivWidth (dispatcher preferring decodeExt, HwAdapter
  register plug, two-core witness). No hardware correspondence is
  claimed beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.NarrowOps

namespace Gabbro.Grammatik.X86

/-- The four bit-test operations. -/
inductive BtOp where
  | bt | bts | btr | btc
  deriving DecidableEq, Repr

/-- Register-form opcode: 0F A3/AB/B3/BB. -/
def btOpcode : BtOp → Nat
  | .bt => 163 | .bts => 171 | .btr => 179 | .btc => 187

/-- Group digit in 0F BA /4../7. -/
def btGruppe : BtOp → Nat
  | .bt => 4 | .bts => 5 | .btr => 6 | .btc => 7

/-- Opcode pins: the four SDM second-opcode bytes. -/
theorem pin_bt_opcode :
    btOpcode .bt = 163 ∧ btOpcode .bts = 171 ∧
    btOpcode .btr = 179 ∧ btOpcode .btc = 187 := by
  decide

/-! ## 1. Widths, bit index, selected bit, raw value.

    Widths 16/32/64 as the architecture defines them: there is no
    8-bit BT form (SDM: operand sizes 16/32/64), so `.b8` refuses by
    construction. The bit offset wraps modulo the width; the selected
    bit is read off the width-truncated base (like `bitGesetzt`). -/

/-- Admitted operand widths: 16/32/64. No 8-bit form exists. -/
def btBreiteOk : Breite → Bool
  | .b8 => false | .b16 => true | .b32 => true | .b64 => true

/-- The 8-bit refusal: no BT form exists at 8 bits. -/
theorem btBreiteOk_b8 : btBreiteOk .b8 = false := rfl

/-- Bit index: the offset modulo the width. -/
def btIndex (w : Breite) (off : Nat) : Nat := off % w.bits

/-- The index lies inside the width. -/
theorem btIndex_schranke (w : Breite) (off : Nat) :
    btIndex w off < w.bits := by
  unfold btIndex
  exact Nat.mod_lt off (by cases w <;> decide)

/-- Selected bit of the width-truncated base at the wrapped offset. -/
def btBit (w : Breite) (base : Wort) (off : Nat) : Bool :=
  (trunc w base).toNat.testBit (btIndex w off)

/-- One-bit mask at the wrapped index. -/
def btMaske (w : Breite) (off : Nat) : Wort :=
  BitVec.ofNat 64 (2 ^ btIndex w off)

/-- Raw new value: BT keeps, BTS sets, BTR clears, BTC complements. -/
def btRoh (op : BtOp) (w : Breite) (base : Wort) (off : Nat) : Wort :=
  match op with
  | .bt => base
  | .bts => base ||| btMaske w off
  | .btr => base &&& ~~~(btMaske w off)
  | .btc => if btBit w base off then base &&& ~~~(btMaske w off)
      else base ||| btMaske w off

/-- Architectural write-back: 8/16-bit merge, 32-bit zero-extends
    (the accepted `mergeRegNarrow`, reused unchanged). -/
def btSchreibe (w : Breite) (oldVal raw : Wort) : Wort :=
  mergeRegNarrow w oldVal raw

/-- A 32-bit write zero-extends like the accepted narrow merge. -/
theorem btSchreibe_b32 (oldVal raw : Wort) :
    btSchreibe .b32 oldVal raw = trunc .b32 raw := rfl

/-- A 64-bit write is whole like the accepted narrow merge. -/
theorem btSchreibe_b64 (oldVal raw : Wort) :
    btSchreibe .b64 oldVal raw = raw := rfl

/-! ## 2. Mask bit facts (core `Nat.testBit` lemmas only). -/

/-- The mask names its own bit. -/
theorem btMaske_bit_gleich (idx : Nat) : (2 ^ idx).testBit idx = true := by
  induction idx with
  | zero => decide
  | succ k ih =>
    show (2 ^ Nat.succ k).testBit (Nat.succ k) = true
    rw [Nat.testBit_succ]
    have e : 2 ^ Nat.succ k / 2 = 2 ^ k := by
      rw [Nat.pow_succ]
      exact Nat.mul_div_cancel _ (by decide)
    rw [e, ih]

/-- The mask names no other bit. -/
theorem btMaske_bit_anders (idx j : Nat) (h : idx ≠ j) :
    (2 ^ idx).testBit j = false :=
  Nat.testBit_two_pow_of_ne h

/-! ## 3. Set/reset/complement laws and CF = old bit.

    Proved through `getLsbD` (the accepted ArchitecturalFlags bridge:
    `testBit_toNat`, `getLsbD_and/or/not/ofNat`), so undefined flags
    never enter the value argument. -/

/-- The width mask covers the selected index. -/
theorem btMasken_bit (w : Breite) (off : Nat) :
    (maske w).getLsbD (btIndex w off) = true := by
  cases w with
  | b8 =>
    have hi : btIndex .b8 off < 8 := btIndex_schranke _ _
    have d : decide (btIndex .b8 off < 8) = true := decide_eq_true hi
    have d64 : decide (btIndex .b8 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b8 = BitVec.ofNat 64 (2 ^ 8 - 1) := by decide
    rw [m]
    simp only [BitVec.getLsbD_ofNat, d64, Bool.true_and,
      Nat.testBit_two_pow_sub_one]
    exact d
  | b16 =>
    have hi : btIndex .b16 off < 16 := btIndex_schranke _ _
    have d : decide (btIndex .b16 off < 16) = true := decide_eq_true hi
    have d64 : decide (btIndex .b16 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b16 = BitVec.ofNat 64 (2 ^ 16 - 1) := by decide
    rw [m]
    simp only [BitVec.getLsbD_ofNat, d64, Bool.true_and,
      Nat.testBit_two_pow_sub_one]
    exact d
  | b32 =>
    have hi : btIndex .b32 off < 32 := btIndex_schranke _ _
    have d : decide (btIndex .b32 off < 32) = true := decide_eq_true hi
    have d64 : decide (btIndex .b32 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b32 = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
    rw [m]
    simp only [BitVec.getLsbD_ofNat, d64, Bool.true_and,
      Nat.testBit_two_pow_sub_one]
    exact d
  | b64 =>
    have hi : btIndex .b64 off < 64 := btIndex_schranke _ _
    have d : decide (btIndex .b64 off < 64) = true := decide_eq_true hi
    have m : maske .b64 = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
    rw [m]
    simp only [BitVec.getLsbD_ofNat, d, Bool.true_and,
      Nat.testBit_two_pow_sub_one]

/-- BTS sets the selected bit. -/
theorem bt_bts_setzt (w : Breite) (base : Wort) (off : Nat) :
    btBit w (btSchreibe w base (btRoh .bts w base off)) off = true := by
  cases w with
  | b8 =>
    have hi : btIndex .b8 off < 8 := btIndex_schranke _ _
    have d64 : decide (btIndex .b8 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b8 = BitVec.ofNat 64 (2 ^ 8 - 1) := by decide
    have hm := btMasken_bit .b8 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b8 off) <;> rfl
  | b16 =>
    have hi : btIndex .b16 off < 16 := btIndex_schranke _ _
    have d64 : decide (btIndex .b16 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b16 = BitVec.ofNat 64 (2 ^ 16 - 1) := by decide
    have hm := btMasken_bit .b16 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b16 off) <;> rfl
  | b32 =>
    have hi : btIndex .b32 off < 32 := btIndex_schranke _ _
    have d64 : decide (btIndex .b32 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b32 = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
    have hm := btMasken_bit .b32 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b32 off) <;> rfl
  | b64 =>
    have hi : btIndex .b64 off < 64 := btIndex_schranke _ _
    have m : maske .b64 = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
    have hm := btMasken_bit .b64 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ofNat, hi, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b64 off) <;> rfl

/-- BTR clears the selected bit. -/
theorem bt_btr_loescht (w : Breite) (base : Wort) (off : Nat) :
    btBit w (btSchreibe w base (btRoh .btr w base off)) off = false := by
  cases w with
  | b8 =>
    have hi : btIndex .b8 off < 8 := btIndex_schranke _ _
    have d64 : decide (btIndex .b8 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b8 = BitVec.ofNat 64 (2 ^ 8 - 1) := by decide
    have hm := btMasken_bit .b8 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b8 off) <;> rfl
  | b16 =>
    have hi : btIndex .b16 off < 16 := btIndex_schranke _ _
    have d64 : decide (btIndex .b16 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b16 = BitVec.ofNat 64 (2 ^ 16 - 1) := by decide
    have hm := btMasken_bit .b16 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b16 off) <;> rfl
  | b32 =>
    have hi : btIndex .b32 off < 32 := btIndex_schranke _ _
    have d64 : decide (btIndex .b32 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b32 = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
    have hm := btMasken_bit .b32 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.testBit_toNat, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b32 off) <;> rfl
  | b64 =>
    have hi : btIndex .b64 off < 64 := btIndex_schranke _ _
    have m : maske .b64 = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
    have hm := btMasken_bit .b64 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.testBit_toNat, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hi, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b64 off) <;> rfl

/-- BTC complements the selected bit (CF keeps the old bit). -/
theorem bt_btc_kehrt_um (w : Breite) (base : Wort) (off : Nat) :
    btBit w (btSchreibe w base (btRoh .btc w base off)) off =
      !(btBit w base off) := by
  simp only [btRoh]
  by_cases hB : btBit w base off = true
  · rw [if_pos hB]
    have hb := bt_btr_loescht w base off
    simp only [btRoh] at hb
    rw [hb]
    cases hc : btBit w base off <;> simp_all
  · rw [if_neg hB]
    have hb := bt_bts_setzt w base off
    simp only [btRoh] at hb
    rw [hb]
    cases hc : btBit w base off <;> simp_all

/-! ## 4. Frame: every other bit is untouched.

    The width mask covers any in-range index; the one-bit mask names
    no other index (`btMaske_bit_anders`). -/

/-- The width mask covers every in-range index. -/
theorem btMasken_bit_lt (w : Breite) (j : Nat) (hj : j < w.bits) :
    (maske w).getLsbD j = true := by
  cases w with
  | b8 =>
    have hj8 : j < 8 := hj
    have dj : decide (j < 8) = true := decide_eq_true hj8
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have m : maske .b8 = BitVec.ofNat 64 (2 ^ 8 - 1) := by decide
    rw [m]
    simp only [BitVec.getLsbD_ofNat, d64j, Bool.true_and,
      Nat.testBit_two_pow_sub_one]
    exact dj
  | b16 =>
    have hj16 : j < 16 := hj
    have dj : decide (j < 16) = true := decide_eq_true hj16
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have m : maske .b16 = BitVec.ofNat 64 (2 ^ 16 - 1) := by decide
    rw [m]
    simp only [BitVec.getLsbD_ofNat, d64j, Bool.true_and,
      Nat.testBit_two_pow_sub_one]
    exact dj
  | b32 =>
    have hj32 : j < 32 := hj
    have dj : decide (j < 32) = true := decide_eq_true hj32
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have m : maske .b32 = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
    rw [m]
    simp only [BitVec.getLsbD_ofNat, d64j, Bool.true_and,
      Nat.testBit_two_pow_sub_one]
    exact dj
  | b64 =>
    have dj : decide (j < 64) = true := decide_eq_true hj
    have m : maske .b64 = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
    rw [m]
    simp only [BitVec.getLsbD_ofNat, dj, Bool.true_and,
      Nat.testBit_two_pow_sub_one]

/-- BTS frame: every other in-range bit is kept. -/
theorem bt_bts_frame (w : Breite) (base : Wort) (off j : Nat)
    (hj : j < w.bits) (hne : j ≠ btIndex w off) :
    ((btSchreibe w base (btRoh .bts w base off)) &&& maske w).getLsbD j =
      (base &&& maske w).getLsbD j := by
  cases w with
  | b8 =>
    have hj8 : j < 8 := hj
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have hM : (2 ^ btIndex .b8 off).testBit j = false :=
      btMaske_bit_anders _ _ (Ne.symm hne)
    have hMask := btMasken_bit_lt .b8 j hj
    have m : maske .b8 = BitVec.ofNat 64 (2 ^ 8 - 1) := by decide
    rw [m] at hMask ⊢
    simp only [btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64j, hMask, hM]
    cases base.getLsbD j <;> rfl
  | b16 =>
    have hj16 : j < 16 := hj
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have hM : (2 ^ btIndex .b16 off).testBit j = false :=
      btMaske_bit_anders _ _ (Ne.symm hne)
    have hMask := btMasken_bit_lt .b16 j hj
    have m : maske .b16 = BitVec.ofNat 64 (2 ^ 16 - 1) := by decide
    rw [m] at hMask ⊢
    simp only [btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64j, hMask, hM]
    cases base.getLsbD j <;> rfl
  | b32 =>
    have hj32 : j < 32 := hj
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have hM : (2 ^ btIndex .b32 off).testBit j = false :=
      btMaske_bit_anders _ _ (Ne.symm hne)
    have hMask := btMasken_bit_lt .b32 j hj
    have m : maske .b32 = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
    rw [m] at hMask ⊢
    simp only [btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ofNat, d64j, hMask, hM]
    cases base.getLsbD j <;> rfl
  | b64 =>
    have d64j : decide (j < 64) = true := decide_eq_true hj
    have hM : (2 ^ btIndex .b64 off).testBit j = false :=
      btMaske_bit_anders _ _ (Ne.symm hne)
    have hMask := btMasken_bit_lt .b64 j hj
    have m : maske .b64 = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
    rw [m] at hMask ⊢
    simp only [btSchreibe, btRoh, btMaske, mergeRegNarrow,
      BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ofNat, d64j, hMask, hM]
    cases base.getLsbD j <;> rfl

/-- BTR frame: every other in-range bit is kept. -/
theorem bt_btr_frame (w : Breite) (base : Wort) (off j : Nat)
    (hj : j < w.bits) (hne : j ≠ btIndex w off) :
    ((btSchreibe w base (btRoh .btr w base off)) &&& maske w).getLsbD j =
      (base &&& maske w).getLsbD j := by
  cases w with
  | b8 =>
    have hj8 : j < 8 := hj
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have hM : (2 ^ btIndex .b8 off).testBit j = false :=
      btMaske_bit_anders _ _ (Ne.symm hne)
    have hMask := btMasken_bit_lt .b8 j hj
    have m : maske .b8 = BitVec.ofNat 64 (2 ^ 8 - 1) := by decide
    rw [m] at hMask ⊢
    simp only [btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64j, hMask, hM]
    cases base.getLsbD j <;> rfl
  | b16 =>
    have hj16 : j < 16 := hj
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have hM : (2 ^ btIndex .b16 off).testBit j = false :=
      btMaske_bit_anders _ _ (Ne.symm hne)
    have hMask := btMasken_bit_lt .b16 j hj
    have m : maske .b16 = BitVec.ofNat 64 (2 ^ 16 - 1) := by decide
    rw [m] at hMask ⊢
    simp only [btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64j, hMask, hM]
    cases base.getLsbD j <;> rfl
  | b32 =>
    have hj32 : j < 32 := hj
    have d64j : decide (j < 64) = true := decide_eq_true (by omega)
    have hM : (2 ^ btIndex .b32 off).testBit j = false :=
      btMaske_bit_anders _ _ (Ne.symm hne)
    have hMask := btMasken_bit_lt .b32 j hj
    have m : maske .b32 = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
    rw [m] at hMask ⊢
    simp only [btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc, m,
      BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64j, hMask, hM]
    cases base.getLsbD j <;> rfl
  | b64 =>
    have d64j : decide (j < 64) = true := decide_eq_true hj
    have hM : (2 ^ btIndex .b64 off).testBit j = false :=
      btMaske_bit_anders _ _ (Ne.symm hne)
    have hMask := btMasken_bit_lt .b64 j hj
    have m : maske .b64 = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
    rw [m] at hMask ⊢
    simp only [btSchreibe, btRoh, btMaske, mergeRegNarrow,
      BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64j, hMask, hM]
    cases base.getLsbD j <;> rfl

/-- BTC frame: every other in-range bit is kept (both outcomes reuse
    the set/reset frames). -/
theorem bt_btc_frame (w : Breite) (base : Wort) (off j : Nat)
    (hj : j < w.bits) (hne : j ≠ btIndex w off) :
    ((btSchreibe w base (btRoh .btc w base off)) &&& maske w).getLsbD j =
      (base &&& maske w).getLsbD j := by
  simp only [btRoh]
  split
  · next _ => simpa [btRoh] using bt_btr_frame w base off j hj hne
  · next _ => simpa [btRoh] using bt_bts_frame w base off j hj hne

/-! ## 5. Concrete pins: offsets, values, selected bits. -/

/-- Index pins: the offset wraps modulo the width. -/
theorem probe_bt_index :
    btIndex .b16 20 = 4 ∧ btIndex .b64 70 = 6 ∧
    btIndex .b32 35 = 3 := by
  decide

/-- Value pins: set gives 8, reset gives 7, BT keeps, bits read back. -/
theorem probe_bt_werte :
    btRoh .bts .b64 0 3 = 8 ∧ btRoh .btr .b64 15 3 = 7 ∧
    btRoh .bt .b64 9 3 = 9 ∧ btBit .b64 8 3 = true ∧
    btBit .b64 7 3 = false := by
  decide

end Gabbro.Grammatik.X86
