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
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.TSO
import Grammatik.X86.HardwareExecution

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

/-! ## 6. Forms, canonical encoding, byte-parsing decoder.

    Operand widths 16/32/64 as the architecture defines them: there
    is no 8-bit BT form (SDM operand sizes 16/32/64), so the width
    type admits nothing else by construction. Canonical subset (one
    byte string per form, mirroring NarrowCodec): a REX byte is always
    present (W selects 64 vs 32, R/B extend the reg/rm registers,
    X = 0 always); 0x66 selects 16-bit (66 + REX.W refuses); 0xF0
    (LOCK) refuses -- the locked RMW stays with the locked families;
    ModRM mod = 3 is register-direct, mod = 2 is base + disp32 (with
    the SIB byte exactly when the base needs it); mod = 0/1 refuse
    (stay open). -/

/-- Admitted operand widths: 16/32/64. No 8-bit form exists. -/
inductive BtWeite where
  | w16 | w32 | w64
  deriving DecidableEq, Repr

/-- Width as architectural `Breite`. -/
def btWeiteBreite : BtWeite → Breite
  | .w16 => .b16 | .w32 => .b32 | .w64 => .b64

/-- Width in bits. -/
def btWeiteBits : BtWeite → Nat
  | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- The four covered shapes: register offset and imm8 offset, each on
    a register or on base + disp32 memory. -/
inductive BtForm where
  | reg (op : BtOp) (w : BtWeite) (dst src : Register)
  | imm (op : BtOp) (w : BtWeite) (dst : Register) (n : Nat)
  | memReg (op : BtOp) (w : BtWeite) (base bitReg : Register)
    (disp : BitVec 32)
  | memImm (op : BtOp) (w : BtWeite) (base : Register)
    (disp : BitVec 32) (n : Nat)
  deriving DecidableEq, Repr

/-- Canonical REX byte with X = 0: W = wBit, R = rBit, B = bBit. -/
def rexBt (wBit rBit bBit : Nat) : Byte :=
  natByte (64 + 8 * wBit + 4 * rBit + bBit)

/-- Canonical prefix: 0x66 exactly for 16-bit, then the REX byte
    (W exactly for 64-bit). -/
def btPref (w : BtWeite) (rBit bBit : Nat) : List Byte :=
  match w with
  | .w16 => [natByte 102, rexBt 0 rBit bBit]
  | .w32 => [rexBt 0 rBit bBit]
  | .w64 => [rexBt 1 rBit bBit]

/-- Canonical byte encoding of one covered form. -/
def encodeBt : BtForm → List Byte
  | .reg op w dst src =>
    btPref w (regHigh src) (regHigh dst) ++
      [natByte 15, natByte (btOpcode op),
       modrmReg (regLow src) (regLow dst)]
  | .imm op w dst n =>
    btPref w 0 (regHigh dst) ++
      [natByte 15, natByte 186,
       natByte (192 + 8 * btGruppe op + regLow dst), natByte n]
  | .memReg op w base bitReg d =>
    btPref w (regHigh bitReg) (regHigh base) ++
      [natByte 15, natByte (btOpcode op),
       modrmMem (regLow bitReg) (regLow base)] ++
      (if regLow base == 4 then [natByte 36] else []) ++ leBytes32 d
  | .memImm op w base d n =>
    btPref w 0 (regHigh base) ++
      [natByte 15, natByte 186,
       natByte (128 + 8 * btGruppe op + regLow base)] ++
      (if regLow base == 4 then [natByte 36] else []) ++
      leBytes32 d ++ [natByte n]

/-- Admitted REX bytes (W/R/B free, X = 0): back to the three bits. -/
def decodeBtRex : Byte → Option (Nat × Nat × Nat)
  | b =>
    match byteNat b with
    | 64 => some (0, 0, 0) | 65 => some (0, 0, 1)
    | 68 => some (0, 1, 0) | 69 => some (0, 1, 1)
    | 72 => some (1, 0, 0) | 73 => some (1, 0, 1)
    | 76 => some (1, 1, 0) | 77 => some (1, 1, 1)
    | _ => none

/-- The REX encoder lands in the admitted set. -/
theorem rexBt_rund (wBit rBit bBit : Nat)
    (hw : wBit < 2) (hr : rBit < 2) (hb : bBit < 2) :
    decodeBtRex (rexBt wBit rBit bBit) = some (wBit, rBit, bBit) := by
  have e1 : wBit = 0 ∨ wBit = 1 := by omega
  have e2 : rBit = 0 ∨ rBit = 1 := by omega
  have e3 : bBit = 0 ∨ bBit = 1 := by omega
  cases e1 with
  | inl h0 =>
    cases e2 with
    | inl h1 =>
      cases e3 with
      | inl h2 => subst h0; subst h1; subst h2; rfl
      | inr h2 => subst h0; subst h1; subst h2; rfl
    | inr h1 =>
      cases e3 with
      | inl h2 => subst h0; subst h1; subst h2; rfl
      | inr h2 => subst h0; subst h1; subst h2; rfl
  | inr h0 =>
    cases e2 with
    | inl h1 =>
      cases e3 with
      | inl h2 => subst h0; subst h1; subst h2; rfl
      | inr h2 => subst h0; subst h1; subst h2; rfl
    | inr h1 =>
      cases e3 with
      | inl h2 => subst h0; subst h1; subst h2; rfl
      | inr h2 => subst h0; subst h1; subst h2; rfl

/-- Register-form opcode back to the operation. -/
def opcOp : Nat → Option BtOp
  | 163 => some .bt | 171 => some .bts
  | 179 => some .btr | 187 => some .btc
  | _ => none

/-- Decoding inverts encoding on every operation. -/
theorem opcOp_btOpcode (op : BtOp) :
    opcOp (btOpcode op) = some op := by
  cases op <;> rfl

/-- Group digit back to the operation. -/
def gruppeOp : Nat → Option BtOp
  | 4 => some .bt | 5 => some .bts | 6 => some .btr | 7 => some .btc
  | _ => none

/-- Decoding inverts encoding on every group digit. -/
theorem gruppeOp_btGruppe (op : BtOp) :
    gruppeOp (btGruppe op) = some op := by
  cases op <;> rfl

/-- Decode the register/memory tail after 0F and a register-form
    opcode: mod = 3 is register-direct (reg field is the bit-offset
    register), mod = 2 is base + disp32 memory (SIB exactly when the
    base needs it); every other mode refuses. -/
def decodeBtRegMem (op : BtOp) (w : BtWeite) (rBit bBit : Nat) :
    List Byte → Option (BtForm × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 3 =>
      match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
      | some src, some dst => some ((.reg op w dst src), rest)
      | _, _ => none
    | 2 =>
      if rm == 4 then
        match rest with
        | sib :: rest' =>
          if byteNat sib == 36 then
            match parseLe32 rest' with
            | some (d, rest'') =>
              match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
              | some bitReg, some base =>
                some ((.memReg op w base bitReg d), rest'')
              | _, _ => none
            | none => none
          else none
        | [] => none
      else
        match parseLe32 rest with
        | some (d, rest') =>
          match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
          | some bitReg, some base =>
            some ((.memReg op w base bitReg d), rest')
          | _, _ => none
        | none => none
    | _ => none

/-- Decode the group tail after 0F BA: the reg field must be the
    group digit (REX.R is 0 in the canonical subset), mod = 3 is the
    imm8 form, mod = 2 the memory imm8 form. -/
def decodeBtGruppe (w : BtWeite) (rBit bBit : Nat) :
    List Byte → Option (BtForm × List Byte)
  | [] => none
  | m :: rest =>
    if rBit == 0 then
      match gruppeOp (byteNat m / 8 % 8) with
      | some op =>
        match codeReg (bBit * 8 + byteNat m % 8) with
        | some dst =>
          match byteNat m / 64 with
          | 3 =>
            match rest with
            | i :: rest' => some ((.imm op w dst (byteNat i)), rest')
            | [] => none
          | 2 =>
            let rm := byteNat m % 8
            if rm == 4 then
              match rest with
              | sib :: rest' =>
                if byteNat sib == 36 then
                  match parseLe32 rest' with
                  | some (d, rest'') =>
                    match rest'' with
                    | i :: rest3 =>
                      some ((.memImm op w dst d (byteNat i)), rest3)
                    | [] => none
                  | none => none
                else none
              | [] => none
            else
              match parseLe32 rest with
              | some (d, rest') =>
                match rest' with
                | i :: rest3 =>
                  some ((.memImm op w dst d (byteNat i)), rest3)
                | [] => none
              | none => none
          | _ => none
        | none => none
      | none => none
    else none

/-- Decode after the 0F prefix: a register-form opcode takes the
    register/memory tail, 186 the group tail, anything else refuses. -/
def decodeBt0F (w : BtWeite) (rBit bBit : Nat) :
    List Byte → Option (BtForm × List Byte)
  | [] => none
  | o :: rest =>
    match opcOp (byteNat o) with
    | some op => decodeBtRegMem op w rBit bBit rest
    | none =>
      if byteNat o == 186 then decodeBtGruppe w rBit bBit rest
      else none

/-- Decode after the prefix: 0F plus the opcode tail. -/
def decodeBtNach (w : BtWeite) (rBit bBit : Nat) :
    List Byte → Option (BtForm × List Byte)
  | [] => none
  | p :: rest =>
    if byteNat p == 15 then decodeBt0F w rBit bBit rest
    else none

/-- Top-level decoder: LOCK refuses; 0x66 selects 16-bit (with a W = 0
    REX behind it, so 66 + REX.W refuses); otherwise the REX byte
    selects 32 vs 64-bit. Anything else refuses. -/
def decodeBt : List Byte → Option (BtForm × List Byte)
  | [] => none
  | b :: rest =>
    if byteNat b == 240 then none
    else if byteNat b == 102 then
      match rest with
      | r :: tail =>
        match decodeBtRex r with
        | some (0, rBit, bBit) => decodeBtNach .w16 rBit bBit tail
        | _ => none
      | [] => none
    else
      match decodeBtRex b with
      | some (0, rBit, bBit) => decodeBtNach .w32 rBit bBit rest
      | some (1, rBit, bBit) => decodeBtNach .w64 rBit bBit rest
      | _ => none

/-! ## 7. Round trips, lengths, planted refusals.

    Decode inverts encode over any suffix; the operation stays
    symbolic through the back-mapping lemmas. Lengths are checked
    separately against `btLaenge` and the 1..15 bound. -/

/-- The opcode byte survives unfolding, for every operation. -/
theorem btOpcode_toNat (op : BtOp) :
    (BitVec.ofNat 8 (btOpcode op)).toNat = btOpcode op := by
  cases op <;> decide

set_option maxHeartbeats 4000000 in
/-- Round trip for register forms, over any suffix: every case
    closed by kernel computation (`rfl`), so the byte mapping is
    checked on all 3072 register/width/operation combinations. -/
theorem roundtripBtReg (op : BtOp) (w : BtWeite) (dst src : Register)
    (suffix : List Byte) :
    decodeBt (encodeBt (.reg op w dst src) ++ suffix) =
      some ((.reg op w dst src), suffix) := by
  cases op <;> cases w <;> cases dst <;> cases src <;> rfl

/-- Canonical prefix length: 2 exactly for 16-bit, else 1. -/
def btPrefLaenge : BtWeite → Nat
  | .w16 => 2 | .w32 => 1 | .w64 => 1

/-- Consumed length of one covered form. -/
def btLaenge : BtForm → Nat
  | .reg _ w _ _ => btPrefLaenge w + 3
  | .imm _ w _ _ => btPrefLaenge w + 4
  | .memReg _ w base _ _ =>
    btPrefLaenge w + 7 + (if regLow base == 4 then 1 else 0)
  | .memImm _ w base _ _ =>
    btPrefLaenge w + 8 + (if regLow base == 4 then 1 else 0)

/-- The consumed length is the encoded length, on every form (lengths
    depend only on the width and the SIB need, never on the offset,
    the displacement value or the operation). -/
theorem btLaenge_encode (f : BtForm) :
    btLaenge f = (encodeBt f).length := by
  cases f with
  | reg op w dst src =>
    cases w <;> rfl
  | imm op w dst n =>
    cases w <;> rfl
  | memReg op w base bitReg d =>
    cases w <;> cases base <;> rfl
  | memImm op w base d n =>
    cases w <;> cases base <;> rfl

/-- Every covered encoding fits the 1..15 instruction bound. -/
theorem btLaenge_ok (f : BtForm) :
    laengeOk (btLaenge f) = true := by
  cases f with
  | reg op w dst src =>
    cases w <;> rfl
  | imm op w dst n =>
    cases w <;> rfl
  | memReg op w base bitReg d =>
    cases w <;> cases base <;> rfl
  | memImm op w base d n =>
    cases w <;> cases base <;> rfl

/-- Pinned bytes: `btc rax, rcx` is REX.W, 0F, BB, C8. -/
theorem pin_bt_btc_rax_rcx :
    encodeBt (.reg .btc .w64 .rax .rcx) =
      [natByte 72, natByte 15, natByte 187, natByte 200] := by
  decide

/-- Pinned bytes: 16-bit `bt rax, rcx` carries the 0x66 prefix. -/
theorem pin_bt_w16_rax_rcx :
    encodeBt (.reg .bt .w16 .rax .rcx) =
      [natByte 102, natByte 64, natByte 15, natByte 163,
        natByte 200] := by
  decide

/-- Pinned bytes: `bts edx, 5` is REX, 0F, BA, EA, 05. -/
theorem pin_bt_bts_edx_5 :
    encodeBt (.imm .bts .w32 .rdx 5) =
      [natByte 64, natByte 15, natByte 186, natByte 234,
        natByte 5] := by
  decide

/-- Pinned bytes: `btr [rbx+16], rcx` with disp32 16. -/
theorem pin_bt_mem_btr :
    encodeBt (.memReg .btr .w64 .rbx .rcx 16) =
      [natByte 72, natByte 15, natByte 179, natByte 139,
        natByte 16, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Pinned bytes: `bt [rsp], rax` needs the SIB byte. -/
theorem pin_bt_mem_sib :
    encodeBt (.memReg .bt .w32 .rsp .rax 0) =
      [natByte 64, natByte 15, natByte 163, natByte 132, natByte 36,
        natByte 0, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Pinned decodes: the canonical rows read back. -/
theorem pin_bt_dekode :
    decodeBt [natByte 72, natByte 15, natByte 187, natByte 200] =
        some (((.reg .btc .w64 .rax .rcx) : BtForm), []) ∧
      decodeBt [natByte 64, natByte 15, natByte 186, natByte 234,
          natByte 5] =
        some (((.imm .bts .w32 .rdx 5) : BtForm), []) ∧
      decodeBt [natByte 64, natByte 15, natByte 163, natByte 132,
          natByte 36, natByte 0, natByte 0, natByte 0, natByte 0] =
        some (((.memReg .bt .w32 .rsp .rax 0) : BtForm), []) := by
  decide

/-- Truncated rows refuse: empty, lone prefix, opcode without ModRM,
    group row without the immediate byte, memory row without disp32. -/
theorem sonde_bt_abgeschnitten :
    decodeBt [] = none ∧
    decodeBt [natByte 102] = none ∧
    decodeBt [natByte 72] = none ∧
    decodeBt [natByte 72, natByte 15] = none ∧
    decodeBt [natByte 72, natByte 15, natByte 163] = none ∧
    decodeBt [natByte 72, natByte 15, natByte 186, natByte 228] =
      none ∧
    decodeBt [natByte 72, natByte 15, natByte 163, natByte 132] =
      none := by
  decide

/-- Planted refusals, each with its named reason: LOCK (locked RMW
    stays with the locked families), 0x66 + REX.W, REX.X, a REX.R
    group row, mod-0/mod-1 memory, a bad group digit, a bad opcode,
    and a wrong SIB byte. -/
theorem sonde_bt_verweigert :
    decodeBt [natByte 240, natByte 72, natByte 15, natByte 163,
        natByte 195] = none ∧
    decodeBt [natByte 102, natByte 72, natByte 15, natByte 163,
        natByte 195] = none ∧
    decodeBt [natByte 66, natByte 15, natByte 163,
        natByte 195] = none ∧
    decodeBt [natByte 76, natByte 15, natByte 186, natByte 228,
        natByte 5] = none ∧
    decodeBt [natByte 72, natByte 15, natByte 163,
        natByte 3] = none ∧
    decodeBt [natByte 72, natByte 15, natByte 163,
        natByte 67] = none ∧
    decodeBt [natByte 72, natByte 15, natByte 186,
        natByte 192] = none ∧
    decodeBt [natByte 72, natByte 15, natByte 200] = none ∧
    decodeBt [natByte 72, natByte 15, natByte 163, natByte 132,
        natByte 0] = none := by
  decide

/-- The opcode back-mapping survives the `%`-form the simplifier
    produces, for every operation. -/
theorem opcOp_modpow (op : BtOp) :
    opcOp (btOpcode op % 2 ^ 8) = some op := by
  cases op <;> decide

/-- The opcode back-mapping in `% 256` form, for every operation. -/
theorem opcOp_mod256 (op : BtOp) :
    opcOp (btOpcode op % 256) = some op := by
  cases op <;> decide

/-- The immediate byte survives unfolding below 256. -/
theorem btImmByte (n : Nat) (h : n < 256) :
    (BitVec.ofNat 8 n).toNat = n :=
  byteNat_natByte_of_lt n h

set_option maxHeartbeats 8000000 in
/-- Round trip for 16-bit memory forms, over any suffix (the operation
    stays symbolic through the back-mapping lemmas). -/
theorem roundtripBtMemReg16 (op : BtOp) (base bitReg : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeBt (encodeBt (.memReg op .w16 base bitReg d) ++ suffix) =
      some (((.memReg op .w16 base bitReg d) : BtForm), suffix) := by
  cases base <;> cases bitReg <;>
    simp [encodeBt, decodeBt, decodeBtNach, decodeBt0F,
      decodeBtRegMem, btPref, rexBt, decodeBtRex, modrmMem, regHigh,
      regLow, regCode, codeReg, byteNat, natByte,
      opcOp_mod256, parseLe32_leBytes32]

/-- Round trip for 32-bit memory forms, over any suffix. -/
theorem roundtripBtMemReg32 (op : BtOp) (base bitReg : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeBt (encodeBt (.memReg op .w32 base bitReg d) ++ suffix) =
      some (((.memReg op .w32 base bitReg d) : BtForm), suffix) := by
  cases base <;> cases bitReg <;>
    simp [encodeBt, decodeBt, decodeBtNach, decodeBt0F,
      decodeBtRegMem, btPref, rexBt, decodeBtRex, modrmMem, regHigh,
      regLow, regCode, codeReg, byteNat, natByte,
      opcOp_mod256, parseLe32_leBytes32]

/-- Round trip for 64-bit memory forms, over any suffix. -/
theorem roundtripBtMemReg64 (op : BtOp) (base bitReg : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeBt (encodeBt (.memReg op .w64 base bitReg d) ++ suffix) =
      some (((.memReg op .w64 base bitReg d) : BtForm), suffix) := by
  cases base <;> cases bitReg <;>
    simp [encodeBt, decodeBt, decodeBtNach, decodeBt0F,
      decodeBtRegMem, btPref, rexBt, decodeBtRex, modrmMem, regHigh,
      regLow, regCode, codeReg, byteNat, natByte,
      opcOp_mod256, parseLe32_leBytes32]

/-- Round trip for imm8 forms, over any suffix. -/
theorem roundtripBtImm (op : BtOp) (w : BtWeite) (dst : Register)
    (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeBt (encodeBt (.imm op w dst n) ++ suffix) =
      some ((.imm op w dst n), suffix) := by
  cases op <;> cases w <;> cases dst <;>
    simp [encodeBt, decodeBt, decodeBtNach, decodeBt0F,
      decodeBtGruppe, decodeBtRex, gruppeOp, opcOp, btPref, rexBt,
      regHigh, regLow, regCode, codeReg, btGruppe, byteNat, natByte,
      btImmByte n h]

/-- Round trip for memory imm8 forms, over any suffix. -/
theorem roundtripBtMemImm (op : BtOp) (w : BtWeite) (base : Register)
    (d : BitVec 32) (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeBt (encodeBt (.memImm op w base d n) ++ suffix) =
      some ((.memImm op w base d n), suffix) := by
  cases op <;> cases w <;> cases base <;>
    simp [encodeBt, decodeBt, decodeBtNach, decodeBt0F,
      decodeBtGruppe, decodeBtRex, gruppeOp, opcOp, btPref, rexBt,
      regHigh, regLow, regCode, codeReg, btGruppe, byteNat, natByte,
      btImmByte n h, parseLe32_leBytes32]

/-! ## 8. Register step, flag class, unified dispatcher.

    The register step reuses the §1-§5 value semantics unchanged: CF
    is the selected (old) bit, ZF is preserved (unaffected), and
    OF/SF/AF/PF keep their incoming values -- a modelling choice the
    `btErlaubt` class leaves free (undefined, never false), so no
    consumer can depend on the kept values. Memory forms refuse here
    (they are TSO events, §9); a length mismatch refuses. The
    dispatcher prefers the accepted unified chain, like
    `decodeMulDivWidth`. -/

/-- A decoded bit-test instruction with its consumed length. -/
structure BtDecodiert where
  befehl : BtForm
  laenge : Nat
  deriving DecidableEq, Repr

/-- Width projection of a form. -/
def btFormWeite : BtForm → BtWeite
  | .reg _ w _ _ => w
  | .imm _ w _ _ => w
  | .memReg _ w _ _ _ => w
  | .memImm _ w _ _ _ => w

/-- Operation projection of a form. -/
def btFormOp : BtForm → BtOp
  | .reg op _ _ _ => op
  | .imm op _ _ _ => op
  | .memReg op _ _ _ _ => op
  | .memImm op _ _ _ _ => op

/-- Flag update: CF is the selected bit, everything else preserved. -/
def btFlags (f : Flags) (cf : Bool) : Flags := { f with cf := cf }

/-- The bit-test flag class: CF is the selected bit, ZF is the
    incoming ZF, OF/SF/AF/PF are free. -/
def btErlaubt (vor : Flags) (cf : Bool) (nach : Flags) : Prop :=
  nach.cf = cf ∧ nach.zf = vor.zf

/-- One register step: refuse on length mismatch; BT/BTS/BTR/BTC on
    registers write back the routed value with CF set to the old
    selected bit; memory forms refuse (TSO events in §9). -/
def btSchritt (d : BtDecodiert) (s : Zustand) : Option Zustand :=
  if d.laenge == btLaenge d.befehl then
    match d.befehl with
    | .reg op w dst src =>
      let base := s.register dst
      let off := (s.register src).toNat
      let bw := btWeiteBreite w
      some (schrittRegister s (ripNach s.rip d.laenge)
        (btFlags s.flags (btBit bw base off)) dst
        (btSchreibe bw base (btRoh op bw base off)))
    | .imm op w dst n =>
      let base := s.register dst
      let bw := btWeiteBreite w
      some (schrittRegister s (ripNach s.rip d.laenge)
        (btFlags s.flags (btBit bw base n)) dst
        (btSchreibe bw base (btRoh op bw base n)))
    | .memReg _ _ _ _ _ => none
    | .memImm _ _ _ _ _ => none
  else none

/-- Length mismatch refuses: the consumed length is checked data. -/
theorem btSchritt_laenge (d : BtDecodiert) (s : Zustand)
    (h : d.laenge ≠ btLaenge d.befehl) :
    btSchritt d s = none := by
  unfold btSchritt
  rw [if_neg (by simpa [beq_iff_eq] using h)]

/-- Memory forms refuse the register step, even at the right length:
    they are TSO events (§9), never the register plug. -/
theorem btSchritt_mem_verweigert (d : BtDecodiert) (s : Zustand)
    (op : BtOp) (w : BtWeite) (base bitReg : Register)
    (disp : BitVec 32)
    (hform : d.befehl = .memReg op w base bitReg disp)
    (h : d.laenge == btLaenge d.befehl) :
    btSchritt d s = none := by
  unfold btSchritt
  rw [if_pos h, hform]

/-- Memory imm8 forms refuse the register step as well. -/
theorem btSchritt_memImm_verweigert (d : BtDecodiert) (s : Zustand)
    (op : BtOp) (w : BtWeite) (base : Register)
    (disp : BitVec 32) (n : Nat)
    (hform : d.befehl = .memImm op w base disp n)
    (h : d.laenge == btLaenge d.befehl) :
    btSchritt d s = none := by
  unfold btSchritt
  rw [if_pos h, hform]

/-- Register step: the routed value with CF set to the old bit. -/
theorem btSchritt_reg (op : BtOp) (w : BtWeite) (dst src : Register)
    (l : Nat) (s : Zustand)
    (h : l == btLaenge (.reg op w dst src)) :
    btSchritt ⟨.reg op w dst src, l⟩ s =
      some (schrittRegister s (ripNach s.rip l)
        (btFlags s.flags
          (btBit (btWeiteBreite w) (s.register dst)
            ((s.register src).toNat))) dst
        (btSchreibe (btWeiteBreite w) (s.register dst)
          (btRoh op (btWeiteBreite w) (s.register dst)
            ((s.register src).toNat)))) := by
  unfold btSchritt
  rw [if_pos h]

/-- Imm8 step: the routed value with CF set to the old bit. -/
theorem btSchritt_imm (op : BtOp) (w : BtWeite) (dst : Register)
    (n : Nat) (l : Nat) (s : Zustand)
    (h : l == btLaenge (.imm op w dst n)) :
    btSchritt ⟨.imm op w dst n, l⟩ s =
      some (schrittRegister s (ripNach s.rip l)
        (btFlags s.flags
          (btBit (btWeiteBreite w) (s.register dst) n)) dst
        (btSchreibe (btWeiteBreite w) (s.register dst)
          (btRoh op (btWeiteBreite w) (s.register dst) n))) := by
  unfold btSchritt
  rw [if_pos h]

/-- A successful step never touches memory. -/
theorem btSchritt_speicher (d : BtDecodiert) (s s' : Zustand)
    (h : btSchritt d s = some s') : s'.speicher = s.speicher := by
  unfold btSchritt at h
  by_cases hl : d.laenge == btLaenge d.befehl
  · rw [if_pos hl] at h
    cases df : d.befehl with
    | reg op w dst src =>
      rw [df] at h
      cases h
      rfl
    | imm op w dst n =>
      rw [df] at h
      cases h
      rfl
    | memReg op w base bitReg disp =>
      rw [df] at h
      cases h
    | memImm op w base disp n =>
      rw [df] at h
      cases h
  · rw [if_neg hl] at h
    cases h

/-- A successful step advances RIP past the decoded length. -/
theorem btSchritt_rip (d : BtDecodiert) (s s' : Zustand)
    (h : btSchritt d s = some s') :
    s'.rip = ripNach s.rip d.laenge := by
  unfold btSchritt at h
  by_cases hl : d.laenge == btLaenge d.befehl
  · rw [if_pos hl] at h
    cases df : d.befehl with
    | reg op w dst src =>
      rw [df] at h
      cases h
      rfl
    | imm op w dst n =>
      rw [df] at h
      cases h
      rfl
    | memReg op w base bitReg disp =>
      rw [df] at h
      cases h
    | memImm op w base disp n =>
      rw [df] at h
      cases h
  · rw [if_neg hl] at h
    cases h

/-- CF of a register step is the old selected bit. -/
theorem btSchritt_cf_reg (op : BtOp) (w : BtWeite) (dst src : Register)
    (l : Nat) (s s' : Zustand)
    (h : l == btLaenge (.reg op w dst src))
    (hs : btSchritt ⟨.reg op w dst src, l⟩ s = some s') :
    s'.flags.cf =
      btBit (btWeiteBreite w) (s.register dst)
        ((s.register src).toNat) := by
  have heq := btSchritt_reg op w dst src l s h
  rw [heq] at hs
  cases hs
  rfl

/-- CF of an imm8 step is the old selected bit. -/
theorem btSchritt_cf_imm (op : BtOp) (w : BtWeite) (dst : Register)
    (n : Nat) (l : Nat) (s s' : Zustand)
    (h : l == btLaenge (.imm op w dst n))
    (hs : btSchritt ⟨.imm op w dst n, l⟩ s = some s') :
    s'.flags.cf = btBit (btWeiteBreite w) (s.register dst) n := by
  have heq := btSchritt_imm op w dst n l s h
  rw [heq] at hs
  cases hs
  rfl

/-- ZF is unaffected by a register step. -/
theorem btSchritt_zf_reg (op : BtOp) (w : BtWeite) (dst src : Register)
    (l : Nat) (s s' : Zustand)
    (h : l == btLaenge (.reg op w dst src))
    (hs : btSchritt ⟨.reg op w dst src, l⟩ s = some s') :
    s'.flags.zf = s.flags.zf := by
  have heq := btSchritt_reg op w dst src l s h
  rw [heq] at hs
  cases hs
  rfl

/-- ZF is unaffected by an imm8 step. -/
theorem btSchritt_zf_imm (op : BtOp) (w : BtWeite) (dst : Register)
    (n : Nat) (l : Nat) (s s' : Zustand)
    (h : l == btLaenge (.imm op w dst n))
    (hs : btSchritt ⟨.imm op w dst n, l⟩ s = some s') :
    s'.flags.zf = s.flags.zf := by
  have heq := btSchritt_imm op w dst n l s h
  rw [heq] at hs
  cases hs
  rfl

/-- A register step meets the flag class: CF pinned, ZF kept. -/
theorem btSchritt_erlaubt_reg (op : BtOp) (w : BtWeite)
    (dst src : Register) (l : Nat) (s s' : Zustand)
    (h : l == btLaenge (.reg op w dst src))
    (hs : btSchritt ⟨.reg op w dst src, l⟩ s = some s') :
    btErlaubt s.flags
      (btBit (btWeiteBreite w) (s.register dst)
        ((s.register src).toNat)) s'.flags :=
  ⟨btSchritt_cf_reg op w dst src l s s' h hs,
    btSchritt_zf_reg op w dst src l s s' h hs⟩

/-- An imm8 step meets the flag class: CF pinned, ZF kept. -/
theorem btSchritt_erlaubt_imm (op : BtOp) (w : BtWeite) (dst : Register)
    (n : Nat) (l : Nat) (s s' : Zustand)
    (h : l == btLaenge (.imm op w dst n))
    (hs : btSchritt ⟨.imm op w dst n, l⟩ s = some s') :
    btErlaubt s.flags
      (btBit (btWeiteBreite w) (s.register dst) n) s'.flags :=
  ⟨btSchritt_cf_imm op w dst n l s s' h hs,
    btSchritt_zf_imm op w dst n l s s' h hs⟩

/-- A register step keeps every other register. -/
theorem btSchritt_fremd_reg (op : BtOp) (w : BtWeite)
    (dst src : Register) (l : Nat) (s s' : Zustand) (q : Register)
    (h : l == btLaenge (.reg op w dst src))
    (hs : btSchritt ⟨.reg op w dst src, l⟩ s = some s')
    (hq : q ≠ dst) :
    s'.register q = s.register q := by
  have heq := btSchritt_reg op w dst src l s h
  rw [heq] at hs
  cases hs
  exact regSet_fremd s.register dst q _ hq

/-- An imm8 step keeps every other register. -/
theorem btSchritt_fremd_imm (op : BtOp) (w : BtWeite) (dst : Register)
    (n : Nat) (l : Nat) (s s' : Zustand) (q : Register)
    (h : l == btLaenge (.imm op w dst n))
    (hs : btSchritt ⟨.imm op w dst n, l⟩ s = some s')
    (hq : q ≠ dst) :
    s'.register q = s.register q := by
  have heq := btSchritt_imm op w dst n l s h
  rw [heq] at hs
  cases hs
  exact regSet_fremd s.register dst q _ hq

/-! ## 9. Unified dispatcher, no-shadowing pins, unified step.

    The dispatcher prefers the accepted unified chain
    (`decodeExt`), taking the bit-test arm only where it refuses --
    no pilot or extension form is shadowed (mirroring
    `decodeMulDivWidth`). The unified step runs Ext through `stepExt`
    and bit-test through `btSchritt` on the core half; BT never
    traps, so refusal is `verweigert`. -/

/-- Unified dispatcher instruction: the accepted unified chain first,
    the bit-test family only where it refuses. -/
inductive BtHwInstr where
  | ext : ExtInstr → BtHwInstr
  | bt : BtDecodiert → BtHwInstr
  deriving DecidableEq, Repr

/-- Dispatcher: the unified decoder first, the bit-test decoder only
    where the unified chain refuses. -/
def decodeBtHw : List Byte → Option (BtHwInstr × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some (i, rest) => some (.ext i, rest)
    | none =>
      match decodeBt bs with
      | some (f, rest) => some (.bt ⟨f, btLaenge f⟩, rest)
      | none => none

/-- The dispatcher agrees with the unified chain wherever it accepts:
    no pilot or extension form is shadowed. -/
theorem decodeBtHw_prefers_ext (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeBtHw bs = some (.ext i, rest) := by
  unfold decodeBtHw
  rw [h]

/-- Where the unified chain refuses, a covered bit-test row is taken. -/
theorem decodeBtHw_bt (bs : List Byte) (f : BtForm)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeBt bs = some (f, rest)) :
    decodeBtHw bs = some (.bt ⟨f, btLaenge f⟩, rest) := by
  unfold decodeBtHw
  rw [h1, h2]

/-- Where both chains refuse, the dispatcher refuses. -/
theorem decodeBtHw_nichts (bs : List Byte)
    (h1 : decodeExt bs = none) (h2 : decodeBt bs = none) :
    decodeBtHw bs = none := by
  unfold decodeBtHw
  rw [h1, h2]

/-! ## 10. No-shadowing pins: the unified chain refuses every new row.

    Each pin is a closed `decide`: if any fails, the canonical subset
    collides with an accepted row -- a finding, never silently kept. -/

/-- The unified chain refuses the 64-bit register row. -/
theorem ext_weist_btreg64_zurueck :
    decodeExt [natByte 72, natByte 15, natByte 187,
      natByte 200] = none := by
  decide

/-- The unified chain refuses the 32-bit register row. -/
theorem ext_weist_btreg32_zurueck :
    decodeExt [natByte 65, natByte 15, natByte 171,
      natByte 200] = none := by
  decide

/-- The unified chain refuses the 16-bit register row. -/
theorem ext_weist_btreg16_zurueck :
    decodeExt [natByte 102, natByte 64, natByte 15, natByte 163,
      natByte 200] = none := by
  decide

/-- The unified chain refuses the imm8 row. -/
theorem ext_weist_btimm_zurueck :
    decodeExt [natByte 64, natByte 15, natByte 186, natByte 234,
      natByte 5] = none := by
  decide

/-- The unified chain refuses the memory row. -/
theorem ext_weist_btmem_zurueck :
    decodeExt [natByte 72, natByte 15, natByte 179, natByte 139,
      natByte 16, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The 64-bit register row takes the bit-test arm. -/
theorem pin_btHw_reg64 :
    decodeBtHw [natByte 72, natByte 15, natByte 187,
      natByte 200] =
      some (.bt ⟨.reg .btc .w64 .rax .rcx, 4⟩, []) := by
  decide

/-- The imm8 row takes the bit-test arm. -/
theorem pin_btHw_imm32 :
    decodeBtHw [natByte 64, natByte 15, natByte 186, natByte 234,
      natByte 5] =
      some (.bt ⟨.imm .bts .w32 .rdx 5, 5⟩, []) := by
  decide

/-- The memory row takes the bit-test arm. -/
theorem pin_btHw_mem64 :
    decodeBtHw [natByte 72, natByte 15, natByte 179, natByte 139,
      natByte 16, natByte 0, natByte 0, natByte 0] =
      some (.bt ⟨.memReg .btr .w64 .rbx .rcx 16, 8⟩, []) := by
  decide

/-! ## 11. One unified step: exact evaluation selection. -/

/-- Consumed length of one dispatcher instruction. -/
def btHwLen : BtHwInstr → Nat
  | .ext i => extLen i
  | .bt d => d.laenge

/-- One unified step: Ext through `stepExt`, bit-test through
    `btSchritt` on the core half. BT never traps. -/
def btHwSchritt (i : BtHwInstr) (t : FpZustand)
    (b : BereitProfil) : ExtAusgang :=
  match i with
  | .ext j => stepExt j t b
  | .bt d =>
    match btSchritt d t.kern with
    | some s' => .weiter { t with kern := s' }
    | none => .verweigert

/-- Selection: the unified arm IS the accepted unified step. -/
theorem btHwSchritt_ext (j : ExtInstr) (t : FpZustand)
    (b : BereitProfil) (o : ExtAusgang)
    (h : stepExt j t b = o) :
    btHwSchritt (.ext j) t b = o := by
  have e : btHwSchritt (.ext j) t b = stepExt j t b := rfl
  rw [e, h]

/-- Selection: the bit-test arm IS the accepted family step on the
    core half, re-embedded on success. -/
theorem btHwSchritt_bt_ok (d : BtDecodiert) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : btSchritt d t.kern = some s') :
    btHwSchritt (.bt d) t b = .weiter { t with kern := s' } := by
  have e : btHwSchritt (.bt d) t b =
      match btSchritt d t.kern with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: bit-test refusal is unified refusal (never a halt). -/
theorem btHwSchritt_bt_verweigert (d : BtDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (h : btSchritt d t.kern = none) :
    btHwSchritt (.bt d) t b = .verweigert := by
  have e : btHwSchritt (.bt d) t b =
      match btSchritt d t.kern with
      | some s' => ExtAusgang.weiter { t with kern := s' }
      | none => .verweigert := rfl
  rw [e, h]

/-! ## 12. Machine adapter: the register plug.

    The producer plug instantiates `HwAdapter BtDecodiert` with the
    accepted API: a successful register step re-embeds core data over
    the shared memory; traps and refusals admit no successor state.
    Memory forms never take the register plug (§13 routes them
    through TSO events instead). -/

/-- The bit-test plug: one checked register event step on the
    coherent machine. `none` = length mismatch, memory form, or
    refusal -- never a silent successor. -/
def adapterBitTest : HwAdapter BtDecodiert :=
  ⟨fun m c d =>
    match btSchritt d (projZustand m c) with
    | some s' =>
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
    | none => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterBitTest_wf (m : HwMaschine) (c : Nat)
    (d : BtDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterBitTest).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterBitTest at h
  simp only at h
  cases hsch : btSchritt d (projZustand m c) with
  | some s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | none =>
    rw [hsch] at h
    simp only at h
    cases h

/-- Agreement: the adapter succeeds exactly where the accepted family
    step succeeds, with the successor core data re-embedded. -/
theorem adapterBitTest_ok (m : HwMaschine) (c : Nat)
    (d : BtDecodiert) (s' : Zustand)
    (h : btSchritt d (projZustand m c) = some s') :
    (adapterBitTest).schritt m c d =
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  unfold adapterBitTest
  simp only [h]

/-- The successor core sees the accepted successor registers over
    the shared memory. -/
theorem adapterBitTest_proj (m : HwMaschine) (c : Nat)
    (d : BtDecodiert) (s' : Zustand)
    (h : btSchritt d (projZustand m c) = some s') :
    ((setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).kerne c).register =
      s'.register ∧
    (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).mem = m.mem ∧
    s'.speicher = m.mem := by
  refine ⟨setKernVonFp_register m c _,
    setKernVonFp_speicher m c _, ?_⟩
  have hmem := btSchritt_speicher d (projZustand m c) s' h
  have hproj : (projZustand m c).speicher = m.mem := rfl
  rw [hproj] at hmem
  exact hmem

/-- A bad decode length admits no adapter step. -/
theorem adapterBitTest_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : BtDecodiert)
    (h : d.laenge ≠ btLaenge d.befehl) :
    (adapterBitTest).schritt m c d = none := by
  have hstep := btSchritt_laenge d (projZustand m c) h
  unfold adapterBitTest
  simp only [hstep]

/-- A memory form admits no adapter successor at any length: the
    register plug never serves memory. -/
theorem adapterBitTest_verweigert_memReg (m : HwMaschine) (c : Nat)
    (op : BtOp) (w : BtWeite) (base bitReg : Register)
    (disp : BitVec 32) (d : BtDecodiert)
    (hform : d.befehl = .memReg op w base bitReg disp) :
    (adapterBitTest).schritt m c d = none := by
  by_cases hl : d.laenge == btLaenge d.befehl
  · have hstep := btSchritt_mem_verweigert d (projZustand m c)
      op w base bitReg disp hform hl
    unfold adapterBitTest
    simp only [hstep]
  · have hne : d.laenge ≠ btLaenge d.befehl := by
      simpa [beq_iff_eq] using hl
    have hstep := btSchritt_laenge d (projZustand m c) hne
    unfold adapterBitTest
    simp only [hstep]

/-- A memory imm8 form admits no adapter successor either. -/
theorem adapterBitTest_verweigert_memImm (m : HwMaschine) (c : Nat)
    (op : BtOp) (w : BtWeite) (base : Register)
    (disp : BitVec 32) (n : Nat) (d : BtDecodiert)
    (hform : d.befehl = .memImm op w base disp n) :
    (adapterBitTest).schritt m c d = none := by
  by_cases hl : d.laenge == btLaenge d.befehl
  · have hstep := btSchritt_memImm_verweigert d (projZustand m c)
      op w base disp n hform hl
    unfold adapterBitTest
    simp only [hstep]
  · have hne : d.laenge ≠ btLaenge d.befehl := by
      simpa [beq_iff_eq] using hl
    have hstep := btSchritt_laenge d (projZustand m c) hne
    unfold adapterBitTest
    simp only [hstep]

/-! ## 13. Memory footprint: the signed offset moves the address.

    A register bit offset is SIGNED: the effective address is base +
    disp32 plus the byte displacement (floor division by 8), wrapping
    modulo 2^64 like hardware. The footprint is exactly the
    operand-size bytes at that address. -/

/-- Signed bit offset held by the offset register. -/
def btOffsetInt (s : Zustand) (bitReg : Register) : Int :=
  (s.register bitReg).toInt

/-- Byte displacement of a signed bit offset (`/` floors, so negative
    offsets move to lower bytes). -/
def btByteVersatz (off : Int) : Int := off / 8

/-- Bit position inside the addressed byte. -/
def btBitImByte (off : Int) : Nat := (off % 8).toNat

/-- Reconstruction: offset = 8 * displacement + bit. -/
theorem btVersatz_rekon (off : Int) :
    8 * (off / 8) + off % 8 = off := by
  omega

/-- The bit position lies inside its byte. -/
theorem btBitImByte_schranke (off : Int) :
    0 ≤ off % 8 ∧ off % 8 < 8 := by
  omega

/-- Effective address of a memory form: base + disp32 plus the signed
    byte displacement, wrapping modulo 2^64 like hardware. -/
def btEffAddr (s : Zustand) (base bitReg : Register)
    (disp : BitVec 32) : Adresse :=
  effAddr s base disp +
    BitVec.ofNat 64 (((s.register bitReg).toInt / 8) % 2 ^ 64).toNat

/-- Zero offset: the effective address is base + disp32. -/
theorem btEffAddr_null (s : Zustand) (base bitReg : Register)
    (disp : BitVec 32) (h : s.register bitReg = 0) :
    btEffAddr s base bitReg disp = effAddr s base disp := by
  have hz : (0 : Wort).toInt = 0 := by decide
  have h0 : (((0 : Int) / 8) % 2 ^ 64).toNat = 0 := by decide
  unfold btEffAddr
  rw [h, hz, h0]
  simp

/-- Operand size in bytes. -/
def btWeiteBytes : BtWeite → Nat
  | .w16 => 2 | .w32 => 4 | .w64 => 8

/-- The footprint of a memory form: the operand-size bytes at the
    effective address -- exactly the addressed unit, never more. -/
def btFuss (w : BtWeite) (eff : Adresse) : List Adresse :=
  (List.range (btWeiteBytes w)).map (fun i => eff + BitVec.ofNat 64 i)

/-- Footprint length is the operand size. -/
theorem btFuss_laenge (w : BtWeite) (eff : Adresse) :
    (btFuss w eff).length = btWeiteBytes w := by
  cases w <;> rfl

/-- Displacement pins: positive offsets move up, negative down, with
    floor division (bit 7 of the byte below for -1). -/
theorem probe_bt_versatz :
    btByteVersatz 20 = 2 ∧ btBitImByte 20 = 4 ∧
    btByteVersatz (-1) = -1 ∧ btBitImByte (-1) = 7 ∧
    btByteVersatz (-9) = -2 ∧ btBitImByte (-9) = 7 := by
  decide

/-! ## 14. Memory forms as TSO events: load, modify, write back.

    A memory form never touches canonical memory directly: it loads
    its exact footprint through one `loadByte` event per byte (any
    unreadable byte refuses the whole word, never a partial word),
    modifies exactly the byte holding the selected bit, and issues
    the bytes back through `issueByte` (buffered, observed by the
    owner through forwarding). -/

/-- Load a footprint through TSO byte events: every byte must be
    readable; `none` is refusal, never a partial word. -/
def btLadeListe (s : TSOZustand) (c : Nat) :
    List Adresse → Option (List Byte)
  | [] => some []
  | a :: rest =>
    match loadByte s c a, btLadeListe s c rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- An unreadable footprint byte refuses the whole load. -/
theorem btLadeListe_verweigert (s : TSOZustand) (c : Nat)
    (addrs : List Adresse) (a : Adresse)
    (hmem : a ∈ addrs) (h : loadByte s c a = none) :
    btLadeListe s c addrs = none := by
  revert hmem
  induction addrs with
  | nil =>
    intro hm
    simp at hm
  | cons b rest ih =>
    intro hm
    simp only [btLadeListe]
    simp only [List.mem_cons] at hm
    cases hm with
    | inl heq =>
      subst heq
      simp [h]
    | inr hm' =>
      have ihr := ih hm'
      simp [ihr]

/-- The issued entries of a write-back: address/value pairs. -/
def btEintraege (addrs : List Adresse) (vs : List Byte) :
    List TSOEintrag :=
  (addrs.zip vs).map (fun p => ⟨p.1, p.2⟩)

/-- Write bytes back through TSO issues (buffered, never a direct
    store); a length mismatch refuses instead of truncating. -/
def btMemSchreibe (s : TSOZustand) (c : Nat) (addrs : List Adresse)
    (vs : List Byte) : Option TSOZustand :=
  if addrs.length == vs.length then
    issueListe s c (btEintraege addrs vs)
  else none

/-- A successful write-back changes no canonical byte (buffer only). -/
theorem btMemSchreibe_mem (s s1 : TSOZustand) (c : Nat)
    (addrs : List Adresse) (vs : List Byte)
    (h : btMemSchreibe s c addrs vs = some s1) (x : Adresse) :
    s1.mem.bytes x = s.mem.bytes x := by
  unfold btMemSchreibe at h
  by_cases hl : (addrs.length == vs.length) = true
  · rw [if_pos hl] at h
    exact issueListe_kein_speicher s s1 c _ h x
  · rw [if_neg hl] at h
    cases h

/-- A successful write-back appends exactly its entries, oldest
    first, to the acting core's buffer. -/
theorem btMemSchreibe_puffer (s s1 : TSOZustand) (c : Nat)
    (addrs : List Adresse) (vs : List Byte)
    (h : btMemSchreibe s c addrs vs = some s1) :
    s1.puffer c = s.puffer c ++ btEintraege addrs vs := by
  unfold btMemSchreibe at h
  by_cases hl : (addrs.length == vs.length) = true
  · rw [if_pos hl] at h
    exact issueListe_haengt_an s s1 c _ h
  · rw [if_neg hl] at h
    cases h

/-- One-bit mask inside a byte. -/
def btByteMaske (bit : Nat) : Byte := BitVec.ofNat 8 (2 ^ bit)

/-- Raw new byte value: BT keeps, BTS sets, BTR clears, BTC
    complements the selected bit of the byte. -/
def btByteRoh (op : BtOp) (base : Byte) (bit : Nat) : Byte :=
  match op with
  | .bt => base
  | .bts => base ||| btByteMaske bit
  | .btr => base &&& ~~~(btByteMaske bit)
  | .btc => if base.toNat.testBit bit then base &&& ~~~(btByteMaske bit)
      else base ||| btByteMaske bit

/-- Replace one byte (total: out-of-range keeps the list). -/
def btSetByte : List Byte → Nat → Byte → List Byte
  | [], _, _ => []
  | _ :: vs, 0, v => v :: vs
  | b :: vs, n + 1, v => b :: btSetByte vs n v

/-- Replacement keeps the length. -/
theorem btSetByte_laenge (vs : List Byte) (i : Nat) (v : Byte) :
    (btSetByte vs i v).length = vs.length := by
  induction vs generalizing i with
  | nil =>
    cases i <;> rfl
  | cons b rest ih =>
    cases i with
    | zero => rfl
    | succ k => simp [btSetByte, ih]

/-- Register-offset target: effective address plus bit-in-byte. -/
def btMemZielReg (s : Zustand) (base bitReg : Register)
    (disp : BitVec 32) : Adresse × Nat :=
  (btEffAddr s base bitReg disp, btBitImByte (btOffsetInt s bitReg))

/-- Imm-offset target: unsigned byte displacement plus bit-in-byte. -/
def btMemZielImm (s : Zustand) (base : Register)
    (disp : BitVec 32) (n : Nat) : Adresse × Nat :=
  (effAddr s base disp + BitVec.ofNat 64 (n / 8), n % 8)

/-- Machine-memory projection: re-embedding helpers read back. -/
theorem setTso_mem (m : HwMaschine) (s : TSOZustand) :
    (setTso m s).mem = s.mem := rfl

/-- Machine-buffer projection. -/
theorem setTso_puffer (m : HwMaschine) (s : TSOZustand) (c : Nat) :
    (setTso m s).puffer c = s.puffer c := rfl

/-- Machine-core projection. -/
theorem setTso_kerne (m : HwMaschine) (s : TSOZustand) (c : Nat) :
    (setTso m s).kerne c = m.kerne c := rfl

/-- Core-data memory projection. -/
theorem setKernDaten_mem (m : HwMaschine) (c : Nat) (k : HwKern) :
    (setKernDaten m c k).mem = m.mem := rfl

/-- Core-data projection at the updated core. -/
theorem setKernDaten_kerne_c (m : HwMaschine) (c : Nat) (k : HwKern) :
    (setKernDaten m c k).kerne c = k := by
  unfold setKernDaten
  simp

/-- A LOCK-prefixed row never decodes, on any suffix: the locked RMW
    stays with the locked families. -/
theorem decodeBt_lock (bs : List Byte) :
    decodeBt (natByte 240 :: bs) = none := by
  show (none : Option (BtForm × List Byte)) = none
  rfl

/-! ## 15. Memory RMW effect on the machine.

    One memory-form machine step: load the exact footprint through
    TSO byte events, modify exactly the byte holding the selected
    bit, issue the bytes back (buffered -- canonical memory moves
    only through the drain), set CF to the old bit and advance RIP.
    No register is written. Well-formedness survives (only core data
    moves, profiles untouched, memory/buffers through the accepted
    TSO equations). -/

/-- Read the operand word of a memory form through its footprint
    events. -/
def btMemLese (s : TSOZustand) (c : Nat) (w : BtWeite)
    (eff : Adresse) : Option (List Byte) :=
  btLadeListe s c (btFuss w eff)

/-- One memory-form machine step on core `c` at the effective address
    `eff` with bit-in-byte `bit`: footprint load, single-byte modify,
    buffered write-back, CF set, RIP advanced. `none` is load refusal
    or issue refusal -- never a partial word. -/
def btMemEffekt (m : HwMaschine) (c : Nat) (op : BtOp) (w : BtWeite)
    (eff : Adresse) (bit : Nat) (l : Nat) : Option HwMaschine :=
  match btMemLese (tsoAnsicht m) c w eff with
  | none => none
  | some vs =>
    let alt := (vs[0]?.getD 0).toNat.testBit bit
    let vs' := btSetByte vs 0 (btByteRoh op (vs[0]?.getD 0) bit)
    match btMemSchreibe (tsoAnsicht m) c (btFuss w eff) vs' with
    | none => none
    | some s1 =>
      let k := m.kerne c
      some (setTso (setKernDaten m c
        ⟨k.register, btFlags k.flags alt, ripNach k.rip l, k.xmm,
          k.fp⟩) s1)

/-- Every memory effect preserves well-formedness. -/
theorem btMemEffekt_wf (m : HwMaschine) (c : Nat) (op : BtOp)
    (w : BtWeite) (eff : Adresse) (bit l : Nat) (m' : HwMaschine)
    (hwf : HwWf m)
    (h : btMemEffekt m c op w eff bit l = some m') :
    HwWf m' := by
  unfold btMemEffekt at h
  cases hL : btMemLese (tsoAnsicht m) c w eff with
  | none =>
    simp only [hL] at h
    cases h
  | some vs =>
    simp only [hL] at h
    cases hS : btMemSchreibe (tsoAnsicht m) c (btFuss w eff)
        (btSetByte vs 0 (btByteRoh op (vs[0]?.getD 0) bit)) with
    | none =>
      simp only [hS] at h
      cases h
    | some s1 =>
      simp only [hS] at h
      cases h
      exact setTso_wf _ _ (setKernDaten_wf _ _ _ hwf)

/-- CF of a memory effect is the old selected byte bit. -/
theorem btMemEffekt_cf (m : HwMaschine) (c : Nat) (op : BtOp)
    (w : BtWeite) (eff : Adresse) (bit l : Nat) (m' : HwMaschine)
    (vs : List Byte)
    (hL : btMemLese (tsoAnsicht m) c w eff = some vs)
    (h : btMemEffekt m c op w eff bit l = some m') :
    ((m'.kerne c).flags).cf =
      ((vs[0]?.getD 0).toNat.testBit bit) := by
  unfold btMemEffekt at h
  simp only [hL] at h
  cases hS : btMemSchreibe (tsoAnsicht m) c (btFuss w eff)
      (btSetByte vs 0 (btByteRoh op (vs[0]?.getD 0) bit)) with
  | none =>
    simp only [hS] at h
    cases h
  | some s1 =>
    simp only [hS] at h
    cases h
    simp only [setTso_kerne, setKernDaten_kerne_c]
    rfl

/-- A memory effect advances RIP past the consumed length. -/
theorem btMemEffekt_rip (m : HwMaschine) (c : Nat) (op : BtOp)
    (w : BtWeite) (eff : Adresse) (bit l : Nat) (m' : HwMaschine)
    (vs : List Byte)
    (hL : btMemLese (tsoAnsicht m) c w eff = some vs)
    (h : btMemEffekt m c op w eff bit l = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip l := by
  unfold btMemEffekt at h
  simp only [hL] at h
  cases hS : btMemSchreibe (tsoAnsicht m) c (btFuss w eff)
      (btSetByte vs 0 (btByteRoh op (vs[0]?.getD 0) bit)) with
  | none =>
    simp only [hS] at h
    cases h
  | some s1 =>
    simp only [hS] at h
    cases h
    simp only [setTso_kerne, setKernDaten_kerne_c]

/-- A memory effect changes no canonical byte: the write-back is
    buffered, shared memory moves only through the drain. -/
theorem btMemEffekt_mem (m : HwMaschine) (c : Nat) (op : BtOp)
    (w : BtWeite) (eff : Adresse) (bit l : Nat) (m' : HwMaschine)
    (vs : List Byte) (x : Adresse)
    (hL : btMemLese (tsoAnsicht m) c w eff = some vs)
    (h : btMemEffekt m c op w eff bit l = some m') :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold btMemEffekt at h
  simp only [hL] at h
  cases hS : btMemSchreibe (tsoAnsicht m) c (btFuss w eff)
      (btSetByte vs 0 (btByteRoh op (vs[0]?.getD 0) bit)) with
  | none =>
    simp only [hS] at h
    cases h
  | some s1 =>
    simp only [hS] at h
    cases h
    have hmem := btMemSchreibe_mem _ s1 c _ _ hS x
    rw [setTso_mem, hmem, tsoAnsicht_speicher]

/-! ## 16. Joint witness: two cores, family steps, memory change.

    Core 0 runs BTS (sets a bit, CF keeps the old bit), core 1 runs
    BTR, both through the adapter on one shared memory; both cores
    also run a memory BTS through TSO events; a buffered byte store
    is forwarded to the owner only and the drain changes actual
    shared memory from 0 to 42. Decode pins, the LOCK refusal, the
    value laws and well-formedness stand beside the run. Every claim
    projects to plain values before `decide`. Non-degenerate: the
    drain changes actual shared memory and both cores write. -/

/-- Witness data window: readable and writable 8192..8200. -/
def btWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness shared memory: zeroed bytes, data window rw. -/
def btWitMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := btWitDaten
    schreibbar := btWitDaten
    ausfuehrbar := fun _ => false }

/-- Witness core-0 registers: rax holds 8, rcx the offset 1. -/
def btWitReg0 : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 8
  else if q = Register.rcx then BitVec.ofNat 64 1
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness core-1 registers: rbx holds 15, rcx the offset 0. -/
def btWitReg1 : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 15
  else BitVec.ofNat 64 0

/-- Witness cores over shared memory. -/
def btWitKern : Nat → HwKern
  | 0 => ⟨btWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨btWitReg1, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon. -/
def btWitStartM : HwMaschine :=
  ⟨btWitMem, btWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed: admission implies silicon
    through the accepted profile lemma. -/
theorem btWitStart_wf : HwWf btWitStartM := by
  intro c f h
  exact (merkmalZugelassen_heisst_beide _ _ f h).1

/-- Core 0 runs BTS rax, rcx through the adapter. -/
def btWitAd0 : Option HwMaschine :=
  (adapterBitTest).schritt btWitStartM 0
    ⟨.reg .bts .w64 .rax .rcx, 4⟩

/-- Core 1 runs BTR rbx, rcx through the adapter. -/
def btWitAd1 : Option HwMaschine :=
  (adapterBitTest).schritt btWitStartM 1
    ⟨.reg .btr .w64 .rbx .rcx, 4⟩

/-- Read a core register out of a machine outcome. -/
def btWitRegOut (o : Option HwMaschine) (c : Nat)
    (q : Register) : Option Wort :=
  match o with
  | some m => some ((m.kerne c).register q)
  | none => none

/-- Read CF out of a machine outcome. -/
def btWitCfOut (o : Option HwMaschine) (c : Nat) : Option Bool :=
  match o with
  | some m => some ((m.kerne c).flags.cf)
  | none => none

/-- Read a core RIP out of a machine outcome. -/
def btWitRipOut (o : Option HwMaschine) (c : Nat) : Option Wort :=
  match o with
  | some m => some (m.kerne c).rip
  | none => none

/-- Core 0 sets bit 1 of 8: rax becomes 10, CF keeps the old 0. -/
theorem btWit_ad0 :
    btWitRegOut btWitAd0 0 .rax = some 10 ∧
    btWitCfOut btWitAd0 0 = some false ∧
    btWitRipOut btWitAd0 0 = some (BitVec.ofNat 64 4100) := by
  decide

/-- Core 1 clears bit 0 of 15: rbx becomes 14, CF keeps the old 1. -/
theorem btWit_ad1 :
    btWitRegOut btWitAd1 1 .rbx = some 14 ∧
    btWitCfOut btWitAd1 1 = some true := by
  decide

/-- Witness TSO start: shared memory, empty buffers. -/
def btWitTso0 : TSOZustand := ⟨btWitMem, fun _ => []⟩

/-- Witness data address. -/
def btWitAdr : Adresse := BitVec.ofNat 64 8192

/-- Core 0 issues byte 42 at the data cell. -/
def btWitTso1 : Option TSOZustand :=
  issueByte btWitTso0 0 btWitAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def btWitEigen : Option (Option Byte) :=
  match btWitTso1 with
  | some s => some (loadByte s 0 btWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def btWitFremd : Option (Option Byte) :=
  match btWitTso1 with
  | some s => some (loadByte s 1 btWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def btWitTso2 : Option TSOZustand :=
  match btWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def btWitNachFlush : Option (Option Byte) :=
  match btWitTso2 with
  | some s => some (some (s.mem.bytes btWitAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def btWitFremdNachFlush : Option (Option Byte) :=
  match btWitTso2 with
  | some s => some (loadByte s 1 btWitAdr)
  | none => none

/-- The data cell starts zeroed: the run really changes memory. -/
theorem btWit_anfang_null :
    btWitMem.bytes btWitAdr = BitVec.ofNat 8 0 := by
  rfl

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem btWit_weiterleitung :
    btWitEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem btWit_fremd_alt :
    btWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem btWit_spuelung :
    btWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem btWit_fremd_neu :
    btWitFremdNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Core 0 runs a memory BTS (word 32, bit 3) through TSO events. -/
def btWitMemOut0 : Option HwMaschine :=
  btMemEffekt btWitStartM 0 .bts .w32 (BitVec.ofNat 64 8192) 3 8

/-- Core 1 runs a memory BTS (word 32, bit 0) through TSO events. -/
def btWitMemOut1 : Option HwMaschine :=
  btMemEffekt btWitStartM 1 .bts .w32 (BitVec.ofNat 64 8192) 0 8

/-- Read a shared-memory byte out of a machine outcome. -/
def btWitMemByte (o : Option HwMaschine) (a : Adresse) : Option Byte :=
  match o with
  | some m => some (m.mem.bytes a)
  | none => none

/-- Read a buffer length out of a machine outcome. -/
def btWitBuflen (o : Option HwMaschine) (c : Nat) : Option Nat :=
  match o with
  | some m => some (m.puffer c).length
  | none => none

/-- Core 0 memory BTS: CF keeps the old 0, memory still reads 0
    (buffered), four entries pending, RIP advanced by 8. -/
theorem btWit_mem0 :
    btWitCfOut btWitMemOut0 0 = some false ∧
    btWitMemByte btWitMemOut0 (BitVec.ofNat 64 8192) =
      some (BitVec.ofNat 8 0) ∧
    btWitBuflen btWitMemOut0 0 = some 4 ∧
    btWitRipOut btWitMemOut0 0 = some (BitVec.ofNat 64 4104) := by
  decide

/-- Core 1 memory BTS: CF keeps the old 0, four entries pending. -/
theorem btWit_mem1 :
    btWitCfOut btWitMemOut1 1 = some false ∧
    btWitBuflen btWitMemOut1 1 = some 4 := by
  decide

/-- Effective-address register file with a given offset word. -/
def btWitEffReg (off : Wort) : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rcx then off
  else BitVec.ofNat 64 0

/-- Effective-address state with offset 20. -/
def btWitEffS : Zustand :=
  ⟨btWitEffReg 20, zeugeFlags, BitVec.ofNat 64 0, btWitMem⟩

/-- Effective-address state with offset -1. -/
def btWitEffSNeg : Zustand :=
  ⟨btWitEffReg (BitVec.ofNat 64 (2 ^ 64 - 1)), zeugeFlags,
    BitVec.ofNat 64 0, btWitMem⟩

/-- Offset 20 moves two bytes up: the address is 8194. -/
theorem btWit_eff_pos :
    btEffAddr btWitEffS .rbx .rcx (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 8194 := by
  decide

/-- Offset -1 moves one byte down: the address is 8191. -/
theorem btWit_eff_neg :
    btEffAddr btWitEffSNeg .rbx .rcx (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 8191 := by
  decide

/-- Register-offset target: address plus bit-in-byte. -/
theorem btWit_zielReg :
    btMemZielReg btWitEffS .rbx .rcx (BitVec.ofNat 32 0) =
      (BitVec.ofNat 64 8194, 4) := by
  decide

/-- Imm-offset target: address plus bit-in-byte. -/
theorem btWit_zielImm :
    btMemZielImm btWitEffS .rbx (BitVec.ofNat 32 0) 20 =
      (BitVec.ofNat 64 8194, 4) := by
  decide

/-- The joint witness: a reached two-core bit-test run (register
    steps on both cores, memory steps on both cores through TSO
    events, a buffered store forwarded to the owner only and drained
    into shared memory with 0 becoming 42) beside decode pins, the
    LOCK refusal, value laws and well-formedness. Non-degenerate:
    both cores write and the drain changes actual shared memory. -/
theorem btWit_zeuge :
    btWitRegOut btWitAd0 0 .rax = some 10 ∧
    btWitCfOut btWitAd0 0 = some false ∧
    btWitRipOut btWitAd0 0 = some (BitVec.ofNat 64 4100) ∧
    btWitRegOut btWitAd1 1 .rbx = some 14 ∧
    btWitCfOut btWitAd1 1 = some true ∧
    btWitMem.bytes btWitAdr = BitVec.ofNat 8 0 ∧
    btWitEigen = some (some (BitVec.ofNat 8 42)) ∧
    btWitFremd = some (some (BitVec.ofNat 8 0)) ∧
    btWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
    btWitFremdNachFlush = some (some (BitVec.ofNat 8 42)) ∧
    btWitCfOut btWitMemOut0 0 = some false ∧
    btWitMemByte btWitMemOut0 (BitVec.ofNat 64 8192) =
      some (BitVec.ofNat 8 0) ∧
    btWitBuflen btWitMemOut0 0 = some 4 ∧
    btWitCfOut btWitMemOut1 1 = some false ∧
    btWitBuflen btWitMemOut1 1 = some 4 ∧
    btEffAddr btWitEffS .rbx .rcx (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 8194 ∧
    btEffAddr btWitEffSNeg .rbx .rcx (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 8191 ∧
    btMemZielReg btWitEffS .rbx .rcx (BitVec.ofNat 32 0) =
      (BitVec.ofNat 64 8194, 4) ∧
    decodeBtHw [natByte 72, natByte 15, natByte 187,
        natByte 200] =
      some (.bt ⟨.reg .btc .w64 .rax .rcx, 4⟩, []) ∧
    decodeBt (natByte 240 :: []) = none ∧
    btBit .b64 (btSchreibe .b64 8 (btRoh .bts .b64 8 3)) 3 = true ∧
    btBit .b64 (btSchreibe .b64 15 (btRoh .btr .b64 15 3)) 3 = false ∧
    HwWf btWitStartM := by
  refine ⟨btWit_ad0.1, btWit_ad0.2.1, btWit_ad0.2.2, btWit_ad1.1,
    btWit_ad1.2, btWit_anfang_null, btWit_weiterleitung,
    btWit_fremd_alt, btWit_spuelung, btWit_fremd_neu,
    btWit_mem0.1, btWit_mem0.2.1, btWit_mem0.2.2.1, btWit_mem1.1,
    btWit_mem1.2, btWit_eff_pos, btWit_eff_neg, btWit_zielReg,
    pin_btHw_reg64, decodeBt_lock [], bt_bts_setzt .b64 8 3,
    bt_btr_loescht .b64 15 3, btWitStart_wf⟩

/- CUTS:
   Proved here: the BT/BTS/BTR/BTC family over canonical words --
   value laws (set/reset/complement/frame, CF = old bit) through the
   accepted `getLsbD` bridge; a canonical byte codec (REX/66 prefix,
   0F A3/AB/B3/BB and 0F BA /4../7, register and base+disp32 memory
   forms) with round trips over any suffix, lengths within 1..15 and
   planted refusals (LOCK, 66+REX.W, REX.X, REX.R group, mod-0/1, bad
   digit/opcode/SIB, truncation); a length-checked register step with
   the flag class (CF pinned, ZF preserved, rest free) that never
   touches memory; a dispatcher preferring the accepted unified
   chain (no pilot or extension form shadowed, pinned per row); a
   `HwAdapter` register plug with exact agreement and planted
   refusals (memory forms never take it); the signed-offset memory
   footprint with floor-division displacement, TSO load/store events
   and a memory RMW effect (buffered write-back, CF set, RIP
   advanced, well-formedness preserved); and a reached non-degenerate
   two-core joint witness with owner-only forwarding and a
   memory-changing drain.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are a stated canonical
     subset with self-consistency (round trip) only, not verified
     against silicon. The SDM rows used (0F A3/AB/B3/BB, 0F BA
     /4../7, CF = selected bit, ZF unaffected, rest undefined,
     16/32/64-bit operand sizes, REX.W/66 prefix roles, LOCK RMW
     semantics, signed memory offset with moving address) are
     provenance in MUSE-REPORT-1277.md, not proofs. The imm8 memory
     offset is modelled unsigned (canonical reading, open against
     the SDM extracts).
   - No SIB-addressed (modrm rm = 4 with index/scale), mod-0/mod-1,
     RIP-relative or 8-bit forms (refused); no per-access
     target-to-W/GX simulation and no whole-word atomicity beyond
     byte drains; no source/IR/ABI/loader/entry/budget link.
   - The word-level bit correspondence between the byte-level memory
     path (`btByteRoh`) and the word-level evaluator (`btRoh`) is
     stated only on instances (witness pins), not as a general
     simulation.
   - Timing/power behaviour is absent.
-/

#print axioms pin_bt_opcode
#print axioms btIndex_schranke
#print axioms btMaske_bit_gleich
#print axioms btMaske_bit_anders
#print axioms btMasken_bit
#print axioms bt_bts_setzt
#print axioms bt_btr_loescht
#print axioms bt_btc_kehrt_um
#print axioms btMasken_bit_lt
#print axioms bt_bts_frame
#print axioms bt_btr_frame
#print axioms bt_btc_frame
#print axioms probe_bt_index
#print axioms probe_bt_werte
#print axioms rexBt_rund
#print axioms opcOp_btOpcode
#print axioms gruppeOp_btGruppe
#print axioms roundtripBtReg
#print axioms roundtripBtMemReg16
#print axioms roundtripBtMemReg32
#print axioms roundtripBtMemReg64
#print axioms roundtripBtImm
#print axioms roundtripBtMemImm
#print axioms btLaenge_encode
#print axioms btLaenge_ok
#print axioms pin_bt_dekode
#print axioms sonde_bt_abgeschnitten
#print axioms sonde_bt_verweigert
#print axioms btSchritt_laenge
#print axioms btSchritt_mem_verweigert
#print axioms btSchritt_reg
#print axioms btSchritt_speicher
#print axioms btSchritt_cf_reg
#print axioms btSchritt_erlaubt_reg
#print axioms decodeBtHw_prefers_ext
#print axioms decodeBtHw_bt
#print axioms ext_weist_btreg64_zurueck
#print axioms pin_btHw_reg64
#print axioms btHwSchritt_bt_ok
#print axioms adapterBitTest_wf
#print axioms adapterBitTest_ok
#print axioms adapterBitTest_verweigert_memReg
#print axioms btVersatz_rekon
#print axioms btEffAddr_null
#print axioms btFuss_laenge
#print axioms probe_bt_versatz
#print axioms btLadeListe_verweigert
#print axioms btMemSchreibe_mem
#print axioms btMemSchreibe_puffer
#print axioms btSetByte_laenge
#print axioms decodeBt_lock
#print axioms btMemEffekt_wf
#print axioms btMemEffekt_cf
#print axioms btMemEffekt_rip
#print axioms btMemEffekt_mem
#print axioms btWitStart_wf
#print axioms btWit_zeuge

end Gabbro.Grammatik.X86
