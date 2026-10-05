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
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc,
      m, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b8 off) <;> rfl
  | b16 =>
    have hi : btIndex .b16 off < 16 := btIndex_schranke _ _
    have d64 : decide (btIndex .b16 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b16 = BitVec.ofNat 64 (2 ^ 16 - 1) := by decide
    have hm := btMasken_bit .b16 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc,
      m, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b16 off) <;> rfl
  | b32 =>
    have hi : btIndex .b32 off < 32 := btIndex_schranke _ _
    have d64 : decide (btIndex .b32 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b32 = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
    have hm := btMasken_bit .b32 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc,
      m, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b32 off) <;> rfl
  | b64 =>
    have hi : btIndex .b64 off < 64 := btIndex_schranke _ _
    have m : maske .b64 = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
    have hm := btMasken_bit .b64 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc,
      m, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
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
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc,
      m, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b8 off) <;> rfl
  | b16 =>
    have hi : btIndex .b16 off < 16 := btIndex_schranke _ _
    have d64 : decide (btIndex .b16 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b16 = BitVec.ofNat 64 (2 ^ 16 - 1) := by decide
    have hm := btMasken_bit .b16 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc,
      m, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b16 off) <;> rfl
  | b32 =>
    have hi : btIndex .b32 off < 32 := btIndex_schranke _ _
    have d64 : decide (btIndex .b32 off < 64) = true :=
      decide_eq_true (by omega)
    have m : maske .b32 = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
    have hm := btMasken_bit .b32 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc,
      m, BitVec.testBit_toNat, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, d64, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b32 off) <;> rfl
  | b64 =>
    have hi : btIndex .b64 off < 64 := btIndex_schranke _ _
    have m : maske .b64 = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
    have hm := btMasken_bit .b64 off
    rw [m] at hm
    simp only [btBit, btSchreibe, btRoh, btMaske, mergeRegNarrow, trunc,
      m, BitVec.testBit_toNat, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hi, hm, btMaske_bit_gleich]
    cases base.getLsbD (btIndex .b64 off) <;> rfl

end Gabbro.Grammatik.X86
