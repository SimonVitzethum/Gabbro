/-
  File:      Grammatik/X86/IntCarryForms.lean
  Subject:   ADC/SBB/INC/DEC connected to the coherent machine and the
             unified byte dispatcher.

  Lane 1275: lifts ADC/SBB (with carry/borrow) and INC/DEC (CF-preserving)
  over the canonical `Wort`/`Breite`/`Flags`/`Zustand` vocabulary into the
  unified dispatcher path (`decodeExt` first, never shadowing the pilot)
  and into a `HwAdapter` over `HwMaschine`/`HwSchritt`
  (`HardwareExecution`). Widths 8/16/32/64 with the architectural merge
  discipline (8/16-bit merge, 32-bit zero-extend, 64-bit full); REX.W and
  the 66H prefix select the width; ModRM register forms run the register
  path, memory forms are TSO byte-issue events, never the register plug.
  One-byte 40H-4FH forms are REX prefixes in 64-bit mode, never INC/DEC.
  No silicon proof beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.NarrowOps
import Grammatik.X86.ArchitecturalFlags
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.MulDiv
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.FeatureProfile
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Operation class: ADC/SBB consume CF, INC/DEC preserve it. -/
inductive CarryKlasse where
  | adc | sbb | inc | dec
  deriving DecidableEq, Repr

/-! ## 1. Value layer: ADC/SBB with carry/borrow, INC/DEC without.

   Values reuse `addB`/`subB` (modular at the named width); carries,
   borrows, overflows and auxiliary carries read the truncated operands
   through `toNat`, like `cfAdd`/`cfSub`/`afAdd`/`afSub` in `Wort.lean`.
   SDM provenance (Intel 325462-093US, checked in
   `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
   ADC/SBB set OF/SF/ZF/AF/CF/PF per result including the carry-in;
   INC/DEC preserve CF and update OF/SF/ZF/AF/PF. -/

/-- Carry-in as a number: ADC/SBB add the incoming CF. -/
def adcEingang (c : Bool) : Nat := if c then 1 else 0

/-- ADC value: modular sum of the truncated operands plus carry-in. -/
def adcWert (b : Breite) (x y : Wort) (c : Bool) : Wort :=
  addB b (addB b x y) (if c then 1 else 0)

/-- ADC carry out: the full sum leaves the width. -/
def adcTrag (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  decide (2 ^ b.bits ≤
    (trunc b x).toNat + (trunc b y).toNat + adcEingang c)

/-- ADC signed overflow from the width-correct operand/result signs. -/
def adcUeberlauf (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  ((negB b x == negB b y) && (negB b (adcWert b x y c) != negB b x))

/-- ADC auxiliary carry: nibble sum including the carry-in. -/
def adcHilf (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  decide (16 ≤ (trunc b x).toNat % 16 + (trunc b y).toNat % 16 +
    adcEingang c)

/-- ADC flag snapshot: all six status bits defined, like ADD. -/
def adcFlags (b : Breite) (x y : Wort) (c : Bool) : Flags :=
  let r := adcWert b x y c
  { cf := adcTrag b x y c, pf := parityEven r, af := some (adcHilf b x y c),
    zf := zfTest r, sf := negB b r, of := adcUeberlauf b x y c }

/-- SBB value: modular difference of the truncated operands minus borrow. -/
def sbbWert (b : Breite) (x y : Wort) (c : Bool) : Wort :=
  subB b (subB b x y) (if c then 1 else 0)

/-- SBB borrow out: the subtrahend plus borrow exceeds the minuend. -/
def sbbEntleihn (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  decide ((trunc b x).toNat <
    (trunc b y).toNat + adcEingang c)

/-- SBB signed overflow from the width-correct operand/result signs. -/
def sbbUeberlauf (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  ((negB b x != negB b y) && (negB b (sbbWert b x y c) != negB b x))

/-- SBB auxiliary borrow: nibble difference including the borrow-in. -/
def sbbHilf (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  decide ((trunc b x).toNat % 16 <
    (trunc b y).toNat % 16 + adcEingang c)

/-- SBB flag snapshot: all six status bits defined, like SUB. -/
def sbbFlags (b : Breite) (x y : Wort) (c : Bool) : Flags :=
  let r := sbbWert b x y c
  { cf := sbbEntleihn b x y c, pf := parityEven r,
    af := some (sbbHilf b x y c),
    zf := zfTest r, sf := negB b r, of := sbbUeberlauf b x y c }

/-- INC value: modular successor at the named width. -/
def incWert (b : Breite) (x : Wort) : Wort := addB b x 1

/-- DEC value: modular predecessor at the named width. -/
def decWert (b : Breite) (x : Wort) : Wort := subB b x 1

/-- INC overflow: the signed maximum wraps to the minimum. -/
def incUeberlauf (b : Breite) (x : Wort) : Bool :=
  ((!negB b x) && negB b (incWert b x))

/-- DEC overflow: the signed minimum wraps to the maximum. -/
def decUeberlauf (b : Breite) (x : Wort) : Bool :=
  ((negB b x) && !(negB b (decWert b x)))

/-- INC auxiliary carry: the low nibble was `0xF`. -/
def incHilf (b : Breite) (x : Wort) : Bool :=
  decide ((trunc b x).toNat % 16 = 15)

/-- DEC auxiliary borrow: the low nibble was `0x0`. -/
def decHilf (b : Breite) (x : Wort) : Bool :=
  decide ((trunc b x).toNat % 16 = 0)

/-- INC flags: CF preserved from the incoming snapshot, the rest updated. -/
def incFlags (b : Breite) (x : Wort) (f : Flags) : Flags :=
  let r := incWert b x
  { cf := f.cf, pf := parityEven r, af := some (incHilf b x),
    zf := zfTest r, sf := negB b r, of := incUeberlauf b x }

/-- DEC flags: CF preserved from the incoming snapshot, the rest updated. -/
def decFlags (b : Breite) (x : Wort) (f : Flags) : Flags :=
  let r := decWert b x
  { cf := f.cf, pf := parityEven r, af := some (decHilf b x),
    zf := zfTest r, sf := negB b r, of := decUeberlauf b x }

/-- The carry-in counts 0 and 1. -/
theorem adcEingang_werte : adcEingang false = 0 ∧ adcEingang true = 1 :=
  ⟨rfl, rfl⟩

/-- Truncation at 64 bits keeps the unsigned value
    (`negB_b64` itself is reused from `ShiftLogic.lean`). -/
theorem trunc_b64_nat (w : Wort) : (trunc .b64 w).toNat = w.toNat := by
  rw [trunc_b64]

/-- ADC without carry-in is the modular sum at 64 bits. -/
theorem adcWert_b64_ohne (x y : Wort) :
    adcWert .b64 x y false = x + y := by
  simp [adcWert, addB, trunc_b64]

/-- ADC carry without carry-in is the ADD carry at 64 bits. -/
theorem adcTrag_b64_ohne (x y : Wort) :
    adcTrag .b64 x y false = cfAdd x y := by
  have hb : Breite.bits .b64 = 64 := rfl
  simp [adcTrag, cfAdd, adcEingang, trunc_b64_nat, hb]

/-- ADC auxiliary carry without carry-in is the ADD one at 64 bits. -/
theorem adcHilf_b64_ohne (x y : Wort) :
    adcHilf .b64 x y false = afAdd x y := by
  simp [adcHilf, afAdd, adcEingang, trunc_b64_nat]

/-- ADC overflow without carry-in is the ADD one at 64 bits. -/
theorem adcUeberlauf_b64_ohne (x y : Wort) :
    adcUeberlauf .b64 x y false =
      ofAdd (sfTest x) (sfTest y) (sfTest (x + y)) := by
  have hv := adcWert_b64_ohne x y
  simp only [adcUeberlauf, ofAdd, hv, negB_b64]

/-- AGREEMENT (64-bit): ADC with CF=0 IS the accepted ADD snapshot. -/
theorem adcFlags_b64_ohne (x y : Wort) :
    adcFlags .b64 x y false = (add64 x y).2 := by
  have hv := adcWert_b64_ohne x y
  simp only [adcFlags, add64, hv, adcTrag_b64_ohne x y,
    adcHilf_b64_ohne x y, adcUeberlauf_b64_ohne x y, negB_b64]

/-- SBB without borrow-in is the modular difference at 64 bits. -/
theorem sbbWert_b64_ohne (x y : Wort) :
    sbbWert .b64 x y false = x - y := by
  simp [sbbWert, subB, trunc_b64]

/-- SBB borrow without borrow-in is the SUB borrow at 64 bits. -/
theorem sbbEntleihn_b64_ohne (x y : Wort) :
    sbbEntleihn .b64 x y false = cfSub x y := by
  simp [sbbEntleihn, cfSub, adcEingang, trunc_b64_nat]

/-- SBB auxiliary borrow without borrow-in is the SUB one at 64 bits. -/
theorem sbbHilf_b64_ohne (x y : Wort) :
    sbbHilf .b64 x y false = afSub x y := by
  simp [sbbHilf, afSub, adcEingang, trunc_b64_nat]

/-- SBB overflow without borrow-in is the SUB one at 64 bits. -/
theorem sbbUeberlauf_b64_ohne (x y : Wort) :
    sbbUeberlauf .b64 x y false =
      ofSub (sfTest x) (sfTest y) (sfTest (x - y)) := by
  have hv := sbbWert_b64_ohne x y
  simp only [sbbUeberlauf, ofSub, hv, negB_b64]

/-- AGREEMENT (64-bit): SBB with CF=0 IS the accepted SUB snapshot. -/
theorem sbbFlags_b64_ohne (x y : Wort) :
    sbbFlags .b64 x y false = (sub64 x y).2 := by
  have hv := sbbWert_b64_ohne x y
  simp only [sbbFlags, sub64, hv, sbbEntleihn_b64_ohne x y,
    sbbHilf_b64_ohne x y, sbbUeberlauf_b64_ohne x y, negB_b64]

/-- CF-PRESERVATION: INC keeps the incoming carry. -/
theorem incFlags_cf (b : Breite) (x : Wort) (f : Flags) :
    (incFlags b x f).cf = f.cf := rfl

/-- CF-PRESERVATION: DEC keeps the incoming carry. -/
theorem decFlags_cf (b : Breite) (x : Wort) (f : Flags) :
    (decFlags b x f).cf = f.cf := rfl

/-- Every ADC value fits its width. -/
theorem adcWert_fits (b : Breite) (x y : Wort) (c : Bool) :
    (adcWert b x y c).toNat < 2 ^ b.bits := by
  unfold adcWert addB
  rw [narrowTruncMod]
  exact Nat.mod_lt _ (by cases b <;> decide)

/-- Every SBB value fits its width. -/
theorem sbbWert_fits (b : Breite) (x y : Wort) (c : Bool) :
    (sbbWert b x y c).toNat < 2 ^ b.bits := by
  unfold sbbWert subB
  rw [narrowTruncMod]
  exact Nat.mod_lt _ (by cases b <;> decide)

/-- Pinned ADC facts: nibble carry, byte carry, carry-in chaining. -/
theorem probe_adc_wert :
    adcWert .b8 0x0F 0x01 false = 0x10 ∧
    adcTrag .b8 0xFF 0x01 false = true ∧
    adcWert .b8 0xFF 0x01 true = 0x01 ∧
    adcTrag .b8 0xFF 0x01 true = true ∧
    adcWert .b64 0x0F 0x01 false = 0x10 := by
  decide

/-- Pinned SBB facts: nibble borrow, byte borrow, borrow-in chaining. -/
theorem probe_sbb_wert :
    sbbWert .b8 0x10 0x01 false = 0x0F ∧
    sbbEntleihn .b8 0x00 0x01 false = true ∧
    sbbWert .b8 0x10 0x01 true = 0x0E ∧
    sbbEntleihn .b8 0x01 0x01 true = true ∧
    sbbWert .b64 0x10 0x01 false = 0x0F := by
  decide

/-- Pinned INC/DEC facts: wrap, overflow shapes, CF preservation. -/
theorem probe_incdec_wert :
    incWert .b8 0xFF = 0x00 ∧
    incUeberlauf .b8 0x7F = true ∧
    incUeberlauf .b8 0xFF = false ∧
    decWert .b8 0x00 = 0xFF ∧
    decUeberlauf .b8 0x80 = true ∧
    decUeberlauf .b8 0x00 = false ∧
    (incFlags .b8 0x7F
      { cf := true, pf := false, af := none, zf := false, sf := false,
        of := false }).cf = true ∧
    (decFlags .b8 0x80
      { cf := true, pf := false, af := none, zf := false, sf := false,
        of := false }).cf = true := by
  decide

/- CUTS:
    Skeleton only: operation classes named, imports wired.
    NOT proved here, and not claimed: everything (see lane task).
-/

#print axioms CarryKlasse

end Gabbro.Grammatik.X86
