/-
  File:      Grammatik/X86/ArchitecturalFlags.lean
  Subject:   Raw RFLAGS word with defined/undefined flag effects and the
             fetched PUSHFQ/POPFQ observers.

  Lane 692 (hardware completion): the existing `Flags` snapshot stores
  every flag but AF as `Bool`, and `mulFlagsU` preserves incoming
  SF/ZF/PF as an explicit modelling choice (MulDiv.lean §2), not
  hardware truth. This file adds the raw 64-bit RFLAGS word beside it,
  a sound defined/undefined effect relation per manual row (undefined
  bits are free choices, never invented zeros or preserved values),
  and the byte-facing PUSHFQ (opcode 9CH) / POPFQ observers with
  VM/RF treatment and CPL/IOPL gating.

  Provenance (checked 2026-10-02 in
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  Intel SDM 325462-093US September 2026):
  - ADD entry (Vol. 2A 3-14): "The OF, SF, ZF, AF, CF, and PF flags are
    set according to the result."
  - NEG entry: "The CF flag set to 0 if the source operand is 0;
    otherwise it is set to 1. The OF, SF, ZF, AF, and PF flags are set
    according to the result."
  - MUL entry: "The OF and CF flags are set to 0 if the upper half of
    the result is 0; otherwise, they are set to 1. The SF, ZF, AF, and
    PF flags are undefined." IMUL/DIV/IDIV/SHL rows likewise.
  - PUSHFQ entry (Vol. 2B 4-528): 64-bit mode pushes RFLAGS with
    "VM and RF bits cleared in image stored on the stack";
    "Flags Affected: None."
  - POPFQ entry (Vol. 2B 4-407): Table 1-12 CPL/IOPL gating; RF is
    cleared; VIP/VIF/VM/reserved unaffected.
  - Vol. 1 3.4.3: EFLAGS init 00000002H (bit 1 set); reserved bits
    1, 3, 5, 15, 22-31; Figure 3-8 bit positions.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.ShiftLogic
import Grammatik.X86.MulDiv

namespace Gabbro.Grammatik.X86

/-- RFLAGS status bit positions (Intel SDM Vol. 1 Figure 3-8). -/
def cfBit : Nat := 0
def pfBit : Nat := 2
def afBit : Nat := 4
def zfBit : Nat := 6
def sfBit : Nat := 7
def ofBit : Nat := 11

/-- One raw status bit of a word. -/
def rbit (w : Wort) (i : Nat) : Bool := w.toNat.testBit i

/-- Control/privilege state beside the flags: CPL and IOPL gate POPFQ,
    IF is the interrupt flag, VM marks virtual-8086 mode. -/
structure Steuer where
  cpl : Nat
  iopl : Nat
  ifBit : Bool
  vm : Bool
  deriving DecidableEq, Repr

/-- Architectural state: the canonical core plus the raw RFLAGS word
    plus control state. `archOK` ties the raw status bits to
    `kern.flags`; projection is `projiziert`. -/
structure ArchZustand where
  kern : Zustand
  roh : Wort
  steuer : Steuer

/-- Read the six status flags out of a raw word. AF is always present
    as a raw bit here; undefinedness lives in the effect relation
    (§4), never in the state. -/
def liestStatus (w : Wort) : Flags :=
  { cf := rbit w cfBit, pf := rbit w pfBit, af := some (rbit w afBit),
    zf := rbit w zfBit, sf := rbit w sfBit, of := rbit w ofBit }

/-- Coherence: the raw word agrees with the canonical flags on every
    status bit, bit 1 reads set (init 00000002H, Vol. 1 3.4.3), and
    privilege values are in range. -/
def archOK (a : ArchZustand) : Prop :=
  liestStatus a.roh = a.kern.flags ∧ rbit a.roh 1 = true ∧
  a.steuer.cpl ≤ 3 ∧ a.steuer.iopl ≤ 3

/-- Projection to the existing state: forget raw word and control. -/
def projiziert (a : ArchZustand) : Zustand := a.kern

/-- The projection reads the canonical flags back. -/
theorem projiziert_flags (a : ArchZustand) (h : archOK a) :
    liestStatus a.roh = (projiziert a).flags := by
  unfold projiziert
  exact h.1

/-! ## 3. Defined AF per width for ADD/SUB/CMP/NEG.

    AF is the carry out of bit 3 (Wort.afAdd/afSub): it reads only the
    low nibbles, so truncation to any pilot width keeps it. The three
    lemmas below reuse the canonical `afAdd`/`afSub` (no second
    nibble computation); the manual rows are ADD (Vol. 2A 3-14: all six
    "set according to the result"), NEG (CF is the nonzero borrow, the
    other five per result), SUB/CMP (same sentence as ADD). -/

/-- A mask keeping the low nibble fixes `% 16`. -/
theorem and_maske_nibble (m : Nat) (hm : ∀ i, i < 4 → m.testBit i = true)
    (x : Nat) : (x &&& m) % 16 = x % 16 := by
  show (x &&& m) % 2 ^ 4 = x % 2 ^ 4
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_and]
  by_cases h : i < 4
  · rw [hm i h]
    simp [h]
  · simp [h]

/-- Every pilot mask keeps the low nibble. -/
theorem maske_nibble (b : Breite) (i : Nat) (h : i < 4) :
    (maske b).toNat.testBit i = true := by
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  cases b with
  | b8 => have e : (maske .b8).toNat = 255 := by decide
          rw [e]; rcases h4 with rfl | rfl | rfl | rfl <;> decide
  | b16 => have e : (maske .b16).toNat = 65535 := by decide
           rw [e]; rcases h4 with rfl | rfl | rfl | rfl <;> decide
  | b32 => have e : (maske .b32).toNat = 4294967295 := by decide
           rw [e]; rcases h4 with rfl | rfl | rfl | rfl <;> decide
  | b64 => have e : (maske .b64).toNat = 18446744073709551615 := by decide
           rw [e]; rcases h4 with rfl | rfl | rfl | rfl <;> decide

/-- Truncation to any pilot width keeps the low nibble. -/
theorem trunc_nibble (b : Breite) (x : Wort) :
    (trunc b x).toNat % 16 = x.toNat % 16 := by
  cases b with
  | b8 => simp only [trunc, maske, BitVec.toNat_and]
          exact and_maske_nibble _ (maske_nibble .b8) _
  | b16 => simp only [trunc, maske, BitVec.toNat_and]
           exact and_maske_nibble _ (maske_nibble .b16) _
  | b32 => simp only [trunc, maske, BitVec.toNat_and]
           exact and_maske_nibble _ (maske_nibble .b32) _
  | b64 => simp only [trunc, maske, BitVec.toNat_and]
           exact and_maske_nibble _ (maske_nibble .b64) _

/-- Per-width ADD auxiliary carry, read off the truncated nibbles. -/
def afAddB (b : Breite) (x y : Wort) : Bool :=
  decide (16 ≤ (trunc b x).toNat % 16 + (trunc b y).toNat % 16)

/-- Per-width SUB auxiliary borrow, read off the truncated nibbles. -/
def afSubB (b : Breite) (x y : Wort) : Bool :=
  decide ((trunc b x).toNat % 16 < (trunc b y).toNat % 16)

/-- The per-width ADD carry is the canonical nibble carry: width plays
    no role beyond the low four bits. -/
theorem afAddB_ist_afAdd (b : Breite) (x y : Wort) :
    afAddB b x y = afAdd x y := by
  simp only [afAddB, afAdd]
  rw [trunc_nibble b x, trunc_nibble b y]

/-- The per-width SUB borrow is the canonical nibble borrow. -/
theorem afSubB_ist_afSub (b : Breite) (x y : Wort) :
    afSubB b x y = afSub x y := by
  simp only [afSubB, afSub]
  rw [trunc_nibble b x, trunc_nibble b y]

/-- NEG auxiliary borrow at width `b`: the accepted `negWf` snapshot
    pins `afSub 0 (trunc b x)` (NegGueltig); it equals the canonical
    borrow out of the full word. -/
theorem negAf_ist_afSub (b : Breite) (x : Wort) :
    afSub 0 (trunc b x) = afSub 0 x := by
  simp only [afSub]
  rw [trunc_nibble b x]

/-- CMP shares the SUB flag row (CMP is SUB without the store:
    `schritt` evaluates `sub64` for `.cmpReg64`); hence per-width CMP
    AF is `afSubB`, i.e. the canonical borrow. -/
theorem cmpAf_ist_afSub (b : Breite) (x y : Wort) :
    afSubB b x y = afSub x y :=
  afSubB_ist_afSub b x y

/- CUTS:
    Skeleton plus raw word (§2) and nibble groundwork (§3 head):
    effect relation, PUSHFQ/POPFQ observers, consumer admission and
    witnesses follow in later pieces.
-/

#print axioms projiziert_flags
#print axioms and_maske_nibble
#print axioms maske_nibble
#print axioms trunc_nibble
#print axioms afAddB_ist_afAdd
#print axioms afSubB_ist_afSub
#print axioms negAf_ist_afSub
#print axioms cmpAf_ist_afSub

end Gabbro.Grammatik.X86
