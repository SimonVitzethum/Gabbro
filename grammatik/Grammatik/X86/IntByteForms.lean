/-
  File:      Grammatik/X86/IntByteForms.lean
  Subject:   8-bit operand forms across the new integer families.

  Lane 1319: byte-register selection with the architectural REX rule
  (AL/CL/DL/BL always; SPL/BPL/SIL/DIL only with REX; AH/CH/DH/BH
  only without REX, outside the `Register` vocabulary), the 8-bit
  merge discipline (merge into the low byte, never zero-extend),
  and the 8-bit rotate / ADC-SBB-INC-DEC / XCHG connections through
  the accepted evaluators with decode/encode round trips plus a
  `HwAdapter` over the coherent machine. Reuses the accepted
  definitions unchanged, never copies a model. No silicon proof
  beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.NarrowOps
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Byte-register target of a full register code under a REX flag:
    codes 0-3 are AL/CL/DL/BL in every mode; codes 4-7 are
    SPL/BPL/SIL/DIL with REX and the high bytes AH/CH/DH/BH
    without REX (outside the `Register` vocabulary, so refused);
    codes 8-15 are R8B-R15B and need REX; the rest refuses. -/
def byteZielReg : Nat → Bool → Option Register
  | 0, _ => some .rax
  | 1, _ => some .rcx
  | 2, _ => some .rdx
  | 3, _ => some .rbx
  | 4, true => some .rsp
  | 5, true => some .rbp
  | 6, true => some .rsi
  | 7, true => some .rdi
  | 8, true => some .r8
  | 9, true => some .r9
  | 10, true => some .r10
  | 11, true => some .r11
  | 12, true => some .r12
  | 13, true => some .r13
  | 14, true => some .r14
  | 15, true => some .r15
  | _, _ => none

/-- Low codes name the classic low bytes with or without REX. -/
theorem byteZielReg_tief (code : Nat) (rex : Bool) (h : code < 4) :
    byteZielReg code rex = codeReg code := by
  cases code with
  | zero => cases rex <;> rfl
  | succ n =>
    cases n with
    | zero => cases rex <;> rfl
    | succ n =>
      cases n with
      | zero => cases rex <;> rfl
      | succ n =>
        cases n with
        | zero => cases rex <;> rfl
        | succ _ => omega

/- CUTS:
   Skeleton only: selection function plus the low-code agreement.
   Merge pins, family lifts, codecs, adapter, witness remain open.
-/

#print axioms byteZielReg_tief

end Gabbro.Grammatik.X86
