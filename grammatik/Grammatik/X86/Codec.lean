/-
  Byte codec pilot for the direct x86-64 validation (lane 279, wave B).
  Canonical bytes for every `Befehl` per `dokumente/x86/BYTE-PILOT.md`;
  the decoder parses bytes (never encode-equality); no hardware or
  source correspondence is claimed here.
-/
import Grammatik.X86.Typen

namespace Gabbro.Grammatik.X86

/-- Architectural register code: rax=0 through r15=15. -/
def regCode : Register → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3
  | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

/-- Inverse check: 4-bit code back to a register. -/
def codeReg : Nat → Option Register
  | 0 => some .rax | 1 => some .rcx | 2 => some .rdx | 3 => some .rbx
  | 4 => some .rsp | 5 => some .rbp | 6 => some .rsi | 7 => some .rdi
  | 8 => some .r8 | 9 => some .r9 | 10 => some .r10 | 11 => some .r11
  | 12 => some .r12 | 13 => some .r13 | 14 => some .r14 | 15 => some .r15
  | _ => none

/-- Decoding inverts encoding on every register. -/
theorem codeReg_regCode (r : Register) : codeReg (regCode r) = some r := by
  cases r <;> rfl

/-- Every register code fits in four bits. -/
theorem regCode_lt (r : Register) : regCode r < 16 := by
  cases r <;> decide

/-- Condition code follows `Bedingung` order 0 through 15. -/
def condCode : Bedingung → Nat
  | .o => 0 | .no => 1 | .b => 2 | .ae => 3
  | .e => 4 | .ne => 5 | .be => 6 | .a => 7
  | .s => 8 | .ns => 9 | .p => 10 | .np => 11
  | .l => 12 | .ge => 13 | .le => 14 | .g => 15

/-- Inverse check: low nibble back to a condition. -/
def codeCond : Nat → Option Bedingung
  | 0 => some .o | 1 => some .no | 2 => some .b | 3 => some .ae
  | 4 => some .e | 5 => some .ne | 6 => some .be | 7 => some .a
  | 8 => some .s | 9 => some .ns | 10 => some .p | 11 => some .np
  | 12 => some .l | 13 => some .ge | 14 => some .le | 15 => some .g
  | _ => none

/-- Decoding inverts encoding on every condition. -/
theorem codeCond_condCode (c : Bedingung) : codeCond (condCode c) = some c := by
  cases c <;> rfl

/-- Every condition code fits in four bits. -/
theorem condCode_lt (c : Bedingung) : condCode c < 16 := by
  cases c <;> decide

/- CUTS:
   Encoder, decoder, length bounds, round-trip, refusals and pinned bytes
   are not yet present; they arrive in small checked increments.
   No execution, TSO-bridge, ABI or source-correspondence claim is made here.
-/

#print axioms codeReg_regCode
#print axioms codeCond_condCode

end Gabbro.Grammatik.X86
