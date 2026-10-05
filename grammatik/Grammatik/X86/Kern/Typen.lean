/-
  Shared syntax and state vocabulary for the direct x86-64 validation pilot.
  This file defines data, not instruction semantics or hardware correspondence.
-/
import Std

namespace Gabbro.Grammatik.X86

abbrev Byte := BitVec 8
abbrev Wort := BitVec 64
abbrev Adresse := BitVec 64

inductive Register where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

inductive Breite where
  | b8 | b16 | b32 | b64
  deriving DecidableEq, Repr, Inhabited

def Breite.bits : Breite → Nat
  | .b8 => 8 | .b16 => 16 | .b32 => 32 | .b64 => 64

def Breite.bytes (b : Breite) : Nat := b.bits / 8

structure Flags where
  cf : Bool
  pf : Bool
  af : Option Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving DecidableEq, Repr

inductive Bedingung where
  | o | no | b | ae | e | ne | be | a
  | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr, Inhabited

structure Speicher where
  bytes : Adresse → Byte
  lesbar : Adresse → Bool
  schreibbar : Adresse → Bool
  ausfuehrbar : Adresse → Bool

structure Zustand where
  register : Register → Wort
  flags : Flags
  rip : Adresse
  speicher : Speicher

inductive Befehl where
  | movImm64 (dst : Register) (value : Wort)
  | movReg64 (dst src : Register)
  | addReg64 (dst src : Register)
  | subReg64 (dst src : Register)
  | xorReg64 (dst src : Register)
  | cmpReg64 (lhs rhs : Register)
  | load64 (dst base : Register) (disp : BitVec 32)
  | store64 (base src : Register) (disp : BitVec 32)
  | jump32 (disp : BitVec 32)
  | jumpIf32 (cond : Bedingung) (disp : BitVec 32)
  | call32 (disp : BitVec 32)
  | push64 (src : Register)
  | pop64 (dst : Register)
  | ret
  deriving DecidableEq, Repr

structure Decodiert where
  befehl : Befehl
  laenge : Nat
  deriving DecidableEq, Repr

/-- The initial data widths are positive and at most eight bytes. -/
theorem breite_bytes (b : Breite) : 0 < b.bytes ∧ b.bytes ≤ 8 := by
  cases b <;> decide

#print axioms breite_bytes

/- CUTS:
   No instruction execution, decoder, encoding, TSO bridge, source correspondence,
   ABI/loader theorem, cost transfer or final-image acceptance is proved here.
   AF = none represents an undefined architectural auxiliary flag, not false.
   The initial instruction syntax is a pilot subset; other widths/forms remain open.
-/
end Gabbro.Grammatik.X86
