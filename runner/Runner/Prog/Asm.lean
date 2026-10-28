import Runner.X86.Enc

/-! # A two-pass assembler with labels

An item is an instruction, a label, a jump to a label (`rel32`, so its length does not depend on the distance) or
`mov r, imm32` of a label's absolute address. The first pass computes the offsets, the second the bytes. Lengths
never depend on label values, so two passes are exact. -/

namespace Runner.Prog
open Runner.X86

inductive Item
  | i (x : Ins)
  | lab (l : Nat)
  | jmpL (l : Nat)
  | jccL (c : Cond) (l : Nat)
  | adr (d : Reg) (l : Nat)

def Item.len : Item → Nat
  | .i x => (enc x).length
  | .lab _ => 0
  | .jmpL _ => 5
  | .jccL _ _ => 6
  | .adr _ _ => 7

/-- The offset of every label, from `o`. -/
def labels : List Item → Nat → List (Nat × Nat)
  | [], _ => []
  | .lab l :: r, o => (l, o) :: labels r o
  | it :: r, o => labels r (o + it.len)

def find (t : List (Nat × Nat)) (l : Nat) : Nat := ((t.find? (·.1 == l)).map (·.2)).getD 0

/-- The instruction an item stands for, at offset `o` (relative jumps are relative to the end of the item). -/
def Item.ins (t : List (Nat × Nat)) (base o : Nat) : Item → Option Ins
  | .i x => some x
  | .lab _ => none
  | .jmpL l => some (.jmp (BitVec.ofInt 32 ((find t l : Int) - (o + 5))))
  | .jccL c l => some (.jcc c (BitVec.ofInt 32 ((find t l : Int) - (o + 6))))
  | .adr d l => some (.movi d (BitVec.ofNat 32 (base + find t l)))

/-- The instructions with their offsets. -/
def place (t : List (Nat × Nat)) (base : Nat) : List Item → Nat → List (Nat × Ins)
  | [], _ => []
  | it :: r, o => match it.ins t base o with
    | some x => (o, x) :: place t base r (o + it.len)
    | none => place t base r (o + it.len)

end Runner.Prog
