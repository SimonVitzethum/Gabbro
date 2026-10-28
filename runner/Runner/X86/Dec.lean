import Runner.X86.Enc

/-! # Decoding: bytes to the instruction forms of the subset

`decode l` reads the instruction at the start of `l` and answers it with its length, or `none` for every byte
sequence outside the subset (the model then does not describe the step). The decoder reads only the bytes of the
instruction it answers. What it answers for a byte sequence is what an x86-64 processor executes for it: that is
checked on the CPU by the differential tests (`Runner/Test/`). -/

namespace Runner.X86

/-- Byte `j` of `l` as a number (0 past the end). -/
def bt (l : List B) (j : Nat) : Nat := (l.getD j 0).toNat

def imm32 (l : List B) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (bt l j + 256 * bt l (j + 1) + 65536 * bt l (j + 2) + 16777216 * bt l (j + 3))

def Alu.ofOpc : Nat → Option Alu
  | 0x01 => some .add | 0x09 => some .or | 0x21 => some .and | 0x29 => some .sub
  | 0x31 => some .xor | 0x39 => some .cmp | 0x85 => some .test | _ => none

def Alu.ofExt : Nat → Option Alu
  | 0 => some .add | 1 => some .or | 4 => some .and | 5 => some .sub | 6 => some .xor | 7 => some .cmp
  | _ => none

def Cond.ofCc : Nat → Option Cond
  | 4 => some .z | 5 => some .nz | 8 => some .s | 12 => some .l | _ => none

/-- The operand of the ModRM byte at `p` under REX bits `r x b`: a register (`mod=11`, length 1) or a SIB memory
    operand (`mod=10 rm=100`, length 6); `g` is the reg field with REX.R. -/
inductive Opd
  | reg (g rm : Nat)
  | mem (g : Nat) (m : Addr)

def opd (l : List B) (p r x b : Nat) : Option (Opd × Nat) :=
  let mr := bt l p
  let g := mr / 8 % 8 + 8 * r
  if mr / 64 = 3 then some (.reg g (mr % 8 + 8 * b), p + 1)
  else if mr / 64 = 2 ∧ mr % 8 = 4 then
    let s := bt l (p + 1)
    let i := s / 8 % 8
    let idx := if i = 4 ∧ x = 0 then none else some (Reg.ofNum (i + 8 * x))
    some (.mem g { base := Reg.ofNum (s % 8 + 8 * b), idx := idx, sc := s / 64, disp := imm32 l (p + 2) }, p + 6)
  else none

/-- The forms behind REX.W = 1 with a one-byte opcode `o` at position 2 (ModRM at 2). -/
def decW (l : List B) (o r x b : Nat) : Option (Ins × Nat) :=
  match opd l 2 r x b with
  | none => none
  | some (.mem g m, n) =>
    match o with
    | 0x8B => some (.ld (Reg.ofNum g) m, n)
    | 0x89 => some (.st m (Reg.ofNum g), n)
    | 0x63 => some (.ldsx (Reg.ofNum g) m, n)
    | 0x8D => some (.lea (Reg.ofNum g) m, n)
    | _ => none
  | some (.reg g rm, n) =>
    match o with
    | 0x89 => some (.mov (Reg.ofNum rm) (Reg.ofNum g), n)
    | 0xC7 => if g % 8 = 0 then some (.movi (Reg.ofNum rm) (imm32 l n), n + 4) else none
    | 0x81 => (Alu.ofExt (g % 8)).map fun a => (.alui a (Reg.ofNum rm) (imm32 l n), n + 4)
    | 0xF7 => if g % 8 = 7 then some (.idiv (Reg.ofNum rm), n) else none
    | 0xD3 =>
      if g % 8 = 4 then some (.shl (Reg.ofNum rm), n)
      else if g % 8 = 5 then some (.shr (Reg.ofNum rm), n) else none
    | _ => (Alu.ofOpc o).map fun a => (.alu a (Reg.ofNum rm) (Reg.ofNum g), n)

/-- The forms behind REX.W = 1 with `0F o` (ModRM at 3). -/
def decW0F (l : List B) (o r x b : Nat) : Option (Ins × Nat) :=
  match opd l 3 r x b with
  | some (.mem g m, n) => if o = 0xB6 then some (.ldzx (Reg.ofNum g) m, n) else none
  | some (.reg g rm, n) =>
    if o = 0xB6 then some (.zx8 (Reg.ofNum g) (Reg.ofNum rm), n)
    else if o = 0xAF then some (.imul (Reg.ofNum g) (Reg.ofNum rm), n) else none
  | none => none

/-- An instruction that starts with a REX prefix. -/
def decRex (l : List B) : Option (Ins × Nat) :=
  let b0 := bt l 0
  let w := b0 / 8 % 2
  let r := b0 / 4 % 2
  let x := b0 / 2 % 2
  let b := b0 % 2
  let o := bt l 1
  if w = 1 then
    if o = 0x99 then some (.cqo, 2)
    else if o = 0x0F then decW0F l (bt l 2) r x b
    else decW l o r x b
  else if o = 0xFF then
    match opd l 2 r x b with
    | some (.mem g m, n) => if g % 8 = 4 then some (.jmpm m, n) else none
    | _ => none
  else if o = 0x0F ∧ bt l 2 / 16 = 9 then
    match opd l 3 r x b, Cond.ofCc (bt l 2 % 16) with
    | some (.reg g rm, n), some c => if g % 8 = 0 then some (.set c (Reg.ofNum rm), n) else none
    | _, _ => none
  else none

def decode (l : List B) : Option (Ins × Nat) :=
  let b0 := bt l 0
  if b0 = 0x0F then
    let b1 := bt l 1
    if b1 = 0x05 then some (.syscall, 2)
    else if b1 = 0x0B then some (.ud2, 2)
    else if b1 / 16 = 8 then (Cond.ofCc (b1 % 16)).map fun c => (.jcc c (imm32 l 2), 6)
    else none
  else if b0 = 0xE9 then some (.jmp (imm32 l 1), 5)
  else if b0 = 0xF0 then
    -- lock cmpxchg [m], r64 : F0 REX.W 0F B1 ModRM SIB disp32
    let t := l.drop 1
    let c := bt t 0
    if c / 16 = 4 ∧ c / 8 % 2 = 1 ∧ bt t 1 = 0x0F ∧ bt t 2 = 0xB1 then
      match opd t 3 (c / 4 % 2) (c / 2 % 2) (c % 2) with
      | some (.mem g m, n) => some (.cmpxchg m (Reg.ofNum g), n + 1)
      | _ => none
    else none
  else if b0 / 16 = 4 then decRex l
  else none

end Runner.X86
