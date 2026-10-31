import Runner.Prog.Elf

/-! # The runner as an assembler listing (Intel syntax), for reading

Printed next to the binary by `lake exe runner`. The listing is not an input to anything: the bytes are
`Runner.Prog.image`; the guardian checks that `objdump` decodes those bytes to the same instructions. -/

namespace Runner.Prog
open Runner.X86

def _root_.Runner.X86.Reg.name : Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx" | .rsp => "rsp" | .rbp => "rbp"
  | .rsi => "rsi" | .rdi => "rdi" | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

def _root_.Runner.X86.Reg.low : Reg → String
  | .rax => "al" | .rcx => "cl" | .rdx => "dl" | .rbx => "bl" | .rsp => "spl" | .rbp => "bpl"
  | .rsi => "sil" | .rdi => "dil" | r => r.name ++ "b"

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def simm (v : BitVec 32) : String :=
  let i := v.toInt
  if i < 0 then "-" ++ hex i.natAbs else hex i.toNat

def _root_.Runner.X86.Addr.show (m : Addr) : String :=
  let ix := match m.idx with | none => "" | some i => s!"+{i.name}*{2 ^ m.sc}"
  let d := m.disp.toInt
  let ds := if d = 0 then "" else if d < 0 then "-" ++ hex d.natAbs else "+" ++ hex d.toNat
  s!"[{m.base.name}{ix}{ds}]"

def _root_.Runner.X86.Alu.name : Alu → String
  | .add => "add" | .or => "or" | .and => "and" | .sub => "sub" | .xor => "xor" | .cmp => "cmp" | .test => "test"

def _root_.Runner.X86.Cond.name : Cond → String
  | .z => "e" | .nz => "ne" | .s => "s" | .l => "l" | .b => "b"

/-- One instruction at address `a` (jump targets as absolute addresses). -/
def _root_.Runner.X86.Ins.show (a : Nat) : Ins → String
  | .ld d m => s!"mov {d.name}, qword ptr {m.show}"
  | .st m s => s!"mov qword ptr {m.show}, {s.name}"
  | .mov d s => s!"mov {d.name}, {s.name}"
  | .movi d v => s!"mov {d.name}, {simm v}"
  | .ldsx d m => s!"movsxd {d.name}, dword ptr {m.show}"
  | .ldzx d m => s!"movzx {d.name}, byte ptr {m.show}"
  | .zx8 d s => s!"movzx {d.name}, {s.low}"
  | .lea d m => s!"lea {d.name}, {m.show}"
  | .alu o d s => s!"{o.name} {d.name}, {s.name}"
  | .alui o d v => s!"{o.name} {d.name}, {simm v}"
  | .imul d s => s!"imul {d.name}, {s.name}"
  | .cqo => "cqo"
  | .idiv s => s!"idiv {s.name}"
  | .udiv s => s!"div {s.name}"
  | .shl d => s!"shl {d.name}, cl"
  | .shr d => s!"shr {d.name}, cl"
  | .set c d => s!"set{c.name} {d.low}"
  | .jmp rel => s!"jmp {hex ((a + 5 + rel.toInt).toNat)}"
  | .jcc c rel => s!"j{c.name} {hex ((a + 6 + rel.toInt).toNat)}"
  | .jmpm m => s!"jmp qword ptr {m.show}"
  | .cmpxchg m s => s!"lock cmpxchg qword ptr {m.show}, {s.name}"
  | .syscall => "syscall"
  | .ud2 => "ud2"

def opName : Nat → String
  | 1 => "const d k" | 2 => "mov d a" | 3 => "add d a b" | 4 => "sub d a b" | 5 => "mul d a b"
  | 6 => "sdiv d a b" | 7 => "srem d a b" | 8 => "and d a b" | 9 => "or d a b" | 10 => "xor d a b"
  | 11 => "shl d a b" | 12 => "shr d a b" | 13 => "lt d a b" | 14 => "eq d a b" | 15 => "ld d a (d := M[a])"
  | 16 => "st a b (M[a] := b)" | 17 => "lea d a" | 18 => "jmp L" | 19 => "brz a L" | 20 => "call a k"
  | 21 => "ret" | 22 => "cas d a e" | 23 => "sys d a" | 24 => "spawn d a (clone, a new OS thread)"
  | 25 => "udiv d a b" | 26 => "urem d a b" | 27 => "ult d a b" | _ => ""

/-- The labels of the listing: loader, handlers by opcode, `ud2`, table. -/
def labelName (l : Nat) : Option String :=
  if l = LOADER then some "loader" else if l = BAD then some "bad" else if l = TABLE then some "table"
  else if 1 ≤ l ∧ l ≤ 27 then some s!"op{l}:  ; {opName l}" else none

def listing : String := Id.run do
  let mut s := "; the S0IR runner, x86-64, Intel syntax; written by `lake exe runner` from Runner/Prog/Code.lean\n"
  s := s ++ "; while the IR runs: r12 = IR pc, r13 = IR fp (frame), r14 = dispatch table; slot i = [r13 + 8*i]\n"
  s := s ++ "; an IR instruction is 16 bytes: opcode byte, then three 32-bit fields at pc+4, pc+8, pc+12\n"
  s := s ++ s!"; ELF loaded at {hex BASE}, code from {hex (BASE + CODE)}, dispatch table at {hex (BASE + tblOff)}\n\n"
  for (o, i) in prog do
    for (l, lo) in tab do
      if lo = o then
        if let some n := labelName l then
          s := s ++ (if n.startsWith "op" then s!"\n{n}\n" else s!"\n{n}:\n")
    s := s ++ s!"  {hex (BASE + o)}:  {Ins.show (BASE + o) i}\n"
  s := s ++ s!"\ntable:  ; 256 handler addresses at {hex (BASE + tblOff)}\n"
  for k in List.range 256 do
    s := s ++ s!"  dq {hex (target k)}  ; opcode {k}\n"
  return s

end Runner.Prog
