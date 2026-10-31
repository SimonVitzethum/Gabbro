import Runner.Basis.Res

/-! # The x86-64 instructions the runner uses (`PLAN-SELF-HOSTING.md` §2.2)

Only these forms exist in the model; the decoder (`Dec.lean`) knows exactly their encodings and nothing else.
Every memory operand is `[base + index·2^scale + disp32]` in the one encoding ModRM `mod=10 rm=100` with a SIB byte;
every instruction except `cqo`, `jmp rel32`, `jcc rel32`, `syscall` and `ud2` carries a REX prefix. -/

namespace Runner.X86

inductive Reg
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

def Reg.num : Reg → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3 | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

def Reg.ofNum : Nat → Reg
  | 0 => .rax | 1 => .rcx | 2 => .rdx | 3 => .rbx | 4 => .rsp | 5 => .rbp | 6 => .rsi | 7 => .rdi
  | 8 => .r8 | 9 => .r9 | 10 => .r10 | 11 => .r11 | 12 => .r12 | 13 => .r13 | 14 => .r14 | _ => .r15

/-- A memory operand `[base + idx·2^sc + disp]`; the index is never `rsp` (not encodable). -/
structure Addr where
  base : Reg
  idx : Option Reg := none
  sc : Nat := 0
  disp : BitVec 32 := 0
  deriving DecidableEq, Repr

/-- The two-operand ALU forms `op r/m64, r64` (opcode byte) and `op r/m64, imm32` (`81 /ext`). -/
inductive Alu
  | add | or | and | sub | xor | cmp | test
  deriving DecidableEq, Repr

/-- Conditions: `z`/`nz` read ZF, `s` reads SF, `l` reads SF and OF, `b` reads CF. -/
inductive Cond
  | z | nz | s | l | b
  deriving DecidableEq, Repr

inductive Ins
  | ld (d : Reg) (m : Addr)              -- mov r64, [m]
  | st (m : Addr) (s : Reg)              -- mov [m], r64
  | mov (d s : Reg)                      -- mov r64, r64
  | movi (d : Reg) (i : BitVec 32)       -- mov r64, simm32
  | ldsx (d : Reg) (m : Addr)            -- movsxd r64, dword [m]
  | ldzx (d : Reg) (m : Addr)            -- movzx r64, byte [m]
  | zx8 (d s : Reg)                      -- movzx r64, r8 (the low byte of s)
  | lea (d : Reg) (m : Addr)
  | alu (o : Alu) (d s : Reg)            -- o d, s
  | alui (o : Alu) (d : Reg) (i : BitVec 32)  -- o d, simm32 (not test)
  | imul (d s : Reg)                     -- d := d * s
  | cqo
  | idiv (s : Reg)
  | udiv (s : Reg)                      -- unsigned rdx:rax / s
  | shl (d : Reg)                        -- by cl
  | shr (d : Reg)                        -- by cl
  | set (c : Cond) (d : Reg)             -- setcc on the low byte of d
  | jmp (rel : BitVec 32)
  | jcc (c : Cond) (rel : BitVec 32)
  | jmpm (m : Addr)                      -- jmp qword [m]
  | cmpxchg (m : Addr) (s : Reg)         -- lock cmpxchg [m], r64
  | syscall
  | ud2
  deriving DecidableEq, Repr

end Runner.X86
