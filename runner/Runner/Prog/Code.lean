import Runner.Prog.Asm

/-! # The runner: loader, dispatch, the 23 handlers (`PLAN-SELF-HOSTING.md` §2.1.5)

Registers while the IR runs: `r12` = the IR `pc`, `r13` = the IR `fp`, `r14` = the dispatch table. Nothing else
lives across instructions, and the runner never uses the stack.

* **Dispatch** (at the end of every handler, threaded): `movzx rax, byte [r12]; jmp [r14 + rax·8]`. The table has
  256 entries; opcodes without a handler go to `ud2`, so every byte has a defined successor.
* **Loader:** `open(argv[1])`, `lseek(fd, 0, SEEK_END)` for the length, `mmap` of the file at `IMG` (private,
  read-write, `MAP_FIXED_NOREPLACE`), then `fp` := the first word of the image, `pc` := `IMG + 16`. Any failure:
  `ud2`.
* Each handler reads its operand fields and slots in the order of the IR semantics (`Runner/IR/Step.lean`) and
  writes last. -/

namespace Runner.Prog
open Runner.X86

def BASE : Nat := 0x400000
/-- The file offset of the code (after the ELF header and two program headers). -/
def CODE : Nat := 0x100
def IMG : Nat := 0x10000000

def mb (b : Reg) (d : BitVec 32 := 0) : Addr := { base := b, disp := d }
def ms (b i : Reg) (d : BitVec 32 := 0) : Addr := { base := b, idx := some i, sc := 3, disp := d }

/-- `r := sx(field k)` of the instruction at `pc`. -/
def fld (r : Reg) (k : Nat) : Item := .i (.ldsx r (mb .r12 (BitVec.ofNat 32 (4 * k))))
/-- `r := slot[i]`. -/
def sld (r i : Reg) : Item := .i (.ld r (ms .r13 i))
/-- `slot[i] := r`. -/
def sst (i r : Reg) : Item := .i (.st (ms .r13 i) r)

def dispatch : List Item := [.i (.ldzx .rax (mb .r12)), .i (.jmpm (ms .r14 .rax))]
def nextI : List Item := .i (.alui .add .r12 16) :: dispatch

/-- `rax := op(slot f2, slot f3)` then `slot f1 := rax`. -/
def binH (body : List Item) : List Item :=
  [fld .rax 2, sld .rax .rax, fld .rdx 3, sld .rdx .rdx] ++ body ++ [fld .rcx 1, sst .rcx .rax] ++ nextI

def divH (res : Reg) : List Item :=
  [fld .rax 2, sld .rax .rax, fld .rsi 3, sld .rsi .rsi, .i .cqo, .i (.idiv .rsi), fld .rcx 1, sst .rcx res] ++ nextI

def shiftH (sh : Ins) : List Item :=
  [fld .rax 2, sld .rax .rax, fld .rcx 3, sld .rcx .rcx, .i sh, fld .rdx 1, sst .rdx .rax] ++ nextI

/-- The handler of each opcode 1..23. -/
def handler : Nat → List Item
  | 1 => [fld .rax 2, fld .rcx 1, sst .rcx .rax] ++ nextI
  | 2 => [fld .rax 2, sld .rax .rax, fld .rcx 1, sst .rcx .rax] ++ nextI
  | 3 => binH [.i (.alu .add .rax .rdx)]
  | 4 => binH [.i (.alu .sub .rax .rdx)]
  | 5 => binH [.i (.imul .rax .rdx)]
  | 6 => divH .rax
  | 7 => divH .rdx
  | 8 => binH [.i (.alu .and .rax .rdx)]
  | 9 => binH [.i (.alu .or .rax .rdx)]
  | 10 => binH [.i (.alu .xor .rax .rdx)]
  | 11 => shiftH (.shl .rax)
  | 12 => shiftH (.shr .rax)
  | 13 => binH [.i (.alu .cmp .rax .rdx), .i (.set .l .rax), .i (.zx8 .rax .rax)]
  | 14 => binH [.i (.alu .cmp .rax .rdx), .i (.set .z .rax), .i (.zx8 .rax .rax)]
  | 15 => [fld .rax 2, sld .rax .rax, .i (.ld .rax (mb .rax)), fld .rcx 1, sst .rcx .rax] ++ nextI
  | 16 => [fld .rax 1, sld .rax .rax, fld .rdx 2, sld .rdx .rdx, .i (.st (mb .rax) .rdx)] ++ nextI
  | 17 => [fld .rax 2, .i (.lea .rax (ms .r13 .rax)), fld .rcx 1, sst .rcx .rax] ++ nextI
  | 18 => [fld .rax 1, .i (.alu .add .r12 .rax)] ++ dispatch
  | 19 => [fld .rax 1, sld .rax .rax, .i (.alu .test .rax .rax), .jccL .nz 219, fld .rax 2,
           .i (.alu .add .r12 .rax)] ++ dispatch ++ [.lab 219] ++ nextI
  | 20 => [fld .rax 1, sld .rax .rax, fld .rdx 2, .i (.lea .rdx (ms .r13 .rdx)), .i (.lea .rcx (mb .r12 16)),
           .i (.st (mb .rdx) .rcx), .i (.st (mb .rdx 8) .r13), .i (.mov .r13 .rdx), .i (.mov .r12 .rax)] ++ dispatch
  | 21 => [.i (.ld .rax (mb .r13)), .i (.ld .r13 (mb .r13 8)), .i (.mov .r12 .rax)] ++ dispatch
  | 22 => [fld .rax 2, .i (.ld .rdx (ms .r13 .rax)), fld .rcx 3, .i (.ld .rax (ms .r13 .rcx)),
           .i (.ld .rsi (ms .r13 .rcx 8)), .i (.cmpxchg (mb .rdx) .rsi), fld .rcx 1, sst .rcx .rax] ++ nextI
  | 23 => [fld .rbx 1, .i (.lea .rbx (ms .r13 .rbx)), fld .rcx 2, .i (.lea .rcx (ms .r13 .rcx)),
           .i (.ld .rax (mb .rcx)), .i (.ld .rdi (mb .rcx 8)), .i (.ld .rsi (mb .rcx 16)), .i (.ld .rdx (mb .rcx 24)),
           .i (.ld .r10 (mb .rcx 32)), .i (.ld .r8 (mb .rcx 40)), .i (.ld .r9 (mb .rcx 48)), .i .syscall,
           .i (.st (mb .rbx) .rax)] ++ nextI
  | _ => []

/-- Label numbers: 0 the loader, `k` the handler of opcode `k`, 100 `ud2`, 101 the table. -/
def LOADER : Nat := 0
def BAD : Nat := 100
def TABLE : Nat := 101

def loader : List Item :=
  [ .i (.ld .rdi (mb .rsp 16)), .i (.movi .rax 2), .i (.movi .rsi 0), .i (.movi .rdx 0), .i .syscall,
    .i (.alu .test .rax .rax), .jccL .s BAD, .i (.mov .rbx .rax),
    .i (.mov .rdi .rbx), .i (.movi .rsi 0), .i (.movi .rdx 2), .i (.movi .rax 8), .i .syscall,
    .i (.alu .test .rax .rax), .jccL .s BAD, .jccL .z BAD, .i (.mov .rsi .rax),
    .i (.movi .rdi (BitVec.ofNat 32 IMG)), .i (.movi .rdx 3), .i (.movi .r10 0x100002), .i (.mov .r8 .rbx),
    .i (.movi .r9 0), .i (.movi .rax 9), .i .syscall,
    .i (.movi .rcx (BitVec.ofNat 32 IMG)), .i (.alu .cmp .rax .rcx), .jccL .nz BAD,
    .adr .r14 TABLE, .i (.ld .r13 (mb .rcx)), .i (.lea .r12 (mb .rcx 16)) ] ++ dispatch

def items : List Item :=
  [.lab LOADER] ++ loader ++
  ((List.range 23).map (· + 1)).flatMap (fun k => .lab k :: handler k) ++
  [.lab BAD, .i .ud2]

def codeLen : Nat := (items.map Item.len).sum

/-- The table's file offset: after the code, aligned to 8. -/
def tblOff : Nat := (CODE + codeLen + 7) / 8 * 8

/-- Label → file offset. -/
def tab : List (Nat × Nat) := (TABLE, tblOff) :: labels items CODE

/-- The runner's instructions with their file offsets. -/
def prog : List (Nat × Ins) := place tab BASE items CODE

/-- The table entry of opcode `k`: the address of its handler. -/
def target (k : Nat) : Nat := BASE + find tab (if 1 ≤ k ∧ k ≤ 23 then k else BAD)

end Runner.Prog
