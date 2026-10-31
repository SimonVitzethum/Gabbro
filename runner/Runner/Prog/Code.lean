import Runner.Prog.Asm

/-! # The runner: loader, dispatch, the 27 handlers (`PLAN-SELF-HOSTING.md` §2.1.5)

Registers while the IR runs: `r12` = the IR `pc`, `r13` = the IR `fp`, `r14` = the dispatch table. Nothing else
lives across instructions, and the runner never uses the stack.

* **Dispatch** (at the end of every handler, threaded): `movzx rax, byte [r12]; jmp [r14 + rax·8]`. The table has
  256 entries; opcodes without a handler go to `ud2`, so every byte has a defined successor.
* **Loader:** `open(argv[1])`, `lseek(fd, 0, SEEK_END)` for the length, `mmap` of the file at `IMG` (private,
  read-write, `MAP_FIXED_NOREPLACE`), then `fp` := the first word of the image, `pc` := `IMG + 16`. Any failure:
  `ud2`.
* Each handler reads its operand fields and slots in the order of the IR semantics (`Runner/IR/Step.lean`) and
  writes last.
* **Threads:** `spawn` calls `clone` with fixed flags (`Runner/Basis/Res.lean`) and no new stack: the runner never
  touches its stack, and no signal handler is installed. The child returns from `syscall` with `rax = 0` and every
  other register of the parent; it takes `pc` and `fp` from `rbx` and `rbp`. A thread ends with `exit`, the
  process with `exit_group`, both through `sys`. -/

namespace Runner.Prog
open Runner.X86

def BASE : Nat := 0x400000
/-- The file offset of the code (after the ELF header and two program headers). -/
def CODE : Nat := 0x100
def IMG : Nat := 0x10000000

def mb (b : Reg) (d : BitVec 32 := 0) : Addr := { base := b, disp := d }
def ms (b i : Reg) (d : BitVec 32 := 0) : Addr := { base := b, idx := some i, sc := 3, disp := d }

/-- `r := sx(field k)` of the instruction at `pc`. -/
def fld (r : Reg) (k : Nat) : Ins := .ldsx r (mb .r12 (BitVec.ofNat 32 (4 * k)))
/-- `r := slot[i]`. -/
def sld (r i : Reg) : Ins := .ld r (ms .r13 i)
/-- `slot[i] := r`. -/
def sst (i r : Reg) : Ins := .st (ms .r13 i) r

def dispatch : List Ins := [.ldzx .rax (mb .r12), .jmpm (ms .r14 .rax)]
def nextI : List Ins := .alui .add .r12 16 :: dispatch

def lenOf (is : List Ins) : Nat := (is.map fun i => (enc i).length).sum

/-- `rax := op(slot f2, slot f3)` then `slot f1 := rax`. -/
def binH (body : List Ins) : List Ins :=
  [fld .rax 2, sld .rax .rax, fld .rdx 3, sld .rdx .rdx] ++ body ++ [fld .rcx 1, sst .rcx .rax] ++ nextI

def divH (res : Reg) : List Ins :=
  [fld .rax 2, sld .rax .rax, fld .rsi 3, sld .rsi .rsi, .cqo, .idiv .rsi, fld .rcx 1, sst .rcx res] ++ nextI

def shiftH (sh : Ins) : List Ins :=
  [fld .rax 2, sld .rax .rax, fld .rcx 3, sld .rcx .rcx, sh, fld .rdx 1, sst .rdx .rax] ++ nextI

/-- `brz`: the taken branch, which the `jnz` skips. -/
def brzTaken : List Ins := [fld .rax 2, .alu .add .r12 .rax] ++ dispatch

/-- `spawn`: the parent's path after `clone`, which the child's `jz` skips. -/
def spawnParent : List Ins := [fld .rcx 1, sst .rcx .rax] ++ nextI

/-- The code of each opcode; position independent (the jumps inside, `brz`'s `jnz` and `spawn`'s `jz`, are
    relative). Opcodes without a handler run `ud2`. -/
def handler : Nat → List Ins
  | 1 => [fld .rax 2, fld .rcx 1, sst .rcx .rax] ++ nextI
  | 2 => [fld .rax 2, sld .rax .rax, fld .rcx 1, sst .rcx .rax] ++ nextI
  | 3 => binH [.alu .add .rax .rdx]
  | 4 => binH [.alu .sub .rax .rdx]
  | 5 => binH [.imul .rax .rdx]
  | 6 => divH .rax
  | 7 => divH .rdx
  | 8 => binH [.alu .and .rax .rdx]
  | 9 => binH [.alu .or .rax .rdx]
  | 10 => binH [.alu .xor .rax .rdx]
  | 11 => shiftH (.shl .rax)
  | 12 => shiftH (.shr .rax)
  | 13 => binH [.alu .cmp .rax .rdx, .set .l .rax, .zx8 .rax .rax]
  | 14 => binH [.alu .cmp .rax .rdx, .set .z .rax, .zx8 .rax .rax]
  | 15 => [fld .rax 2, sld .rax .rax, .ld .rax (mb .rax), fld .rcx 1, sst .rcx .rax] ++ nextI
  | 16 => [fld .rax 1, sld .rax .rax, fld .rdx 2, sld .rdx .rdx, .st (mb .rax) .rdx] ++ nextI
  | 17 => [fld .rax 2, .lea .rax (ms .r13 .rax), fld .rcx 1, sst .rcx .rax] ++ nextI
  | 18 => [fld .rax 1, .alu .add .r12 .rax] ++ dispatch
  | 19 => [fld .rax 1, sld .rax .rax, .alu .test .rax .rax, .jcc .nz (BitVec.ofNat 32 (lenOf brzTaken))] ++
           brzTaken ++ nextI
  | 20 => [fld .rax 1, sld .rax .rax, fld .rdx 2, .lea .rdx (ms .r13 .rdx), .lea .rcx (mb .r12 16),
           .st (mb .rdx) .rcx, .st (mb .rdx 8) .r13, .mov .r13 .rdx, .mov .r12 .rax] ++ dispatch
  | 21 => [.ld .rax (mb .r13), .ld .r13 (mb .r13 8), .mov .r12 .rax] ++ dispatch
  | 22 => [fld .rax 2, .ld .rdx (ms .r13 .rax), fld .rcx 3, .ld .rax (ms .r13 .rcx),
           .ld .rsi (ms .r13 .rcx 8), .cmpxchg (mb .rdx) .rsi, fld .rcx 1, sst .rcx .rax] ++ nextI
  | 23 => [fld .rbx 1, .lea .rbx (ms .r13 .rbx), fld .rcx 2, .lea .rcx (ms .r13 .rcx),
           .ld .rax (mb .rcx), .ld .rdi (mb .rcx 8), .ld .rsi (mb .rcx 16), .ld .rdx (mb .rcx 24),
           .ld .r10 (mb .rcx 32), .ld .r8 (mb .rcx 40), .ld .r9 (mb .rcx 48), .syscall,
           .st (mb .rbx) .rax] ++ nextI
  | 24 => [fld .rcx 2, .lea .rcx (ms .r13 .rcx), .ld .rbx (mb .rcx), .ld .rbp (mb .rcx 8),
           .movi .rax (BitVec.ofNat 32 NR_CLONE), .movi .rdi (BitVec.ofNat 32 CLONE_FLAGS), .movi .rsi 0,
           .movi .rdx 0, .movi .r10 0, .movi .r8 0, .movi .r9 0, .syscall,
           .alu .test .rax .rax, .jcc .z (BitVec.ofNat 32 (lenOf spawnParent))] ++ spawnParent ++
           [.mov .r12 .rbx, .mov .r13 .rbp] ++ dispatch
  | 27 => binH [.alu .cmp .rax .rdx, .set .b .rax, .zx8 .rax .rax]
  | 25 => [fld .rax 2, sld .rax .rax, fld .rsi 3, sld .rsi .rsi,
           .movi .rdx 0, .udiv .rsi, fld .rcx 1, sst .rcx .rax] ++ nextI
  | 26 => [fld .rax 2, sld .rax .rax, fld .rsi 3, sld .rsi .rsi,
           .movi .rdx 0, .udiv .rsi, fld .rcx 1, sst .rcx .rdx] ++ nextI
  | _ => [.ud2]

/-- Label numbers: 0 the loader, `k` the handler of opcode `k`, 100 `ud2`, 101 the table. -/
def LOADER : Nat := 0
def BAD : Nat := 100
def TABLE : Nat := 101

/-! The loader, in five blocks; a failure jumps to its own `ud2` at the end (relative jumps only). Its one
    absolute operand, the table's address `tb`, is filled in after the layout is known. -/

/-- `rdi := argv[1]`; `open(rdi, O_RDONLY, 0)`; test. -/
def ld1 : List Ins := [.ld .rdi (mb .rsp 16), .movi .rax 2, .movi .rsi 0, .movi .rdx 0, .syscall, .alu .test .rax .rax]
/-- keep the fd in `rbx`; `lseek(fd, 0, SEEK_END)`; test. -/
def ld2 : List Ins :=
  [.mov .rbx .rax, .mov .rdi .rbx, .movi .rsi 0, .movi .rdx 2, .movi .rax 8, .syscall, .alu .test .rax .rax]
/-- `mmap(IMG, len, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_FIXED_NOREPLACE, fd, 0)`; compare with `IMG`. -/
def ld4 : List Ins :=
  [.mov .rsi .rax, .movi .rdi (BitVec.ofNat 32 IMG), .movi .rdx 3, .movi .r10 0x100002, .mov .r8 .rbx, .movi .r9 0,
   .movi .rax 9, .syscall, .movi .rcx (BitVec.ofNat 32 IMG), .alu .cmp .rax .rcx]
/-- `r14` := the table, `fp` := the image's first word, `pc` := `IMG + 16`, dispatch. -/
def ld5 (tb : Nat) : List Ins :=
  [.movi .r14 (BitVec.ofNat 32 tb), .ld .r13 (mb .rcx), .lea .r12 (mb .rcx 16)] ++ dispatch

def ldj4 : Ins := .jcc .nz (BitVec.ofNat 32 (lenOf (ld5 0)))
def ldj3 : Ins := .jcc .z (BitVec.ofNat 32 (lenOf (ld4 ++ [ldj4] ++ ld5 0)))
def ldj2 : Ins := .jcc .s (BitVec.ofNat 32 (lenOf ([ldj3] ++ ld4 ++ [ldj4] ++ ld5 0)))
def ldj1 : Ins := .jcc .s (BitVec.ofNat 32 (lenOf (ld2 ++ [ldj2, ldj3] ++ ld4 ++ [ldj4] ++ ld5 0)))

def loaderI (tb : Nat) : List Ins :=
  ld1 ++ [ldj1] ++ ld2 ++ [ldj2, ldj3] ++ ld4 ++ [ldj4] ++ ld5 tb ++ [.ud2]

/-- The program with the table at `tb`; the layout does not depend on `tb`. -/
def itemsWith (tb : Nat) : List Item :=
  [.lab LOADER] ++ (loaderI tb).map .i ++
  ((List.range 27).map (· + 1)).flatMap (fun k => .lab k :: (handler k).map .i) ++
  [.lab BAD, .i .ud2]

def codeLen : Nat := ((itemsWith 0).map Item.len).sum

/-- The table's file offset: after the code, aligned to 8. -/
def tblOff : Nat := (CODE + codeLen + 7) / 8 * 8

def items : List Item := itemsWith (BASE + tblOff)


/-- Label → file offset. -/
def tab : List (Nat × Nat) := (TABLE, tblOff) :: labels (itemsWith 0) CODE

/-- The runner's instructions with their file offsets. -/
def prog : List (Nat × Ins) := place tab BASE items CODE

/-- The table entry of opcode `k`: the address of its handler. -/
def target (k : Nat) : Nat := BASE + find tab (if 1 ≤ k ∧ k ≤ 27 then k else BAD)

end Runner.Prog
