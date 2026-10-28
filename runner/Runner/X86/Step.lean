import Runner.X86.Dec

/-! # The x86-64 machine for the subset: state and one step

Written after the Intel SDM (vol. 2) and checked against the processor by `Runner/Test/`. One user-mode thread:
sixteen registers, `rip` and the four status flags the runner reads. Every data access is a request to the memory
(`Runner/Basis/Res.lean`), answered by the machine (`Runner/Mach/`); instructions are fetched from the runner's
code `C`, which never changes while it runs (its pages are not writable and the kernel keeps them: the named
assumption of the machine).
A flag is `none` where the manual leaves it undefined or where the model does not track it; a condition that reads
`none` is `unk` (the model says nothing), so whatever the model does describe holds on every processor.

* A memory access the memory refuses is a page fault: `fault` (the process dies, it has no handler).
* `idiv` with a zero divisor or a quotient outside 64 bits is `#DE`: `fault`. `ud2` is `#UD`: `fault`.
* `syscall` hands the request to the kernel; after the answer `rax` holds the result, `rcx` the return address,
  `r11` what the kernel left there, and every other register is kept (the Linux system-call convention, a named
  assumption). The flags are not tracked across the call. -/

namespace Runner.X86

structure X where
  rax : W
  rcx : W
  rdx : W
  rbx : W
  rsp : W
  rbp : W
  rsi : W
  rdi : W
  r8 : W
  r9 : W
  r10 : W
  r11 : W
  r12 : W
  r13 : W
  r14 : W
  r15 : W
  rip : W
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool

namespace X

def get (x : X) : Reg → W
  | .rax => x.rax | .rcx => x.rcx | .rdx => x.rdx | .rbx => x.rbx
  | .rsp => x.rsp | .rbp => x.rbp | .rsi => x.rsi | .rdi => x.rdi
  | .r8 => x.r8 | .r9 => x.r9 | .r10 => x.r10 | .r11 => x.r11
  | .r12 => x.r12 | .r13 => x.r13 | .r14 => x.r14 | .r15 => x.r15

def set (x : X) : Reg → W → X
  | .rax, v => { x with rax := v } | .rcx, v => { x with rcx := v }
  | .rdx, v => { x with rdx := v } | .rbx, v => { x with rbx := v }
  | .rsp, v => { x with rsp := v } | .rbp, v => { x with rbp := v }
  | .rsi, v => { x with rsi := v } | .rdi, v => { x with rdi := v }
  | .r8, v => { x with r8 := v } | .r9, v => { x with r9 := v }
  | .r10, v => { x with r10 := v } | .r11, v => { x with r11 := v }
  | .r12, v => { x with r12 := v } | .r13, v => { x with r13 := v }
  | .r14, v => { x with r14 := v } | .r15, v => { x with r15 := v }

/-- All four flags unknown. -/
def nof (x : X) : X := { x with cf := none, zf := none, sf := none, of := none }

/-- The flags of `cmp a, b` (`a - b`). -/
def cmpf (x : X) (a b : W) : X :=
  { x with cf := some (a.ult b), zf := some (a - b == 0), sf := some (a - b).msb,
           of := some ((a.msb != b.msb) && ((a - b).msb != a.msb)) }

end X

def sx32 (v : BitVec 32) : W := v.signExtend 64

/-- The effective address of a memory operand. -/
def ea (x : X) (m : Addr) : W :=
  match m.idx with
  | none => x.get m.base + sx32 m.disp
  | some i => x.get m.base + x.get i * BitVec.ofNat 64 (2 ^ m.sc) + sx32 m.disp

def Cond.eval (x : X) : Cond → Option Bool
  | .z => x.zf
  | .nz => x.zf.map (!·)
  | .s => x.sf
  | .l => match x.sf, x.of with
    | some sg, some ov => some (sg != ov)
    | _, _ => none

def aluOp : Alu → W → W → W
  | .add, a, b => a + b | .or, a, b => a ||| b | .and, a, b => a &&& b | .sub, a, b => a - b
  | .xor, a, b => a ^^^ b | .cmp, a, _ => a | .test, a, _ => a

/-- `op d, b`: `cmp` and `test` only set flags, the others write `d` and leave the flags unknown. -/
def aluStep (x : X) (o : Alu) (d : Reg) (b : W) : X :=
  let a := x.get d
  match o with
  | .cmp => x.cmpf a b
  | .test => { x with cf := some false, of := some false, zf := some (a &&& b == 0), sf := some (a &&& b).msb }
  | o => (x.set d (aluOp o a b)).nof

/-- One instruction of length `n` at `x.rip`. -/
def exec (i : Ins) (n : Nat) (x : X) : Res X :=
  let nx := x.rip + BitVec.ofNat 64 n
  let y := { x with rip := nx }
  match i with
  | .ld d m => rd64 (ea x m) fun v => .next (y.set d v)
  | .st m s => wr64 (ea x m) (x.get s) y
  | .mov d s => .next (y.set d (x.get s))
  | .movi d v => .next (y.set d (sx32 v))
  | .ldsx d m => rd32 (ea x m) fun v => .next (y.set d (sx32 v))
  | .ldzx d m => rd8 (ea x m) fun v => .next (y.set d v)
  | .zx8 d s => .next (y.set d (((x.get s).setWidth 8).setWidth 64))
  | .lea d m => .next (y.set d (ea x m))
  | .alu o d s => .next (aluStep y o d (x.get s))
  | .alui o d v => .next (aluStep y o d (sx32 v))
  | .imul d s => .next (y.set d (x.get d * x.get s)).nof
  | .cqo => .next (y.set .rdx (if x.rax.msb then BitVec.allOnes 64 else 0))
  | .idiv s =>
    let dd : Int := x.rdx.toInt * 2 ^ 64 + x.rax.toNat
    let dv := (x.get s).toInt
    if dv = 0 then .fault else
    let q := dd.tdiv dv
    if q < -2 ^ 63 ∨ 2 ^ 63 ≤ q then .fault else
    .next ((y.set .rax (BitVec.ofInt 64 q)).set .rdx (BitVec.ofInt 64 (dd.tmod dv))).nof
  | .shl d => .next (y.set d (x.get d <<< (x.rcx.toNat % 64))).nof
  | .shr d => .next (y.set d (x.get d >>> (x.rcx.toNat % 64))).nof
  | .set c d =>
    match Cond.eval x c with
    | none => .unk
    | some t => .next (y.set d ((x.get d &&& ~~~(BitVec.ofNat 64 0xFF)) ||| (if t then 1 else 0)))
  | .jmp rel => .next { x with rip := nx + sx32 rel }
  | .jcc c rel =>
    match Cond.eval x c with
    | none => .unk
    | some t => .next { x with rip := if t then nx + sx32 rel else nx }
  | .jmpm m => rd64 (ea x m) fun t => .next { x with rip := t }
  | .cmpxchg m s => cas (ea x m) x.rax (x.get s) fun old => .next ((y.cmpf x.rax old).set .rax old)
  | .syscall =>
    .ask (.sys ⟨x.rax, x.rdi, x.rsi, x.rdx, x.r10, x.r8, x.r9⟩) fun r => opt r fun p =>
      .next { y.nof with rax := p.1, rcx := nx, r11 := p.2 }
  | .ud2 => .fault

/-- The 15 bytes at `a` of the code `C` (the longest x86 instruction). -/
def fetch (C : W → B) (a : W) : List B :=
  (List.range 15).map fun i => C (a + BitVec.ofNat 64 i)

def step (C : W → B) (x : X) : Res X :=
  match decode (fetch C x.rip) with
  | none => .unk
  | some (i, n) => exec i n x

end Runner.X86
