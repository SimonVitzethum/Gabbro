import Runner.X86.Step
import Runner.Prog.Elf

/-! # Differential tests of the x86-64 model on the processor (`PLAN-SELF-HOSTING.md` §2.2, point 2)

Each case is one instruction of the subset on a random register file, random flags and a random 256-byte data
area. The test program `xtest` loads the case (flags through `popfq`), executes the instruction, stores every
register, the flags (`pushfq`) and leaves the data area in place; at the end it writes all case blocks to stdout.
The expected bytes are the model's `exec` on the same state. Flags the model leaves `none` are masked; every
other bit must agree. Cases the model faults on are not generated here (the processor would end the program);
`faults` are separate programs, each expected to die by the named signal.

The harness itself (register loads and stores, `pushfq`, `popfq`) is outside the proved code and needs no proof:
a harness error shows as a difference. -/

namespace Runner.Test
open Runner Runner.X86 Runner.Prog

/-! ## Randomness -/

structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let x := g.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, ⟨x⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (x.toNat % n, g)

/-- A word: half the time from the edge cases. -/
def Rng.word (g : Rng) : W × Rng :=
  let (c, g) := g.below 2
  let (x, g) := g.next
  if c = 0 then (BitVec.ofNat 64 x.toNat, g)
  else
    let edges : List Nat := [0, 1, 2, 7, 8, 63, 64, 255, 256, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32,
      2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1, 2 ^ 64 - 2, 2 ^ 64 - 255]
    (BitVec.ofNat 64 (edges.getD (x.toNat % edges.length) 0), g)

def regs : List Reg := [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- A register other than `rsp` and the ones in `avoid`. -/
def Rng.reg (g : Rng) (avoid : List Reg := []) : Reg × Rng :=
  let ok := regs.filter fun r => r != .rsp && !avoid.contains r
  let (i, g) := g.below ok.length
  (ok.getD i .rax, g)

/-! ## Cases -/

/-- The data area of a case starts at `dat`; memory operands point into it. -/
structure Case where
  ins : List Ins           -- the instruction (and for jumps the instruction jumped over)
  regs : Reg → W
  flags : Nat              -- input flags: some of CF ZF SF OF
  data : Array B           -- 256 bytes

def DATA : Nat := 0x20000000
def BLOCK : Nat := 1024
def OUT : Nat := 512

def caseBase (i : Nat) : Nat := DATA + i * BLOCK
def caseDat (i : Nat) : Nat := caseBase i + 136

/-- A memory operand into the data area of case `i`: `base` holds `dat + 64`, the index is small. -/
def Rng.addr (g : Rng) (i : Nat) (avoid : List Reg) :
    Addr × List (Reg × W) × Rng :=
  let (b, g) := g.reg avoid
  let (useIdx, g) := g.below 2
  let (x, g) := g.reg (b :: .r12 :: avoid)
  let (iv, g) := g.below 16
  let (sc, g) := g.below 4
  let (d, g) := g.below 121
  let disp := BitVec.ofInt 32 ((d : Int) - 64)
  let bv := BitVec.ofNat 64 (caseDat i + 64)
  if useIdx = 0 then ({ base := b, disp := disp }, [(b, bv)], g)
  else
    -- keep the address inside the area: 64 + 15·8 + 56 + 8 ≤ 256
    ({ base := b, idx := some x, sc := sc, disp := disp }, [(b, bv), (x, BitVec.ofNat 64 iv)], g)

def aluAll : List Alu := [.add, .or, .and, .sub, .xor, .cmp, .test]
def aluImm : List Alu := [.add, .or, .and, .sub, .xor, .cmp]
def conds : List Cond := [.z, .nz, .s, .l]

/-- The instruction of a case of kind `k`, with the registers its memory operand fixes. `base` is excluded. -/
def Rng.ins (g : Rng) (k : Nat) (i : Nat) (base : Reg) : List Ins × List (Reg × W) × Rng :=
  let av := [base]
  let (d, g) := g.reg av
  let (s, g) := g.reg av
  let (w, g) := g.word
  let imm := w.setWidth 32
  match k with
  | 0 => let (m, fix, g) := g.addr i (d :: av); ([.ld d m], fix, g)
  | 1 => let (m, fix, g) := g.addr i (s :: av); ([.st m s], fix, g)
  | 2 => ([.mov d s], [], g)
  | 3 => ([.movi d imm], [], g)
  | 4 => let (m, fix, g) := g.addr i (d :: av); ([.ldsx d m], fix, g)
  | 5 => let (m, fix, g) := g.addr i (d :: av); ([.ldzx d m], fix, g)
  | 6 => ([.zx8 d s], [], g)
  | 7 => let (m, _, g) := g.addr i av; ([.lea d m], [], g)
  | 8 => let (o, g) := g.below aluAll.length; ([.alu (aluAll.getD o .add) d s], [], g)
  | 9 => let (o, g) := g.below aluImm.length; ([.alui (aluImm.getD o .add) d imm], [], g)
  | 10 => ([.imul d s], [], g)
  | 11 => ([.cqo], [], g)
  | 12 => ([.idiv s], [], g)
  | 13 => ([.shl d], [], g)
  | 14 => ([.shr d], [], g)
  | 15 => let (c, g) := g.below 4; ([.set (conds.getD c .z) d], [], g)
  | 16 => let (c, g) := g.below 4; ([.jcc (conds.getD c .z) 7, .movi .rcx 0x1234], [], g)
  | 17 => ([.jmp 7, .movi .rcx 0x1234], [], g)
  | _ => let (m, fix, g) := g.addr i (s :: .rax :: av); ([.cmpxchg m s], fix, g)

def KINDS : Nat := 19

/-! ## The model's answer -/

def flagBits : List Nat := [0, 6, 7, 11]

def bitOf (n b : Nat) : Bool := n / 2 ^ b % 2 = 1

def dataMem (i : Nat) (data : Array B) : Mem where
  b a := if caseDat i ≤ a.toNat ∧ a.toNat < caseDat i + 256 then data.getD (a.toNat - caseDat i) 0 else 0
  rd a := caseDat i ≤ a.toNat ∧ a.toNat < caseDat i + 256
  wr a := caseDat i ≤ a.toNat ∧ a.toNat < caseDat i + 256

def initX (i : Nat) (c : Case) : X :=
  { rax := c.regs .rax, rcx := c.regs .rcx, rdx := c.regs .rdx, rbx := c.regs .rbx, rsp := 0,
    rbp := c.regs .rbp, rsi := c.regs .rsi, rdi := c.regs .rdi, r8 := c.regs .r8, r9 := c.regs .r9,
    r10 := c.regs .r10, r11 := c.regs .r11, r12 := c.regs .r12, r13 := c.regs .r13, r14 := c.regs .r14,
    r15 := c.regs .r15, rip := 0x1000,
    cf := some (bitOf c.flags 0), zf := some (bitOf c.flags 6), sf := some (bitOf c.flags 7),
    of := some (bitOf c.flags 11) }

/-- The answer of the one memory `m` to a data request. -/
def memAns (m : Mem) : Op → Option (Ans × Mem)
  | .rd 1 a => some ((m.rd8 a).map (fun v => (v.setWidth 64, 0)), m)
  | .rd 4 a => some ((m.rd32 a).map (fun v => (v.setWidth 64, 0)), m)
  | .rd _ a => some ((m.rd64 a).map (fun v => (v, 0)), m)
  | .wr a v => some (match m.wr64 a v with | some m' => (some (0, 0), m') | none => (none, m))
  | .cas a e n => some (match m.cas a e n with | some (o, m') => (some (o, 0), m') | none => (none, m))
  | .sys _ => none

/-- One instruction against the memory `m`: the new state and memory, or `none` for a fault or `unk`. -/
def execM (i : Ins) (x : X) (m : Mem) : Option (X × Mem) :=
  match exec i (enc i).length x with
  | .next y => some (y, m)
  | .ask o k =>
    match memAns m o with
    | some (a, m') => match k a with
      | .next y => some (y, m')
      | _ => none
    | none => none
  | _ => none

/-- Runs the case's instructions in order; a jump that skips the next instruction skips it. -/
def runCase : List Ins → X → Mem → Option (X × Mem)
  | [], x, m => some (x, m)
  | i :: is, x, m =>
    let n := (enc i).length
    match execM i x m with
    | some (y, m') =>
      if y.rip = x.rip + BitVec.ofNat 64 n then runCase is y m'
      else
        let skipped := (is.map fun j => (enc j).length).sum
        if y.rip = x.rip + BitVec.ofNat 64 (n + skipped) then some ({ y with rip := x.rip }, m') else none
    | none => none

def flagsOut (x : X) : Nat × Nat :=
  let fs := [(0, x.cf), (6, x.zf), (7, x.sf), (11, x.of)]
  fs.foldl (fun (v, m) (b, f) => match f with
    | some t => (v + (if t then 2 ^ b else 0), m + 2 ^ b)
    | none => (v, m)) (0, 0)

/-! ## The program -/

def raw (l : List Nat) : List B := l.map byte

def pushRax : List B := raw [0x50]
def popRax : List B := raw [0x58]
def pushfq : List B := raw [0x9C]
def popfq : List B := raw [0x9D]

def caseCode (i : Nat) (base : Reg) (c : Case) : List B :=
  let b := caseBase i
  let ld := fun (r : Reg) => enc (.ld r { base := base, disp := BitVec.ofNat 32 (8 * r.num) })
  let st := fun (r : Reg) => enc (.st { base := base, disp := BitVec.ofNat 32 (OUT + 8 * r.num) } r)
  let live := regs.filter fun r => r != .rsp && r != base
  enc (.movi base (BitVec.ofNat 32 b)) ++ enc (.ld .rax { base := base, disp := 128 }) ++ pushRax ++ popfq ++
  live.flatMap ld ++ c.ins.flatMap enc ++ live.flatMap st ++
  pushfq ++ popRax ++ enc (.st { base := base, disp := BitVec.ofNat 32 (OUT + 128) } .rax)

/-- `write(1, DATA, n·BLOCK)` then `exit_group(0)`. -/
def tail (n : Nat) : List B :=
  enc (.movi .rax 1) ++ enc (.movi .rdi 1) ++ enc (.movi .rsi (BitVec.ofNat 32 DATA)) ++
  enc (.movi .rdx (BitVec.ofNat 32 (n * BLOCK))) ++ enc .syscall ++
  enc (.movi .rax 231) ++ enc (.movi .rdi 0) ++ enc .syscall

def leW (v : W) : List B := leN 8 v.toNat

/-- The ELF: code at `0x400000` (read, execute), data at `DATA` (read, write). -/
def elf2 (code data : List B) : List B :=
  let codeOff := 0x1000
  let dataOff := codeOff + (code.length + 0xFFF) / 0x1000 * 0x1000
  let hdr := [byte 0x7F, byte 0x45, byte 0x4C, byte 0x46, byte 2, byte 1, byte 1, byte 0] ++ leN 8 0 ++
    leN 2 2 ++ leN 2 0x3E ++ leN 4 1 ++ leN 8 (0x400000 + codeOff) ++ leN 8 64 ++ leN 8 0 ++
    leN 4 0 ++ leN 2 64 ++ leN 2 56 ++ leN 2 3 ++ leN 2 64 ++ leN 2 0 ++ leN 2 0
  let ph1 := leN 4 1 ++ leN 4 5 ++ leN 8 codeOff ++ leN 8 (0x400000 + codeOff) ++ leN 8 (0x400000 + codeOff) ++
    leN 8 code.length ++ leN 8 code.length ++ leN 8 0x1000
  let ph2 := leN 4 1 ++ leN 4 6 ++ leN 8 dataOff ++ leN 8 DATA ++ leN 8 DATA ++
    leN 8 data.length ++ leN 8 data.length ++ leN 8 0x1000
  let ph3 := leN 4 0x6474E551 ++ leN 4 6 ++ leN 8 0 ++ leN 8 0 ++ leN 8 0 ++ leN 8 0 ++ leN 8 0 ++ leN 8 16
  pad (pad (hdr ++ ph1 ++ ph2 ++ ph3) codeOff ++ code) dataOff ++ data

/-- Generates `n` cases: the program, the expected blocks, and per case the flag mask and the kind. -/
partial def gen (n : Nat) : List B × List B × List (Nat × Nat) := Id.run do
  let mut g : Rng := ⟨0x9E3779B97F4A7C15⟩
  let mut code : List (List B) := []
  let mut input : List (List B) := []
  let mut expect : List (List B) := []
  let mut masks : List (Nat × Nat) := []
  let mut i := 0
  while i < n do
    let (k, g1) := g.below KINDS
    let (bsel, g2) := g1.below 2
    let base := if bsel = 0 then Reg.r15 else Reg.rbx
    let (ins, fix, g3) := g2.ins k i base
    -- registers: random, then the fixed ones; cmpxchg sometimes expects the memory word
    let mut gg := g3
    let mut rv : Array W := #[]
    for _ in [0:16] do
      let (w, g') := gg.word
      rv := rv.push w
      gg := g'
    let (fl, g4) := gg.below 16
    let flags := 2 + (if bitOf fl 0 then 1 else 0) + (if bitOf fl 1 then 64 else 0) +
      (if bitOf fl 2 then 128 else 0) + (if bitOf fl 3 then 2048 else 0)
    let mut g5 := g4
    let mut data : Array B := #[]
    for _ in [0:256] do
      let (v, g') := g5.below 256
      data := data.push (byte v)
      g5 := g'
    -- idiv: half the cases with rdx the sign of rax (as after cqo), else nearly every quotient overflows
    let (sgn, g4) := g4.below 2
    if k = 12 ∧ sgn = 0 then
      rv := rv.set! Reg.rdx.num (if rv[Reg.rax.num]!.msb then BitVec.allOnes 64 else 0)
    let regsF : Reg → W := fun r =>
      match fix.find? (·.1 == r) with
      | some (_, v) => v
      | none => if r == base then BitVec.ofNat 64 (caseBase i) else rv[r.num]!
    let c0 : Case := { ins := ins, regs := regsF, flags := flags, data := data }
    -- half of the cmpxchg cases expect the word in memory
    let (eqc, g6) := g5.below 2
    let c : Case := match ins with
      | [.cmpxchg m _] =>
        if eqc = 0 then
          let x := initX i c0
          match (dataMem i c0.data).rd64 (ea x m) with
          | some v => { c0 with regs := fun r => if r == .rax then v else regsF r }
          | none => c0
        else c0
      | _ => c0
    g := g6
    match runCase c.ins (initX i c) (dataMem i c.data) with
    | none => pure ()   -- the model faults (idiv): no case
    | some (y, ym) =>
      let blockIn : List B := (regs.map fun r => if r == .rsp then 0 else c.regs r).flatMap leW ++
        leN 8 c.flags ++ c.data.toList
      let live := regs.filter fun r => r != .rsp && r != base
      let (fv, fm) := flagsOut y
      let dataOut := (List.range 256).map fun j => ym.b (BitVec.ofNat 64 (caseDat i + j))
      let outRegs := regs.flatMap fun r => if live.contains r then leW (y.get r) else leN 8 0
      let blk := pad (blockIn.take 136 ++ dataOut) OUT ++ outRegs ++ leN 8 fv
      code := caseCode i base c :: code
      input := pad blockIn BLOCK :: input
      expect := pad blk BLOCK :: expect
      masks := (fm, k) :: masks
      i := i + 1
  let prog := elf2 (code.reverse.flatten ++ tail n) input.reverse.flatten
  return (prog, expect.reverse.flatten, masks.reverse)

end Runner.Test

namespace Runner.Test
open Runner Runner.X86 Runner.Prog

/-- A one-instruction program whose instruction the model says faults: the name, the program, the signal the
    processor must end it with, and whether the model really answers `fault` for the state the program sets up. -/
structure FaultCase where
  name : String
  prog : List B
  signal : Nat
  model : Bool

/-- `setup` then the instruction; the code page is read-only, `DATA` is one writable page. -/
def faultProg (setup : List Ins) (i : Ins) : List B :=
  elf2 (setup.flatMap enc ++ enc i ++ tail 0) (List.replicate 4096 (byte 0))

/-- The step faults against the memory `m`. -/
def faults1 (r : Res X) (m : Mem) : Bool :=
  match r with
  | .fault => true
  | .ask o k => match memAns m o with
    | some (a, _) => match k a with | .fault => true | _ => false
    | none => false
  | _ => false

def faultModel (regs : List (Reg × W)) (i : Ins) : Bool :=
  let m : Mem :=
    { b := fun _ => 0
      rd := fun a => DATA ≤ a.toNat ∧ a.toNat < DATA + 4096 ∨ 0x401000 ≤ a.toNat ∧ a.toNat < 0x402000
      wr := fun a => DATA ≤ a.toNat ∧ a.toNat < DATA + 4096 }
  let x : X :=
    { rax := 0, rcx := 0, rdx := 0, rbx := 0, rsp := 0, rbp := 0, rsi := 0, rdi := 0, r8 := 0,
      r9 := 0, r10 := 0, r11 := 0, r12 := 0, r13 := 0, r14 := 0, r15 := 0, rip := 0x401000,
      cf := none, zf := none, sf := none, of := none }
  let x := regs.foldl (fun x (r, v) => x.set r v) x
  faults1 (exec i (enc i).length x) m

def idivOverflowModel : Bool :=
  let m : Mem := { b := fun _ => 0, rd := fun _ => false, wr := fun _ => false }
  let x : X :=
    { rax := BitVec.ofNat 64 (2 ^ 63), rcx := 63, rdx := BitVec.allOnes 64, rbx := 0, rsp := 0, rbp := 0,
      rsi := BitVec.allOnes 64, rdi := 0, r8 := 0, r9 := 0, r10 := 0, r11 := 0, r12 := 0, r13 := 0,
      r14 := 0, r15 := 0, rip := 0, cf := none, zf := none, sf := none, of := none }
  match exec (.idiv .rsi) 3 x with
  | .fault => true
  | _ => false

def faults : List FaultCase :=
  let mk (name : String) (regs : List (Reg × W)) (i : Ins) (sig : Nat) : FaultCase :=
    { name := name, prog := faultProg (regs.map fun (r, v) => Ins.movi r (v.setWidth 32)) i, signal := sig,
      model := faultModel (regs.map fun (r, v) => (r, (v.setWidth 32).signExtend 64)) i }
  [ mk "idiv-zero" [(.rax, 7), (.rdx, 0), (.rsi, 0)] (.idiv .rsi) 8,
    -- rdx:rax = -2^63 as a 128-bit value: rax = 2^63 is not a 32-bit immediate, so shift it there
    { name := "idiv-overflow",
      prog := faultProg [.movi .rax 1, .movi .rcx 63, .shl .rax, .cqo, .movi .rsi (BitVec.ofInt 32 (-1))] (.idiv .rsi),
      signal := 8,
      model := idivOverflowModel },
    mk "ld-unmapped" [(.rbx, 0x10)] (.ld .rax { base := .rbx }) 11,
    mk "st-readonly" [(.rbx, 0x401000)] (.st { base := .rbx } .rax) 11,
    mk "ldsx-unmapped" [(.rbx, 0x10)] (.ldsx .rax { base := .rbx }) 11,
    mk "ldzx-unmapped" [(.rbx, 0x10)] (.ldzx .rax { base := .rbx }) 11,
    mk "jmpm-unmapped" [(.rbx, 0x10)] (.jmpm { base := .rbx }) 11,
    -- the comparison fails (rax = 1, memory 0) and the locked write still needs the permission
    mk "cmpxchg-readonly-fail" [(.rbx, 0x401000), (.rax, 1)] (.cmpxchg { base := .rbx } .rcx) 11,
    mk "st-crossing" [(.rbx, DATA + 4092)] (.st { base := .rbx } .rax) 11,
    mk "ud2" [] .ud2 4 ]

end Runner.Test
