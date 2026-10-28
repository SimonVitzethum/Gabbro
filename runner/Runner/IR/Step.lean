import Runner.Basis.Res

/-! # `S0IR`: the instructions and their small-step semantics (`PLAN-SELF-HOSTING.md` §2.1.3)

An instruction is 16 bytes at `pc`: the opcode in byte 0 (bytes 1-3 are ignored), then three little-endian 32-bit
operand fields at `pc + 4`, `pc + 8`, `pc + 12`, each sign-extended to 64 bits. An operand names a slot of the
current frame, the word at `fp + 8·i`. The state is `pc`, `fp` and the memory; the IR code itself lies in that
memory and is fetched from it, so every image -- also one that writes over its own code -- has a defined run.
Every access is checked by the shared memory functions (`Runner/Basis/Mem.lean`); a refused access is a fault.

Each instruction reads in a fixed order and writes last; the runner's handler does the same accesses in the same
order, which is what makes the simulation an equality of memories. -/

namespace Runner.IR

structure S where
  pc : W
  fp : W
  mem : Mem

def sx (v : BitVec 32) : W := v.signExtend 64

/-- The address of slot `i` of the frame at `fp`. -/
def slot (fp i : W) : W := fp + i * 8

def f1 (s : S) : Option W := (s.mem.rd32 (s.pc + 4)).map sx
def f2 (s : S) : Option W := (s.mem.rd32 (s.pc + 8)).map sx
def f3 (s : S) : Option W := (s.mem.rd32 (s.pc + 12)).map sx

/-- The value of slot `i`. -/
def ld (s : S) (i : W) : Option W := s.mem.rd64 (slot s.fp i)

def nxt (s : S) (m : Mem) : Res S := .next { s with pc := s.pc + 16, mem := m }

/-- Store `r` into the slot named by field 1, then the next instruction. The field is read from `m`. -/
def ret1 (s : S) (m : Mem) (r : W) : Res S :=
  opt ((m.rd32 (s.pc + 4)).map sx) fun d => opt (m.wr64 (slot s.fp d) r) fun m' => nxt s m'

/-- `d := f a b` with `a`, `b` the slots of fields 2 and 3 and `d` the slot of field 1. -/
def bin (f : W → W → Option W) (s : S) : Res S :=
  opt (f2 s) fun a => opt (ld s a) fun va =>
  opt (f3 s) fun b => opt (ld s b) fun vb =>
  opt (f va vb) fun r => ret1 s s.mem r

/-- Signed division truncating towards zero; no result for a zero divisor or a quotient outside 64 bits. -/
def sdiv (a b : W) : Option W :=
  if b.toInt = 0 then none else
  let q := a.toInt.tdiv b.toInt
  if q < -2 ^ 63 ∨ 2 ^ 63 ≤ q then none else some (BitVec.ofInt 64 q)

/-- The remainder of `sdiv` (sign of the dividend); defined exactly where `sdiv` is. -/
def srem (a b : W) : Option W :=
  if b.toInt = 0 then none else
  let q := a.toInt.tdiv b.toInt
  if q < -2 ^ 63 ∨ 2 ^ 63 ≤ q then none else some (BitVec.ofInt 64 (a.toInt.tmod b.toInt))

def bool (c : Bool) : W := if c then 1 else 0

/-- One instruction, by opcode. Opcode 0, 24 (`spawn`, built with the threads) and 25-255 fault. -/
def op (o : Nat) (s : S) : Res S :=
  match o with
  | 1 => -- const d k
    opt (f2 s) fun k => ret1 s s.mem k
  | 2 => -- mov d a
    opt (f2 s) fun a => opt (ld s a) fun va => ret1 s s.mem va
  | 3 => bin (fun a b => some (a + b)) s
  | 4 => bin (fun a b => some (a - b)) s
  | 5 => bin (fun a b => some (a * b)) s
  | 6 => bin sdiv s
  | 7 => bin srem s
  | 8 => bin (fun a b => some (a &&& b)) s
  | 9 => bin (fun a b => some (a ||| b)) s
  | 10 => bin (fun a b => some (a ^^^ b)) s
  | 11 => bin (fun a b => some (a <<< (b.toNat % 64))) s
  | 12 => bin (fun a b => some (a >>> (b.toNat % 64))) s
  | 13 => bin (fun a b => some (bool (a.slt b))) s
  | 14 => bin (fun a b => some (bool (a == b))) s
  | 15 => -- ld d a : d := M[a]
    opt (f2 s) fun a => opt (ld s a) fun va => opt (s.mem.rd64 va) fun v => ret1 s s.mem v
  | 16 => -- st a b : M[a] := b
    opt (f1 s) fun a => opt (ld s a) fun va =>
    opt (f2 s) fun b => opt (ld s b) fun vb =>
    opt (s.mem.wr64 va vb) fun m => nxt s m
  | 17 => -- lea d a : d := the address of slot a
    opt (f2 s) fun a => ret1 s s.mem (slot s.fp a)
  | 18 => -- jmp L : pc := pc + L (a byte offset)
    opt (f1 s) fun l => .next { s with pc := s.pc + l }
  | 19 => -- brz a L
    opt (f1 s) fun a => opt (ld s a) fun va =>
    if va = 0 then opt (f2 s) fun l => .next { s with pc := s.pc + l }
    else .next { s with pc := s.pc + 16 }
  | 20 => -- call a k : the callee frame at slot k holds the return pc and the caller's fp
    opt (f1 s) fun a => opt (ld s a) fun t =>
    opt (f2 s) fun k =>
    opt (s.mem.wr64 (slot s.fp k) (s.pc + 16)) fun m1 =>
    opt (m1.wr64 (slot s.fp k + 8) s.fp) fun m2 =>
    .next { pc := t, fp := slot s.fp k, mem := m2 }
  | 21 => -- ret
    opt (s.mem.rd64 s.fp) fun p => opt (s.mem.rd64 (s.fp + 8)) fun f =>
    .next { s with pc := p, fp := f }
  | 22 => -- cas d a e : at M[a], expect slot e, store slot e+1; d := the old word
    opt (f2 s) fun a => opt (ld s a) fun va =>
    opt (f3 s) fun e => opt (ld s e) fun ve => opt (s.mem.rd64 (slot s.fp e + 8)) fun vn =>
    opt (s.mem.cas va ve vn) fun (old, m) => ret1 s m old
  | 23 => -- sys d a : number in slot a, arguments in a+1 .. a+6, result into slot d
    opt (f1 s) fun d => opt (f2 s) fun a =>
    opt (ld s a) fun nr => opt (s.mem.rd64 (slot s.fp a + 8)) fun a1 =>
    opt (s.mem.rd64 (slot s.fp a + 16)) fun a2 => opt (s.mem.rd64 (slot s.fp a + 24)) fun a3 =>
    opt (s.mem.rd64 (slot s.fp a + 32)) fun a4 => opt (s.mem.rd64 (slot s.fp a + 40)) fun a5 =>
    opt (s.mem.rd64 (slot s.fp a + 48)) fun a6 =>
    .sys ⟨nr, a1, a2, a3, a4, a5, a6⟩ fun r =>
      (r.mem.wr64 (slot s.fp d) r.ret).map fun m => { s with pc := s.pc + 16, mem := m }
  | _ => .fault

def step (s : S) : Res S :=
  opt (s.mem.rd8 s.pc) fun o => op o.toNat s

end Runner.IR
