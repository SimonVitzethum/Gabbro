import Runner.Basis.Res

/-! # `S0IR`: the instructions and their small-step semantics (`PLAN-SELF-HOSTING.md` §2.1.3)

An instruction is 16 bytes at `pc`: the opcode in byte 0 (bytes 1-3 are ignored), then three little-endian 32-bit
operand fields at `pc + 4`, `pc + 8`, `pc + 12`, each sign-extended to 64 bits. An operand names a slot of the
current frame, the word at `fp + 8·i`. A thread is `pc` and `fp`; the code, the frames and everything else lie in
the shared memory, and every access is a request (`Runner/Basis/Res.lean`): a step is a tree of requests in a
fixed order, so every image -- also one that writes over its own code -- has a defined run under every memory
model. The runner's handler makes the same requests in the same order (`Runner/Beweis/`).

`spawn` asks the kernel for `clone` with fixed flags (a thread sharing the memory); the machine starts the new
thread with the answer 0 (`Runner/Mach/`), the parent continues with the thread id or the error. -/

namespace Runner.IR

structure T where
  pc : W
  fp : W
  deriving DecidableEq

def sx (v : BitVec 32) : W := v.signExtend 64

/-- The address of slot `i` of the frame at `fp`. -/
def slot (fp i : W) : W := fp + i * 8

def f1 (t : T) (f : W → Res T) : Res T := rd32 (t.pc + 4) fun v => f (sx v)
def f2 (t : T) (f : W → Res T) : Res T := rd32 (t.pc + 8) fun v => f (sx v)
def f3 (t : T) (f : W → Res T) : Res T := rd32 (t.pc + 12) fun v => f (sx v)

/-- The value of slot `i`. -/
def ld (t : T) (i : W) (f : W → Res T) : Res T := rd64 (slot t.fp i) f

def nxt (t : T) : T := { t with pc := t.pc + 16 }

/-- Store `r` into the slot named by field 1, then the next instruction. -/
def ret1 (t : T) (r : W) : Res T := f1 t fun d => wr64 (slot t.fp d) r (nxt t)

/-- `d := g a b` with `a`, `b` the slots of fields 2 and 3 and `d` the slot of field 1. -/
def bin (g : W → W → Option W) (t : T) : Res T :=
  f2 t fun a => ld t a fun va => f3 t fun b => ld t b fun vb => opt (g va vb) fun r => ret1 t r

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

/-- One instruction, by opcode. Opcode 0 and 25-255 fault. -/
def op (o : Nat) (t : T) : Res T :=
  match o with
  | 1 => -- const d k
    f2 t fun k => ret1 t k
  | 2 => -- mov d a
    f2 t fun a => ld t a fun va => ret1 t va
  | 3 => bin (fun a b => some (a + b)) t
  | 4 => bin (fun a b => some (a - b)) t
  | 5 => bin (fun a b => some (a * b)) t
  | 6 => bin sdiv t
  | 7 => bin srem t
  | 8 => bin (fun a b => some (a &&& b)) t
  | 9 => bin (fun a b => some (a ||| b)) t
  | 10 => bin (fun a b => some (a ^^^ b)) t
  | 11 => bin (fun a b => some (a <<< (b.toNat % 64))) t
  | 12 => bin (fun a b => some (a >>> (b.toNat % 64))) t
  | 13 => bin (fun a b => some (bool (a.slt b))) t
  | 14 => bin (fun a b => some (bool (a == b))) t
  | 15 => -- ld d a : d := M[a]
    f2 t fun a => ld t a fun va => rd64 va fun v => ret1 t v
  | 16 => -- st a b : M[a] := b
    f1 t fun a => ld t a fun va => f2 t fun b => ld t b fun vb => wr64 va vb (nxt t)
  | 17 => -- lea d a : d := the address of slot a
    f2 t fun a => ret1 t (slot t.fp a)
  | 18 => -- jmp L : pc := pc + L (a byte offset)
    f1 t fun l => .next { t with pc := t.pc + l }
  | 19 => -- brz a L
    f1 t fun a => ld t a fun va =>
    if va = 0 then f2 t fun l => .next { t with pc := t.pc + l } else .next (nxt t)
  | 20 => -- call a k : the callee frame at slot k holds the return pc and the caller's fp
    f1 t fun a => ld t a fun c => f2 t fun k =>
    .ask (.wr (slot t.fp k) (t.pc + 16)) fun r => opt r fun _ =>
    wr64 (slot t.fp k + 8) t.fp { pc := c, fp := slot t.fp k }
  | 21 => -- ret
    rd64 t.fp fun p => rd64 (t.fp + 8) fun f => .next { pc := p, fp := f }
  | 22 => -- cas d a e : at M[a], expect slot e, store slot e+1; d := the old word
    f2 t fun a => ld t a fun va => f3 t fun e => ld t e fun ve => rd64 (slot t.fp e + 8) fun vn =>
    cas va ve vn fun old => ret1 t old
  | 23 => -- sys d a : number in slot a, arguments in a+1 .. a+6, result into slot d
    f1 t fun d => f2 t fun a =>
    ld t a fun nr => rd64 (slot t.fp a + 8) fun a1 => rd64 (slot t.fp a + 16) fun a2 =>
    rd64 (slot t.fp a + 24) fun a3 => rd64 (slot t.fp a + 32) fun a4 => rd64 (slot t.fp a + 40) fun a5 =>
    rd64 (slot t.fp a + 48) fun a6 =>
    .ask (.sys ⟨nr, a1, a2, a3, a4, a5, a6⟩) fun r => opt r fun p => wr64 (slot t.fp d) p.1 (nxt t)
  | 24 => -- spawn d a : a new thread at the code address in slot a with the frame in slot a+1
    f2 t fun a => ld t a fun c => rd64 (slot t.fp a + 8) fun f =>
    .ask (.sys cloneReq) fun r => opt r fun p =>
    if p.1 = 0 then .next { pc := c, fp := f } else ret1 t p.1
  | _ => .fault

def step (t : T) : Res T := rd8 t.pc fun o => op o.toNat t

end Runner.IR
