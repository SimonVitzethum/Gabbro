import Grammatik.Llvm.Model.Syntax
import Grammatik.Llvm.Model.Memory

/-
  File:      Grammatik/Llvm/Model/Semantics.lean
  Subject:   TRACK L, PHASE L0 -- THE SMALL-STEP SEMANTICS of the IR subset.

  A configuration is `run m f ks` -- the memory, the running frame (function, block label, index
  of the next instruction in the block body, register file, where its caller wants the result)
  and the frames of the callers -- or `fin m v`, a finished run with its result.

  `step M O c` is ONE step, a FUNCTION of the configuration and of an ORACLE `O`. The oracle
  answers the only two questions the semantics itself does not decide:
    * what an ATOMIC LOAD returns (`Oracle.ld`) -- the weak-memory interface, see below;
    * what an OPAQUE instruction (inline assembly) gives back and does to memory (`Oracle.asm`).
  Everything else -- arithmetic, plain loads and stores, calls, branches -- is deterministic, so
  the oracle enters `step` in exactly two instruction forms (`step_indep`).

  The RELATION `Step M S c c'` says: some LEGAL oracle makes `step` produce `c'`. Legal means:
    * an atomic load returns only a value the memory-model interface `S` allows
      (`Sees`: memory, block, offset, type, order, value) -- for sequential consistency `S` is
      "the value in memory" (`Sees.sc`), for the weak memory the messages the view may read:
      the same shape as machine GX, whose reads of the shared atomics are answered by a
      PRESENTED memory that agrees with G's everywhere else (`Zielsatz`, `GXMaschine.lean`);
    * an opaque instruction changes memory only as its declared effect `Eff` allows (`Eff.ok`).
  So no memory model is invented here: the IR is parameterised by the interface the proofs
  about threads already use, and `Weak.lean` links the orders to `Speichermodell.Ordnung`.

  WHAT GETS STUCK (`step` is `none`) -- the model's word for undefined behaviour and poison,
  read strictly: division by zero, signed overflow of `sdiv`/`srem`, a shift by the width or
  more, a load or store outside its block or on a never written cell or misaligned, a violated
  `!range`/`!tbaa` annotation, a false `llvm.assume`, `unreachable`, a type mismatch,
  `noalias` arguments that share a block.
-/

namespace Gabbro.Llvm

open Gabbro.Grammatik.Gleitkomma

/-! ## 1. Registers, frames, configurations -/

abbrev Regs := Reg → Option Val

def Regs.set (rs : Regs) (d : Reg) (v : Val) : Regs := fun x => if x = d then some v else rs x

structure Frame where
  fn : Nat
  lbl : Lbl
  /-- The index of the next instruction in the body of block `lbl`; one past the last means
      "at the terminator". -/
  pc : Nat
  regs : Regs
  /-- Where the CALLER wants this frame's result. -/
  dst : Option Reg := none

def Frame.adv (f : Frame) : Frame := { f with pc := f.pc + 1 }

def Frame.setr (f : Frame) (d : Reg) (v : Val) : Frame := { f with regs := f.regs.set d v }

inductive Cfg where
  | run (m : Mem) (f : Frame) (ks : List Frame)
  | fin (m : Mem) (v : Option Val)

/-- The block no allocation ever has: the null pointer. -/
def nullBlk : Nat := 2 ^ 62

/-- Evaluate an operand in a register file. -/
def Opd.ev (rs : Regs) : Opd → Option Val
  | .reg r => rs r
  | .int w n => some (Val.ofInt w n)
  | .flt g => some (.flt g)
  | .dbl g => some (.dbl g)
  | .glob g => some (.ptr g 0)
  | .null => some (.ptr nullBlk 0)

/-! ## 2. Pure operations -/

/-- The meaning of an annotation, as a proposition over the typed value it sits on. -/
def Meta.ok : Meta → Ty → Val → Bool
  | .range lo hi, _, .int w v =>
      decide (lo % ((2 : Int) ^ w) = hi % ((2 : Int) ^ w))
        || decide (((v.toNat : Int) - lo) % ((2 : Int) ^ w) < (hi - lo) % ((2 : Int) ^ w))
  | .range .., _, _ => false
  | .tbaa t, t', _ => decide (t = t')

def Meta.holds (μ : Meta) (t : Ty) (v : Val) : Prop := μ.ok t v = true

/-- Integer arithmetic of width `w`. `none` is stuck. -/
def BinOp.ap : BinOp → (w : Nat) → BitVec w → BitVec w → Option (BitVec w)
  | .add, _, a, b => some (a + b)
  | .sub, _, a, b => some (a - b)
  | .mul, _, a, b => some (a * b)
  | .udiv, _, a, b => if b = 0 then none else some (a / b)
  | .urem, _, a, b => if b = 0 then none else some (a % b)
  | .sdiv, w, a, b =>
      if b = 0 ∨ (a.toInt = -((2 : Int) ^ (w - 1)) ∧ b.toInt = -1) then none else some (a.sdiv b)
  | .srem, w, a, b =>
      if b = 0 ∨ (a.toInt = -((2 : Int) ^ (w - 1)) ∧ b.toInt = -1) then none else some (a.srem b)
  | .shl, w, a, b => if b.toNat < w then some (a <<< b.toNat) else none
  | .lshr, w, a, b => if b.toNat < w then some (a >>> b.toNat) else none
  | .ashr, w, a, b => if b.toNat < w then some (a.sshiftRight b.toNat) else none
  | .and, _, a, b => some (a &&& b)
  | .or, _, a, b => some (a ||| b)
  | .xor, _, a, b => some (a ^^^ b)

def IPred.ap : IPred → {w : Nat} → BitVec w → BitVec w → Bool
  | .eq, _, a, b => decide (a = b)
  | .ne, _, a, b => !decide (a = b)
  | .ult, _, a, b => a.ult b
  | .ule, _, a, b => a.ule b
  | .ugt, _, a, b => b.ult a
  | .uge, _, a, b => b.ule a
  | .slt, _, a, b => a.slt b
  | .sle, _, a, b => a.sle b
  | .sgt, _, a, b => b.slt a
  | .sge, _, a, b => b.sle a

/-- Both operands are `iW`; the result is `iW`. -/
def Val.bin (op : BinOp) (w : Nat) : Val → Val → Option Val
  | .int w1 x, .int w2 y =>
      if h1 : w1 = w then
        if h2 : w2 = w then (op.ap w (h1 ▸ x) (h2 ▸ y)).map (Val.int w) else none
      else none
  | _, _ => none

/-- `icmp`: both operands `iW`, the result `i1`. -/
def Val.icmp (p : IPred) (w : Nat) : Val → Val → Option Val
  | .int w1 x, .int w2 y =>
      if h1 : w1 = w then
        if h2 : w2 = w then some (Val.bool (p.ap (h1 ▸ x) (h2 ▸ y))) else none
      else none
  | _, _ => none

/-- Float arithmetic of the kernel IEEE model. -/
def Val.fbin (op : FOp) : Val → Val → Option Val
  | .flt a, .flt b =>
      some (.flt (match op with
        | .add => add f32 a b | .sub => sub f32 a b | .mul => mul f32 a b | .div => div f32 a b))
  | .dbl a, .dbl b =>
      some (.dbl (match op with
        | .add => add f64 a b | .sub => sub f64 a b | .mul => mul f64 a b | .div => div f64 a b))
  | _, _ => none

def fcmpAp (F : Format) (p : FPred) (a b : GBits F) : Bool :=
  match p with
  | .oeq => fle F a b && fle F b a
  | .one => flt F a b || flt F b a
  | .olt => flt F a b
  | .ole => fle F a b
  | .ogt => flt F b a
  | .oge => fle F b a

def Val.fcmp (p : FPred) : Val → Val → Option Val
  | .flt a, .flt b => some (Val.bool (fcmpAp f32 p a b))
  | .dbl a, .dbl b => some (Val.bool (fcmpAp f64 p a b))
  | _, _ => none

/-- A conversion to type `t`. -/
def Val.cast (k : Cast) (t : Ty) : Val → Option Val
  | .int w x =>
      match k, t with
      | .zext, .int w' => if w ≤ w' then some (.int w' (x.setWidth w')) else none
      | .sext, .int w' => if w ≤ w' then some (.int w' (x.signExtend w')) else none
      | .trunc, .int w' => if w' ≤ w then some (.int w' (x.setWidth w')) else none
      | .bits, .flt => if w = 32 then some (.flt (ausBits f32 x.toNat)) else none
      | .bits, .dbl => if w = 64 then some (.dbl (ausBits f64 x.toNat)) else none
      | .sitof, .flt => some (.flt (Gabbro.Grammatik.Gleitkomma.ofInt f32 x.toInt))
      | .sitof, .dbl => some (.dbl (Gabbro.Grammatik.Gleitkomma.ofInt f64 x.toInt))
      | .uitof, .flt => some (.flt (Gabbro.Grammatik.Gleitkomma.ofInt f32 (x.toNat : Int)))
      | .uitof, .dbl => some (.dbl (Gabbro.Grammatik.Gleitkomma.ofInt f64 (x.toNat : Int)))
      | _, _ => none
  | .flt g =>
      match k, t with
      | .bits, .int 32 => some (.int 32 (BitVec.ofNat 32 (zuBits f32 g)))
      | _, _ => none
  | .dbl g =>
      match k, t with
      | .bits, .int 64 => some (.int 64 (BitVec.ofNat 64 (zuBits f64 g)))
      | _, _ => none
  | .ptr b o =>
      match k, t with
      | .bits, .ptr => some (.ptr b o)
      | _, _ => none

/-- The integer an index operand denotes (signed). -/
def Val.idx : Val → Option Int
  | .int _ x => some x.toInt
  | _ => none

/-- The new value of an `atomicrmw`. -/
def RmwOp.ap (op : RmwOp) : Val → Val → Option Val
  | .int w x, .int w2 y =>
      if h : w2 = w then
        some (.int w (match op with
          | .xchg => h ▸ y | .add => x + h ▸ y | .sub => x - h ▸ y
          | .and => x &&& h ▸ y | .or => x ||| h ▸ y | .xor => x ^^^ h ▸ y))
      else none
  | _, v => match op with | .xchg => some v | _ => none

/-! ## 3. Straight-line instructions: `stepI` -/

/-- The alignment check of an access: `al = 0` means "natural, not stated". -/
def alignOk (al : Nat) (o : Int) : Prop := al = 0 ∨ o % (al : Int) = 0

instance (al : Nat) (o : Int) : Decidable (alignOk al o) := by
  unfold alignOk; exact inferInstance

/-- Is an `inbounds` address within its block (one past the end allowed)? -/
def inBlock (m : Mem) (b : Nat) (o : Int) : Bool :=
  match m.blks b with
  | some blk => decide (0 ≤ o ∧ o ≤ (blk.size : Int))
  | none => false

/-- One non-control, non-call, non-oracle instruction on memory and registers. `none` is stuck
    -- and also the answer for the three instruction forms handled by `step` itself
    (`call`, `aload`, `asm`). -/
def stepI : Instr → Mem → Regs → Option (Mem × Regs)
  | .bin d op w a b, m, rs =>
      match a.ev rs, b.ev rs with
      | some x, some y => (Val.bin op w x y).map fun v => (m, rs.set d v)
      | _, _ => none
  | .fbin d op _ a b, m, rs =>
      match a.ev rs, b.ev rs with
      | some x, some y => (Val.fbin op x y).map fun v => (m, rs.set d v)
      | _, _ => none
  | .icmp d p w a b, m, rs =>
      match a.ev rs, b.ev rs with
      | some x, some y => (Val.icmp p w x y).map fun v => (m, rs.set d v)
      | _, _ => none
  | .fcmp d p _ a b, m, rs =>
      match a.ev rs, b.ev rs with
      | some x, some y => (Val.fcmp p x y).map fun v => (m, rs.set d v)
      | _, _ => none
  | .pick d c t a b, m, rs =>
      match c.ev rs, a.ev rs, b.ev rs with
      | some (.int 1 x), some u, some v =>
          if u.ty = t ∧ v.ty = t then some (m, rs.set d (if x = 1 then u else v)) else none
      | _, _, _ => none
  | .cast d k s t a, m, rs =>
      match a.ev rs with
      | some x => if x.ty = s then (Val.cast k t x).map fun v => (m, rs.set d v) else none
      | none => none
  | .alloc d t _, m, rs =>
      let r := m.alloc t.size false
      some (r.1, rs.set d (.ptr r.2 0))
  | .load d t p al _ ms, m, rs =>
      match p.ev rs with
      | some (.ptr b o) =>
          if alignOk al o then
            match m.load b o t with
            | some v => if ms.all (fun μ => μ.ok t v) then some (m, rs.set d v) else none
            | none => none
          else none
      | _ => none
  | .store t v p al _ ms, m, rs =>
      match v.ev rs, p.ev rs with
      | some x, some (.ptr b o) =>
          if alignOk al o ∧ ms.all (fun μ => μ.ok t x) = true then
            (m.store b o t x).map fun m' => (m', rs)
          else none
      | _, _ => none
  | .gep d t p ix inb, m, rs =>
      match p.ev rs, ix.mapM (fun i => (i.ev rs).bind Val.idx) with
      | some (.ptr b o), some is =>
          match Ty.gepOff t is with
          | some (off, _) =>
              if !inb || inBlock m b (o + off) then some (m, rs.set d (.ptr b (o + off))) else none
          | none => none
      | _, _ => none
  | .astor t v p _ _, m, rs =>
      match v.ev rs, p.ev rs with
      | some x, some (.ptr b o) =>
          if o % (t.store : Int) = 0 then (m.store b o t x).map fun m' => (m', rs) else none
      | _, _ => none
  | .armw d op t p v _, m, rs =>
      match p.ev rs, v.ev rs with
      | some (.ptr b o), some x =>
          if o % (t.store : Int) = 0 then
            match m.load b o t with
            | some old =>
                match op.ap old x with
                | some new => (m.store b o t new).map fun m' => (m', rs.set d old)
                | none => none
            | none => none
          else none
      | _, _ => none
  | .cas d ok t p e n _ _, m, rs =>
      match p.ev rs, e.ev rs, n.ev rs with
      | some (.ptr b o), some ex, some nw =>
          if o % (t.store : Int) = 0 then
            match m.load b o t with
            | some old =>
                if old = ex then (m.store b o t nw).map fun m' => (m', (rs.set d old).set ok (Val.bool true))
                else some (m, (rs.set d old).set ok (Val.bool false))
            | none => none
          else none
      | _, _, _ => none
  | .fence _, m, rs => some (m, rs)
  | .fact c, m, rs =>
      match c.ev rs with
      | some (.int 1 x) => if x = 1 then some (m, rs) else none
      | _ => none
  | .aload .., _, _ => none
  | .call .., _, _ => none
  | .asm .., _, _ => none

end Gabbro.Llvm
