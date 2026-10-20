import Grammatik.Code.Model.Types

/-
  File:      Grammatik/Code/Model/Syntax.lean
  Subject:   TRACK L -- `Code`: operands, instructions, terminators, blocks, functions, modules.

  `Code` is ISA-neutral by construction (`dokumente/PLAN-TRANSLATION-VALIDATION.md` 9a):
    * LOCALS are numbered registers with no bound and no class; allocating them to machine
      registers is the later backend's problem. There are NO condition flags and no status
      register: a comparison produces a word (`icmp`, 0 or 1), a branch (`br`) tests a word
      against zero -- that is one fused instruction on every ISA (`bne x, zero` on RISC-V, `cbnz`
      on AArch64, `test; jne` on x86). `brc` is the fused compare-and-branch, `br`'s two-step form.
    * Arithmetic has an EXPLICIT width and wraps around; whatever the ISAs disagree on is a
      PRECONDITION of the operation (division by zero, `INT_MIN / -1`, a shift by the width or
      more, an unaligned access): the step is STUCK there, never defined (`Semantics.lean`).
    * Atomics have the five orderings `rlx acq rel acrel seqc` on word-sized aligned cells; a
      read-modify-write is ONE abstract operation (`armw`, `cas`), a fence is abstract.
    * Calls have an abstract frame (arguments in, one result out); there are no ABI numbers.
  Names are short English words (at most five letters per word).

  Cuts: no first-class aggregate values, vectors, `inttoptr`/`ptrtoint`, exceptions; a `cmpxchg`
  returns two registers (the old value and the success flag).
-/

namespace Gabbro.Code

open Gabbro.Grammatik.Gleitkomma

abbrev Reg := Nat
abbrev Lbl := Nat

/-- An operand: a register, a constant, the address of a global, the null pointer. -/
inductive Opd where
  | reg (r : Reg)
  | int (w : Nat) (n : Int)
  | flt (g : F32)
  | dbl (g : F64)
  /-- `@g`: the pointer to global number `g` (global `g` is memory block `g`). -/
  | glob (g : Nat)
  | null
  deriving DecidableEq

inductive BinOp where
  | add | sub | mul | udiv | sdiv | urem | srem | shl | lshr | ashr | and | or | xor
  deriving DecidableEq, Repr

inductive FOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

inductive IPred where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr

inductive FPred where
  | oeq | one | olt | ole | ogt | oge
  deriving DecidableEq, Repr

inductive Cast where
  | zext | sext | trunc
  /-- `bitcast` between an integer and a float of the same width, or between pointers. -/
  | bits
  /-- `sitofp` / `uitofp`. -/
  | sitof | uitof
  deriving DecidableEq, Repr

/-- The memory orders of atomics. -/
inductive Order where
  | rlx | acq | rel | acrel | seqc
  deriving DecidableEq, Repr

inductive RmwOp where
  | xchg | add | sub | and | or | xor
  deriving DecidableEq, Repr

inductive Instr where
  /-- `d := a op b` at width `w` (wraps around; `udiv`, `sdiv`, `urem`, `srem`, `shl`, `lshr`,
      `ashr` have preconditions, see `BinOp.ap`). -/
  | bin (d : Reg) (op : BinOp) (w : Nat) (a b : Opd)
  | fbin (d : Reg) (op : FOp) (t : Ty) (a b : Opd)
  /-- `d := (a p b) ? 1 : 0` at width `w`. -/
  | icmp (d : Reg) (p : IPred) (w : Nat) (a b : Opd)
  | fcmp (d : Reg) (p : FPred) (t : Ty) (a b : Opd)
  /-- `d := c ≠ 0 ? a : b` -/
  | pick (d : Reg) (c : Opd) (t : Ty) (a b : Opd)
  | cast (d : Reg) (k : Cast) (s t : Ty) (a : Opd)
  /-- A fresh stack cell of type `t`; `d` points to it. -/
  | alloc (d : Reg) (t : Ty)
  /-- `d := *p` (aligned). -/
  | load (d : Reg) (t : Ty) (p : Opd)
  /-- `*p := v` (aligned). -/
  | store (t : Ty) (v p : Opd)
  /-- `d := p + offset of the index path` into a value of type `t`. -/
  | gep (d : Reg) (t : Ty) (p : Opd) (ix : List Opd) (inb : Bool)
  /-- An atomic load of a word-sized aligned cell. -/
  | aload (d : Reg) (t : Ty) (p : Opd) (o : Order)
  | astor (t : Ty) (v p : Opd) (o : Order)
  /-- One abstract read-modify-write (`d` gets the old value). -/
  | armw (d : Reg) (op : RmwOp) (t : Ty) (p v : Opd) (o : Order)
  /-- One abstract compare-and-swap: `d` gets the old value, `ok` the success flag. -/
  | cas (d ok : Reg) (t : Ty) (p e n : Opd) (so fo : Order)
  | fence (o : Order)
  /-- The INTERRUPT MASK of the executing core, as one word cell (`d := old word; word := v`, nonzero masks).
      The cell `p` addresses is the core's architectural mask word, not RAM: that is a named hardware
      assumption (`Conc/MaskNeed.lean`), no ISA instruction is named here. -/
  | imsk (d : Reg) (p v : Opd)
  /-- `[d :=] call f(args)` -- a direct call of function number `f` of the module. -/
  | call (d : Option Reg) (f : Nat) (args : List Opd)
  /-- Stuck when `c` is zero: a fact the checker has proved, handed to the optimiser. -/
  | fact (c : Opd)

inductive Term where
  /-- `br label %l` -/
  | jmp (l : Lbl)
  /-- Branch to `t` if the word `c` is nonzero, else to `e`. -/
  | br (c : Opd) (t e : Lbl)
  /-- Fused compare-and-branch: `a p b` at width `w`. -/
  | brc (p : IPred) (w : Nat) (a b : Opd) (t e : Lbl)
  /-- `switch iW v, label %dflt [ iW n, label %l ... ]` -/
  | sw (w : Nat) (v : Opd) (dflt : Lbl) (cs : List (Int × Lbl))
  /-- `ret t v` / `ret void` -/
  | ret (v : Option Opd)
  /-- `unreachable` -/
  | dead

/-- `%d = phi t [v, %l], ...` -/
structure Phi where
  d : Reg
  t : Ty
  ins : List (Lbl × Opd)

structure Block where
  lbl : Lbl
  phis : List Phi
  body : List Instr
  term : Term

/-- A parameter: its type and the register it arrives in. -/
structure Param where
  t : Ty
  r : Reg

structure Func where
  name : String
  params : List Param
  ret : Ty
  /-- The entry block is the first one. -/
  blks : List Block

/-- A zero-initialised global. -/
structure Glob where
  name : String
  t : Ty

/-- A module: its globals (global `i` is memory block `i`) and its functions. -/
structure Modl where
  globs : List Glob
  funs : List Func

namespace Modl

/-- The block labelled `l` of function number `f`. -/
def blk (M : Modl) (f : Nat) (l : Lbl) : Option Block :=
  (M.funs[f]?).bind fun fn => fn.blks.find? fun b => b.lbl == l

/-- The entry block of function number `f`. -/
def entry (M : Modl) (f : Nat) : Option Block :=
  (M.funs[f]?).bind fun fn => fn.blks.head?

end Modl

end Gabbro.Code
