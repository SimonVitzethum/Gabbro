import Grammatik.Llvm.Model.Types

/-
  File:      Grammatik/Llvm/Model/Syntax.lean
  Subject:   TRACK L, PHASE L0 -- THE SYNTAX OF THE IR SUBSET: operands, instructions,
             terminators, blocks, functions, modules.

  Naming. Every constructor is a short English word (at most five letters per word). Where the
  LLVM mnemonic is longer or collides with a Lean keyword the printer (`Print.lean`) carries the
  mapping:  `alloc` = alloca, `pick` = select, `fact` = `call @llvm.assume`, `jmp` = `br label`,
  `br` = `br i1`, `sw` = switch, `dead` = unreachable, `astor` = `store atomic`,
  `aload` = `load atomic`, `armw` = atomicrmw, `cas` = cmpxchg, `sitof` = sitofp.

  What is NOT carried (named cuts, `PLAN-UEBERSETZUNGSVALIDIERUNG.md` 9a):
    * wrap/exact/inbounds-nuw flags on integer arithmetic (the semantics is plain modular
      arithmetic, and a violated precondition -- division by zero, an out-of-range shift -- is
      STUCK, the model's word for poison and undefined behaviour, which is the strict reading);
    * first-class aggregate values, vectors, `inttoptr`, `ptrtoint`, `invoke`, exceptions;
    * a `cmpxchg` returns two registers (the old value and the success flag) instead of a pair.
-/

namespace Gabbro.Llvm

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

/-- The memory orders of LLVM atomics. -/
inductive Order where
  | unord | mono | acq | rel | acrel | seqc
  deriving DecidableEq, Repr

inductive RmwOp where
  | xchg | add | sub | and | or | xor
  deriving DecidableEq, Repr

/-- Metadata a lowering attaches, as PROOF-CARRYING ANNOTATIONS: each one has a meaning stated
    as a proposition over the value or the access (`Semantics.lean`, `Meta.ok`), and the
    semantics is stuck when it is false -- so a program that runs satisfies all of them. -/
inductive Meta where
  /-- `!range !{iN lo, iN hi}`: the loaded integer lies in the half-open circular interval. -/
  | range (lo hi : Int)
  /-- `!tbaa`: the access has exactly this scalar type. -/
  | tbaa (t : Ty)
  deriving DecidableEq

/-- The declared effect of an opaque instruction (inline assembly, a declared function). -/
inductive Eff where
  /-- touches no memory. -/
  | pure
  /-- reads memory, writes none. -/
  | read
  /-- writes memory only in the blocks its pointer arguments point to. -/
  | write
  /-- may change any existing memory, but never its allocation structure. -/
  | any
  deriving DecidableEq, Repr

inductive Instr where
  /-- `%d = op iW a, b` -/
  | bin (d : Reg) (op : BinOp) (w : Nat) (a b : Opd)
  /-- `%d = fop float|double a, b` -/
  | fbin (d : Reg) (op : FOp) (t : Ty) (a b : Opd)
  /-- `%d = icmp p iW a, b` -/
  | icmp (d : Reg) (p : IPred) (w : Nat) (a b : Opd)
  | fcmp (d : Reg) (p : FPred) (t : Ty) (a b : Opd)
  /-- `%d = select i1 c, t a, t b` -/
  | pick (d : Reg) (c : Opd) (t : Ty) (a b : Opd)
  /-- `%d = k s a to t` -/
  | cast (d : Reg) (k : Cast) (s t : Ty) (a : Opd)
  /-- `%d = alloca t, align al` -/
  | alloc (d : Reg) (t : Ty) (al : Nat)
  /-- `%d = load [volatile] t, ptr p, align al, !range .. !tbaa ..` -/
  | load (d : Reg) (t : Ty) (p : Opd) (al : Nat) (vol : Bool) (ms : List Meta)
  /-- `store [volatile] t v, ptr p, align al, !tbaa ..` -/
  | store (t : Ty) (v p : Opd) (al : Nat) (vol : Bool) (ms : List Meta)
  /-- `%d = getelementptr [inbounds] t, ptr p, i0, i1, ..` -/
  | gep (d : Reg) (t : Ty) (p : Opd) (ix : List Opd) (inb : Bool)
  /-- `%d = load atomic t, ptr p ord, align al` -/
  | aload (d : Reg) (t : Ty) (p : Opd) (o : Order) (al : Nat)
  /-- `store atomic t v, ptr p ord, align al` -/
  | astor (t : Ty) (v p : Opd) (o : Order) (al : Nat)
  /-- `%d = atomicrmw op ptr p, t v ord` (`d` gets the old value) -/
  | armw (d : Reg) (op : RmwOp) (t : Ty) (p v : Opd) (o : Order)
  /-- `cmpxchg ptr p, t e, t n so fo`: `d` gets the old value, `ok` the success flag. -/
  | cas (d ok : Reg) (t : Ty) (p e n : Opd) (so fo : Order)
  | fence (o : Order)
  /-- `[%d =] call @f(args)` -- a direct call of function number `f` of the module. -/
  | call (d : Option Reg) (f : Nat) (args : List Opd)
  /-- An opaque instruction: inline assembly (or a declared function). It gives back any value
      of type `t` (when `d` names a register) and changes memory as `eff` allows. -/
  | asm (d : Option Reg) (t : Ty) (eff : Eff) (args : List Opd) (txt : String)
  /-- `call void @llvm.assume(i1 c)`: stuck when `c` is false. -/
  | fact (c : Opd)

inductive Term where
  /-- `br label %l` -/
  | jmp (l : Lbl)
  /-- `br i1 c, label %t, label %e` -/
  | br (c : Opd) (t e : Lbl)
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

/-- A parameter: its type, the register it arrives in, and `noalias`. -/
structure Param where
  t : Ty
  r : Reg
  noali : Bool := false

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

end Gabbro.Llvm
