import Grammatik.Code.Lower.Stmt

/-
  File:      Grammatik/Code/Lower/Func.lean
  Subject:   TRACK L, PHASE L1 -- THE LOWERING OF A FUNCTION, as a Lean function.

  `lowerFn lay P f` turns the body of function `f` of the program `P` (machine G: an `Endblock`
  over the context `D.params f`) into an IR function: parameter `i` arrives in register `i`
  (as its register image `regTy`); the entry block (label 0) gives every parameter an `alloc`
  cell and stores the argument into it (`prologue`; the cells are made LAST parameter first, so
  the context's first variable ends up the head of `cenv`), then jumps to the lowered body
  (labels from 1; `lowerEnd`). The answer type is `regTy` of `D.erg f`, or `void`.
-/

namespace Gabbro.Code.Lower

open Gabbro.Grammatik (Deklaration Programm Vertrag vertragVon Ctx Res)

variable [Conf] {D : Deklaration}

/-- The cells of the parameters: parameter `i` (of the list) is in register `i + base`. The last
    parameter is made first. Returns the code, the cell registers (first parameter first) and the
    next free register. -/
def prologue : List GTy → Nat → Nat → Option (List Instr × List Reg × Nat)
  | [], _, r => some ([], [], r)
  | τ :: τs, i, r =>
      match prologue τs (i + 1) r with
      | some (c2, as, r1) =>
          match bindCode τ (.reg i) r1 with
          | some (c, a, r2) => some (c2 ++ c, a :: as, r2)
          | none => none
      | none => none

/-- The IR type of a function's answer. -/
def retTy : Option GTy → Ty
  | none => .void
  | some τ => regTy τ

/-- The IR type of a function's answer, with its failure channel: the plain image, or the answer word. -/
def retTyF (n : Nat) (eo : Option GTy) : Ty := if n = 0 then retTy eo else .int (retW n eo)

/-- The IR parameters of a function with these parameter types. -/
def irParams (ps : List GTy) : List Param :=
  ps.zipIdx.map fun (τ, i) => ⟨regTy τ, i⟩

/-- **The lowering of function `f`.** -/
def lowerFn (lay : Layout D) (P : Programm D) (f : D.Fn) (name : String) : Option Func :=
  match prologue (D.params f) 0 (D.params f).length with
  | some (pc, cenv, r) =>
      match lowerEnd lay cenv (0, 0) (P.rumpf f) 1 ⟨r, 2⟩ with
      | some (blks, _) =>
          some ⟨name, irParams (D.params f), retTyF (D.gruende f) (D.erg f), ⟨0, [], pc, .jmp 1⟩ :: blks⟩
      | none => none
  | none => none

end Gabbro.Code.Lower
