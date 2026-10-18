import Grammatik.Code.Lower.Rep

/-
  File:      Grammatik/Code/Lower/Expr.lean
  Subject:   TRACK L, PHASE L1 -- THE LOWERING OF EXPRESSIONS, as a Lean function.

  `lowerE lay cenv e r` turns an expression of machine G into straight-line IR: the list of
  instructions, the operand that holds the value, and the next free register. Registers are
  numbered in program order (`r`, `r + 1`, ...); every variable of the context lives in an
  `alloc` cell whose register is `cenv[x.idx]`.

  THE FRAGMENT: constants, variables, globals, table slots (also through a pointer),
  widening, `+ - * neg`, `/ %` on non-negative numerators and denominators `>= 1` (the instruction's
  precondition is a fact of the ranges), `< <= ==`, `&& || !`. Every other form lowers to `none` (the Rust
  the lowering refuses it); `none` is also the answer for a type outside `supp`
  or a range beyond 128 bits. Integer ranges live in `Ar.wid` bits; an operation is carried out at
  the width of its RESULT range, its operands moved there by `cvt` (`sext`/`zext` by the sign of
  the operand's own range, `trunc` when narrower), which is exact modulo `2^w`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Expr Ctx Var)

variable {D : Deklaration}

/-- The index of a variable: its position in the context. -/
def varIdx : {Γ : Ctx} → {τ : GTy} → Var Γ τ → Nat
  | _, _, .here => 0
  | _, _, .there x => varIdx x + 1

/-- A lowered fragment: instructions, the operand holding the value, the next free register. -/
abbrev LR := List Instr × Opd × Nat

/-- Move an `iSRC` operand to `iDST`: `sext`/`zext` when widening (by `signed`), `trunc` when
    narrowing, nothing when equal. -/
def cvt (src dst : Nat) (signed : Bool) (o : Opd) (r : Nat) : LR :=
  if src = dst then ([], o, r)
  else if src < dst then
    ([.cast r (if signed then .sext else .zext) (.int src) (.int dst) o], .reg r, r + 1)
  else ([.cast r .trunc (.int src) (.int dst) o], .reg r, r + 1)

/-- The width of an integer type. -/
def twid : GTy → Nat
  | .int lo hi => Ar.wid lo hi
  | _ => 0

/-- Is it a signed range? -/
def tsgn : GTy → Bool
  | .int lo _ => decide (lo < 0)
  | _ => false

/-- Move an integer-typed operand from its own width to the width of `τ`. -/
def cvtG (σ τ : GTy) (o : Opd) (r : Nat) : Option LR :=
  match σ, τ with
  | .int _ _, .int _ _ => some (cvt (twid σ) (twid τ) (tsgn σ) o r)
  | _, _ => none

/-- Load a scalar of type `τ` from a pointer operand. -/
def loadG (τ : GTy) (p : Opd) (r : Nat) : Option LR :=
  match τ with
  | .int lo hi =>
      if Ar.Fits lo hi 128 then some ([.load r (.int (Ar.wid lo hi)) p], .reg r, r + 1) else none
  | .bool =>
      some ([.load r (.int 8) p, .cast (r + 1) .trunc (.int 8) (.int 1) (.reg r)],
            .reg (r + 1), r + 2)
  | .ptr _ _ => some ([.load r .ptr p], .reg r, r + 1)
  | .opt n =>
      if Ar.Fits (-1) (n - 1) 128 then some ([.load r (.int (Ar.wid (-1) (n - 1))) p], .reg r, r + 1) else none
  | .why n =>
      if Ar.Fits 0 ((n : Int) - 1) 128 then
        some ([.load r (.int (Ar.wid 0 ((n : Int) - 1))) p], .reg r, r + 1) else none
  | .sum cs =>
      if Ar.Fits 0 (sumTop cs) 128 then
        some ([.load r (.int (Ar.wid 0 (sumTop cs))) p], .reg r, r + 1) else none
  | _ => none

/-- Does an integer type fit the widths the lowering knows? -/
def fitsT : GTy → Bool
  | .int lo hi => decide (Ar.Fits lo hi 128)
  | _ => false

/-- The tail of a binary operation: move both operands to the width of the result type `τ`,
    then the instruction. -/
def binRest (op : BinOp) (τ σa σb : GTy) (oa ob : Opd) (r : Nat) : Option LR :=
  match cvtG σa τ oa r with
  | some (c1, oa', r1) =>
      match cvtG σb τ ob r1 with
      | some (c2, ob', r2) =>
          if fitsT τ then some (c1 ++ c2 ++ [.bin r2 op (twid τ) oa' ob'], .reg r2, r2 + 1) else none
      | none => none
  | none => none

/-- The union of two integer ranges, as a type. -/
def joinT : GTy → GTy → GTy
  | .int l1 h1, .int l2 h2 => .int (min l1 l2) (max h1 h2)
  | _, _ => .bool

/-- The tail of a comparison: both operands at the width of the joined range, compared unsigned
    or signed by the sign of the joined range. -/
def cmpRest (pu ps : IPred) (σa σb : GTy) (oa ob : Opd) (r : Nat) : Option LR :=
  match σa, σb with
  | .int _ _, .int _ _ =>
      let j := joinT σa σb
      match cvtG σa j oa r with
      | some (c1, oa', r1) =>
          match cvtG σb j ob r1 with
          | some (c2, ob', r2) =>
              if fitsT j then
                some (c1 ++ c2 ++ [.icmp r2 (if tsgn j then ps else pu) (twid j) oa' ob'],
                      .reg r2, r2 + 1)
              else none
          | none => none
      | none => none
  | _, _ => none

/-- The tail of an unsigned division or remainder (`div`, `rem`: the numerator is `>= 0` and the
    denominator `>= 1`, so the instruction's precondition -- a nonzero divisor -- holds): both operands
    at the width of the JOINED range (so the divisor is not truncated), the instruction, then the
    result moved to the width of its own type. -/
def divRest (op : BinOp) (τ σa σb : GTy) (oa ob : Opd) (r : Nat) : Option LR :=
  match σa, σb with
  | .int _ _, .int _ _ =>
      let j := joinT σa σb
      match cvtG σa j oa r with
      | some (c1, oa', r1) =>
          match cvtG σb j ob r1 with
          | some (c2, ob', r2) =>
              if fitsT j && fitsT τ then
                match cvtG j τ (.reg r2) (r2 + 1) with
                | some (c3, o3, r3) => some (c1 ++ c2 ++ [.bin r2 op (twid j) oa' ob'] ++ c3, o3, r3)
                | none => none
              else none
          | none => none
      | none => none
  | _, _ => none

/-- The type of an expression, as a value. -/
def ety {Γ : Ctx} {Λ : List (Gabbro.Grammatik.Res D)} {τ : GTy} (_ : Expr D Γ Λ τ) : GTy := τ

/-- The address of field `f` of the slot an index operand names, from a base pointer. -/
def slotAddr (lay : Layout D) (t : D.Tab) (f : D.Feld t) (base : Opd) (iτ : GTy) (oi : Opd)
    (r : Nat) : Option LR :=
  if D.count t ≤ 2 ^ (Conf.wbits - 2) ∧ Ar.Fits 0 (D.count t - 1) 128 then
    match cvtG iτ (.int 0 (2 ^ Conf.wbits - 1)) oi r with
    | some (c, ow, r1) =>
        some (c ++ [.gep r1 (lay.tty t) base [.int Conf.wbits 0, ow, .int Conf.wbits (lay.fidx t f)] true],
              .reg r1, r1 + 1)
    | none => none
  else none

/-- **The lowering of expressions.** -/
def lowerE (lay : Layout D) (cenv : List Reg) :
    {Γ : Ctx} → {Λ : List (Gabbro.Grammatik.Res D)} → {τ : GTy} → Expr D Γ Λ τ → Nat → Option LR
  | _, _, _, .lit n, r =>
      if Ar.Fits n n 128 then some ([], .int (Ar.wid n n) n, r) else none
  | _, _, _, .tru, r => some ([], .int 1 1, r)
  | _, _, _, .fls, r => some ([], .int 1 0, r)
  | _, _, τ, .var x, r =>
      match cenv[varIdx x]? with
      | some a => if supp τ then loadG τ (.reg a) r else none
      | none => none
  | _, _, _, .glob g _, r => if supp (D.gtyp g) then loadG (D.gtyp g) (.glob (lay.ggblk g)) r else none
  | _, _, _, .slot t f i _, r =>
      match lowerE lay cenv i r with
      | some (ci, oi, r1) =>
          match slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r1 with
          | some (ca, oa, r2) =>
              match (if supp (D.typ t f) then loadG (D.typ t f) oa r2 else none) with
              | some (cl, ol, r3) => some (ci ++ ca ++ cl, ol, r3)
              | none => none
          | none => none
      | none => none
  | _, _, _, .thru p t _ f i _, r =>
      match lowerE lay cenv p r with
      | some (cp, op, r1) =>
          match lowerE lay cenv i r1 with
          | some (ci, oi, r2) =>
              match slotAddr lay t f op (.int 0 (D.count t - 1)) oi r2 with
              | some (ca, oa, r3) =>
                  match (if supp (D.typ t f) then loadG (D.typ t f) oa r3 else none) with
                  | some (cl, ol, r4) => some (cp ++ ci ++ ca ++ cl, ol, r4)
                  | none => none
              | none => none
          | none => none
      | none => none
  | _, _, _, .ptrOf t _ _ _, r => some ([], .glob (lay.gblk t), r)
  | _, _, _, .widen h1 h2 e, r =>
      match lowerE lay cenv e r with
      | some (c, o, r1) =>
          match cvtG (ety e) (ety (Expr.widen h1 h2 e)) o r1 with
          | some (c2, o2, r2) =>
              if fitsT (ety e) ∧ fitsT (ety (Expr.widen h1 h2 e)) then some (c ++ c2, o2, r2) else none
          | none => none
      | none => none
  | _, _, _, .add a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) =>
              (binRest .add (ety (Expr.add a b)) (ety a) (ety b) oa ob r2).map fun x => (ca ++ cb ++ x.1, x.2.1, x.2.2)
          | none => none
      | none => none
  | _, _, _, .sub a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) =>
              (binRest .sub (ety (Expr.sub a b)) (ety a) (ety b) oa ob r2).map fun x => (ca ++ cb ++ x.1, x.2.1, x.2.2)
          | none => none
      | none => none
  | _, _, _, .mul a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) =>
              (binRest .mul (ety (Expr.mul a b)) (ety a) (ety b) oa ob r2).map fun x => (ca ++ cb ++ x.1, x.2.1, x.2.2)
          | none => none
      | none => none
  | _, _, _, .neg a, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match binRest .sub (ety (Expr.neg a)) (.int 0 0) (ety a) (.int (twid (.int 0 0)) 0) oa r1 with
          | some (c, o, r2) => some (ca ++ c, o, r2)
          | none => none
      | none => none
  | _, _, _, .div h0 h1 a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) =>
              (divRest .udiv (ety (Expr.div h0 h1 a b)) (ety a) (ety b) oa ob r2).map fun x =>
                (ca ++ cb ++ x.1, x.2.1, x.2.2)
          | none => none
      | none => none
  | _, _, _, .rem h0 h1 a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) =>
              (divRest .urem (ety (Expr.rem h0 h1 a b)) (ety a) (ety b) oa ob r2).map fun x =>
                (ca ++ cb ++ x.1, x.2.1, x.2.2)
          | none => none
      | none => none
  | _, _, _, .lt a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) =>
              (cmpRest .ult .slt (ety a) (ety b) oa ob r2).map fun x => (ca ++ cb ++ x.1, x.2.1, x.2.2)
          | none => none
      | none => none
  | _, _, _, .le a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) =>
              (cmpRest .ule .sle (ety a) (ety b) oa ob r2).map fun x => (ca ++ cb ++ x.1, x.2.1, x.2.2)
          | none => none
      | none => none
  | _, _, _, .eq a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) =>
              (cmpRest .eq .eq (ety a) (ety b) oa ob r2).map fun x => (ca ++ cb ++ x.1, x.2.1, x.2.2)
          | none => none
      | none => none
  | _, _, _, .and a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) => some (ca ++ cb ++ [.bin r2 .and 1 oa ob], .reg r2, r2 + 1)
          | none => none
      | none => none
  | _, _, _, .or a b, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) =>
          match lowerE lay cenv b r1 with
          | some (cb, ob, r2) => some (ca ++ cb ++ [.bin r2 .or 1 oa ob], .reg r2, r2 + 1)
          | none => none
      | none => none
  | _, _, _, .not a, r =>
      match lowerE lay cenv a r with
      | some (ca, oa, r1) => some (ca ++ [.bin r1 .xor 1 oa (.int 1 1)], .reg r1, r1 + 1)
      | none => none
  -- `opt n`: the integer `-1` for absent, the index otherwise (`encR`)
  | _, _, _, .none n, r =>
      if Ar.Fits (-1) (n - 1) 128 then some ([], .int (Ar.wid (-1) (n - 1)) (-1), r) else none
  | _, _, _, .some (n := n) e, r =>
      match lowerE lay cenv e r with
      | some (ca, oa, r1) =>
          if Ar.Fits (-1) (n - 1) 128 ∧ Ar.Fits 0 (n - 1) 128 then
            (cvtG (.int 0 (n - 1)) (.int (-1) (n - 1)) oa r1).map fun x => (ca ++ x.1, x.2.1, x.2.2)
          else none
      | none => none
  | _, _, _, .istSome (n := n) e, r =>
      match lowerE lay cenv e r with
      | some (ca, oa, r1) =>
          if Ar.Fits (-1) (n - 1) 128 then
            some (ca ++ [.icmp r1 .sge (Ar.wid (-1) (n - 1)) oa (.int (Ar.wid (-1) (n - 1)) 0)],
              .reg r1, r1 + 1)
          else none
      | none => none
  | _, _, _, .why n i, r =>
      if Ar.Fits 0 ((n : Int) - 1) 128 then some ([], .int (Ar.wid 0 ((n : Int) - 1)) (i.val : Int), r)
      else none
  | _, _, _, _, _ => none

/-- The lowering of the arguments of a call: the code, the operands that hold the values (their
    register images, in order), and the next free register. -/
def lowerArgs (lay : Layout D) (cenv : List Reg) :
    {Γ : Ctx} → {Λ : List (Gabbro.Grammatik.Res D)} → {τs : List GTy} → Gabbro.Grammatik.Args D Γ Λ τs →
      Nat → Option (List Instr × List Opd × Nat)
  | _, _, _, .nil, r => some ([], [], r)
  | _, _, _, .cons e rest, r =>
      match lowerE lay cenv e r with
      | some (ce, oe, r1) =>
          match lowerArgs lay cenv rest r1 with
          | some (cr, os, r2) => some (ce ++ cr, oe :: os, r2)
          | none => none
      | none => none

end Gabbro.Code.Lower
