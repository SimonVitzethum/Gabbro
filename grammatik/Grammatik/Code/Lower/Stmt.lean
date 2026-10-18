import Grammatik.Code.Lower.Expr

/-
  File:      Grammatik/Code/Lower/Stmt.lean
  Subject:   TRACK L, PHASE L1 -- THE LOWERING OF STATEMENTS, BLOCKS AND END BLOCKS, as Lean
             functions to IR basic blocks.

  `lowerS lay cenv lv s lb k st` lowers statement `s` to IR blocks that start at label `lb` and,
  when `s` completes normally, jump to label `k`; `st` carries the next free register and the next
  free label (both numbered in program order); the result is the list of new blocks and the new
  state. `lowerB` does the same for a `Block` (`nil` is a block that just jumps on), `lowerEnd`
  for an end block, which never falls through: every path ends in `ret`.

  THE FRAGMENT: assignments to table slots (also through a pointer), globals and local
  variables; `if`/`else`; `return`; `let` (an `alloc` cell plus its first store); `check` (a
  failed condition runs the `else` end block). Every other form lowers to `none`
  (a form with no `Code` lowering is refused by name). A variable is a stack cell whose register is
  `cenv[i]`; a `bool` is a byte in memory (`cvtM`).
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr)

variable {D : Deklaration}

/-- Next free register and next free label. -/
structure St where
  r : Nat
  l : Nat

/-- A value of G type `τ` from its register image to its memory image. -/
def cvtM (τ : GTy) (o : Opd) (r : Nat) : Option LR :=
  match τ with
  | .bool => some ([.cast r .zext (.int 1) (.int 8) o], .reg r, r + 1)
  | .int lo hi => if Ar.Fits lo hi 128 then some ([], o, r) else none
  | .ptr _ _ => some ([], o, r)
  | _ => none

/-- `store` of a value (already in its memory image) to a pointer operand. -/
def storeI (τ : GTy) (v p : Opd) : Instr := .store (memTy τ) v p

/-- The code that evaluates, converts and stores `e` at the address operand `p`. -/
def storeTo (τ : GTy) (oe : Opd) (r1 : Nat) (p : Opd) : Option (List Instr × Nat) :=
  match cvtM τ oe r1 with
  | some (cm, om, r2) => some (cm ++ [storeI τ om p], r2)
  | none => none

/-- A new local: allocate its cell, store the first value. Returns the code, the cell's register
    and the next free register. -/
def bindCode (τ : GTy) (oe : Opd) (r1 : Nat) : Option (List Instr × Nat × Nat) :=
  match cvtM τ oe r1 with
  | some (cm, om, r2) =>
      if supp τ then
        some (cm ++ [.alloc r2 (memTy τ), storeI τ om (.reg r2)], r2, r2 + 1)
      else none
  | none => none

/-- `return` of an optional value. -/
def lowerErg (lay : Layout D) (cenv : List Reg) :
    {Γ : Ctx} → {Λ : List (Res D)} → {eo : Option GTy} → ErgExpr D Γ Λ eo → Lbl → St →
      Option (List Block × St)
  | _, _, _, .empty, lb, s => some ([⟨lb, [], [], .ret none⟩], s)
  | _, _, _, .val e, lb, s =>
      match lowerE lay cenv e s.r with
      | some (ce, oe, r1) => some ([⟨lb, [], ce, .ret (some oe)⟩], { s with r := r1 })
      | none => none

variable {V : Vertrag D}

mutual

def lowerS (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Gabbro.Grammatik.Stmt D V l Γ Λ Λ' →
      Lbl → Lbl → St → Option (List Block × St)
  | _, _, _, _, .assignSlot t f i e _ _, lb, k, s =>
      if supp (D.typ t f) then
        match lowerE lay cenv i s.r with
        | some (ci, oi, r1) =>
            match lowerE lay cenv e r1 with
            | some (ce, oe, r2) =>
                match slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r2 with
                | some (ca, oa, r3) =>
                    match storeTo (D.typ t f) oe r3 oa with
                    | some (cs, r4) =>
                        some ([⟨lb, [], ci ++ ce ++ ca ++ cs, .jmp k⟩], { s with r := r4 })
                    | none => none
                | none => none
            | none => none
        | none => none
      else none
  | _, _, _, _, .assignThru p t _ f i e _ _, lb, k, s =>
      if supp (D.typ t f) then
        match lowerE lay cenv p s.r with
        | some (cp, op, r1) =>
            match lowerE lay cenv i r1 with
            | some (ci, oi, r2) =>
                match lowerE lay cenv e r2 with
                | some (ce, oe, r3) =>
                    match slotAddr lay t f op (.int 0 (D.count t - 1)) oi r3 with
                    | some (ca, oa, r4) =>
                        match storeTo (D.typ t f) oe r4 oa with
                        | some (cs, r5) =>
                            some ([⟨lb, [], cp ++ ci ++ ce ++ ca ++ cs, .jmp k⟩], { s with r := r5 })
                        | none => none
                    | none => none
                | none => none
            | none => none
        | none => none
      else none
  | _, _, _, _, .assignGlob g e _ _, lb, k, s =>
      if supp (D.gtyp g) then
        match lowerE lay cenv e s.r with
        | some (ce, oe, r1) =>
            match storeTo (D.gtyp g) oe r1 (.glob (lay.ggblk g)) with
            | some (cs, r2) => some ([⟨lb, [], ce ++ cs, .jmp k⟩], { s with r := r2 })
            | none => none
        | none => none
      else none
  | _, _, _, _, Gabbro.Grammatik.Stmt.assignVar (τ := τ) x e, lb, k, s =>
      match cenv[varIdx x]? with
      | some a =>
          if supp τ then
            match lowerE lay cenv e s.r with
            | some (ce, oe, r1) =>
                match storeTo τ oe r1 (.reg a) with
                | some (cs, r2) => some ([⟨lb, [], ce ++ cs, .jmp k⟩], { s with r := r2 })
                | none => none
            | none => none
          else none
      | none => none
  | _, _, _, _, .ite c tb eb, lb, k, s =>
      match lowerE lay cenv c s.r with
      | some (cc, oc, r1) =>
          match lowerB lay cenv lv tb s.l k ⟨r1, s.l + 2⟩ with
          | some (bt, s1) =>
              match lowerB lay cenv lv eb (s.l + 1) k s1 with
              | some (be, s2) => some (⟨lb, [], cc, .br oc s.l (s.l + 1)⟩ :: (bt ++ be), s2)
              | none => none
          | none => none
      | none => none
  | _, _, _, _, .ret e _, lb, k, s => lowerErg lay cenv e lb s
  | _, _, _, _, .leave _, lb, _, s => some ([⟨lb, [], [], .jmp lv.1⟩], s)
  | _, _, _, _, .next _, lb, _, s => some ([⟨lb, [], [], .jmp lv.2⟩], s)
  | _, _, _, _, .forever _ _ body, lb, k, s => lowerB lay cenv (k, lb) body lb lb s
  | _, _, _, _, .traverse t _ body, lb, k, s =>
      -- a counter register `s.r` counts the passes; the loop variable is a cell made per pass
      if 0 ≤ D.count t ∧ Ar.Fits 0 (D.count t) 128 then
        match cvtG (.int 0 (D.count t)) (.int 0 (D.count t - 1)) (.reg s.r) (s.r + 1) with
        | some (cv, ov, r1) =>
            match bindCode (.int 0 (D.count t - 1)) ov r1 with
            | some (cb, a, r2) =>
                match lowerB lay (a :: cenv) (k, s.l + 2) body (s.l + 3) (s.l + 2) ⟨r2, s.l + 4⟩ with
                | some (bb, s1) =>
                    some (⟨lb, [], [.bin s.r .add (Ar.wid 0 (D.count t)) (.int (Ar.wid 0 (D.count t)) 0)
                            (.int (Ar.wid 0 (D.count t)) 0)], .jmp s.l⟩ ::
                          ⟨s.l, [], [], .brc .ult (Ar.wid 0 (D.count t)) (.reg s.r)
                            (.int (Ar.wid 0 (D.count t)) (D.count t)) (s.l + 1) k⟩ ::
                          ⟨s.l + 1, [], cv ++ cb, .jmp (s.l + 3)⟩ ::
                          ⟨s.l + 2, [], [.bin s.r .add (Ar.wid 0 (D.count t)) (.reg s.r)
                            (.int (Ar.wid 0 (D.count t)) 1)], .jmp s.l⟩ :: bb, s1)
                | none => none
            | none => none
        | none => none
      else none
  | _, _, _, _, _, _, _, _ => none

def lowerB (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Gabbro.Grammatik.Block D V l Γ Λ Λ' →
      Lbl → Lbl → St → Option (List Block × St)
  | _, _, _, _, .nil, lb, k, s => some ([⟨lb, [], [], .jmp k⟩], s)
  | _, _, _, _, .cons st rest, lb, k, s =>
      match lowerS lay cenv lv st lb s.l ⟨s.r, s.l + 1⟩ with
      | some (b1, s1) =>
          match lowerB lay cenv lv rest s.l k s1 with
          | some (b2, s2) => some (b1 ++ b2, s2)
          | none => none
      | none => none
  | _, _, _, _, Gabbro.Grammatik.Block.bind (τ := τ) e rest, lb, k, s =>
      match lowerE lay cenv e s.r with
      | some (ce, oe, r1) =>
          match bindCode τ oe r1 with
          | some (cb, a, r2) =>
              match lowerB lay (a :: cenv) lv rest s.l k ⟨r2, s.l + 1⟩ with
              | some (b2, s2) => some (⟨lb, [], ce ++ cb, .jmp s.l⟩ :: b2, s2)
              | none => none
          | none => none
      | none => none
  | _, _, _, _, Gabbro.Grammatik.Block.narrow (lo := lo) (hi := hi) e lo' hi' sonst rest, lb, k, s =>
      match lowerE lay cenv (Expr.and (Expr.le (Expr.lit lo') e) (Expr.le e (Expr.lit hi'))) s.r with
      | some (cc, oc, r1) =>
          match lowerE lay cenv e r1 with
          | some (ce, oe, r2) =>
              match cvtG (.int lo hi) (.int lo' hi') oe r2 with
              | some (cv, ov, r3) =>
                  match bindCode (.int lo' hi') ov r3 with
                  | some (cb, a, r4) =>
                      match lowerEnd lay cenv lv sonst s.l ⟨r4, s.l + 3⟩ with
                      | some (be, s1) =>
                          match lowerB lay (a :: cenv) lv rest (s.l + 2) k s1 with
                          | some (br, s2) =>
                              some (⟨lb, [], cc, .br oc (s.l + 1) s.l⟩ ::
                                ⟨s.l + 1, [], ce ++ cv ++ cb, .jmp (s.l + 2)⟩ :: (be ++ br), s2)
                          | none => none
                      | none => none
                  | none => none
              | none => none
          | none => none
      | none => none
  | _, _, _, _, .check c sonst rest, lb, k, s =>
      match lowerE lay cenv c s.r with
      | some (cc, oc, r1) =>
          match lowerEnd lay cenv lv sonst s.l ⟨r1, s.l + 2⟩ with
          | some (be, s1) =>
              match lowerB lay cenv lv rest (s.l + 1) k s1 with
              | some (br, s2) => some (⟨lb, [], cc, .br oc (s.l + 1) s.l⟩ :: (be ++ br), s2)
              | none => none
          | none => none
      | none => none
  | _, _, _, _, _, _, _, _ => none

def lowerEnd (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Gabbro.Grammatik.Endblock D V l Γ Λ →
      Lbl → St → Option (List Block × St)
  | _, _, _, .ret e _, lb, s => lowerErg lay cenv e lb s
  | _, _, _, .leave _, lb, s => some ([⟨lb, [], [], .jmp lv.1⟩], s)
  | _, _, _, .next _, lb, s => some ([⟨lb, [], [], .jmp lv.2⟩], s)
  | _, _, _, .cons st rest, lb, s =>
      match lowerS lay cenv lv st lb s.l ⟨s.r, s.l + 1⟩ with
      | some (b1, s1) =>
          match lowerEnd lay cenv lv rest s.l s1 with
          | some (b2, s2) => some (b1 ++ b2, s2)
          | none => none
      | none => none
  | _, _, _, Gabbro.Grammatik.Endblock.bind (τ := τ) e rest, lb, s =>
      match lowerE lay cenv e s.r with
      | some (ce, oe, r1) =>
          match bindCode τ oe r1 with
          | some (cb, a, r2) =>
              match lowerEnd lay (a :: cenv) lv rest s.l ⟨r2, s.l + 1⟩ with
              | some (b2, s2) => some (⟨lb, [], ce ++ cb, .jmp s.l⟩ :: b2, s2)
              | none => none
          | none => none
      | none => none
  | _, _, _, _, _, _ => none

end

end Gabbro.Code.Lower
