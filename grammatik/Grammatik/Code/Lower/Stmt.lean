import Grammatik.Code.Lower.Expr
import Grammatik.Code.Lower.Fail

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
  variables; `if`/`else`; `return`; `let` (an `alloc` cell plus its first store); `check` and
  `narrow` (a failed condition runs the `else` end block); `leave`/`next` (a jump to the loop's
  targets `lv`); the loops `forever`, `traverse` (a counter register) and `retry` (a counter
  register, the test first, an overflow block); the calls `f(..)` and `let x = f(..)` (the result
  goes to a fresh register and then to a cell). Every other form lowers to `none` (a form with no
  `Code` lowering is refused by name). A variable is a stack cell whose register is `cenv[i]`;
  a `bool` is a byte in memory (`cvtM`).
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
  | .opt n => if Ar.Fits (-1) (n - 1) 128 then some ([], o, r) else none
  | .why n => if Ar.Fits 0 ((n : Int) - 1) 128 then some ([], o, r) else none
  | .sum cs => if Ar.Fits 0 (sumTop cs) 128 then some ([], o, r) else none
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

/-- The pass counter of a `retry` of `n` passes fits the widths the lowering knows (a `Bool` test:
    `n ≤ 2 ^ 62`, see `retryOk_fits`; it is a test the unifier can evaluate on a variable without
    unrolling a huge numeral, which a test of `Ar.Fits` is not). -/
def retryOk (n : Nat) : Bool := Nat.ble n (2 ^ 62)

theorem retryOk_fits {n : Nat} (h : retryOk n = true) : Ar.Fits 0 (n : Int) 128 := by
  unfold retryOk at h
  have hn := Nat.le_of_ble_eq_true h
  unfold Ar.Fits
  simp only [Int.le_refl, if_true]
  have h1 : ((n : Nat) : Int) ≤ 2 ^ 62 := by exact_mod_cast hn
  omega

/-- The payload of an arm of a `match` on a tagged value, as the integer of its own range: from the
    scrutinee's word `ov` (`W` bits, below `top`) the quotient by the number of cases `L` (an unsigned
    division by a constant above zero), plus the low bound of the payload (modulo `2^w`), then the
    result moved to the width of its own range. The three steps run at the width of the range
    `min 0 lo .. max top hi`, which holds the word, the quotient and the payload alike. -/
def payCode (top : Int) (W L : Nat) (lo hi : Int) (ov : Opd) (r : Nat) : Option LR :=
  if Ar.Fits (min 0 lo) (max top hi) 128 then
    match cvt W (Ar.wid (min 0 lo) (max top hi)) false ov r with
    | (c1, o1, r1) =>
        match cvtG (.int (min 0 lo) (max top hi)) (.int lo hi) (.reg (r1 + 1)) (r1 + 2) with
        | some (c3, o3, r3) =>
            some (c1 ++ [.bin r1 .udiv (Ar.wid (min 0 lo) (max top hi)) o1
                    (.int (Ar.wid (min 0 lo) (max top hi)) (L : Int)),
                  .bin (r1 + 1) .add (Ar.wid (min 0 lo) (max top hi)) (.reg r1)
                    (.int (Ar.wid (min 0 lo) (max top hi)) lo)] ++ c3, o3, r3)
        | none => none
  else none

/-- `return` of an optional value. -/
def lowerErg (lay : Layout D) (cenv : List Reg) :
    {Γ : Ctx} → {Λ : List (Res D)} → {eo : Option GTy} → ErgExpr D Γ Λ eo → Lbl → St →
      Option (List Block × St)
  | _, _, _, .empty, lb, s => some ([⟨lb, [], [], .ret none⟩], s)
  | _, _, _, .val e, lb, s =>
      match lowerE lay cenv e s.r with
      | some (ce, oe, r1) => some ([⟨lb, [], ce, .ret (some oe)⟩], { s with r := r1 })
      | none => none

/-- `return` of a function with `n > 0` reasons: the answer word (`Lower/Fail.lean`): a value is
    `(n + 1) * (v - lo)` (the payload packing with case number `0`), no value is `0`. -/
def lowerErgF (lay : Layout D) (cenv : List Reg) (n : Nat) :
    {Γ : Ctx} → {Λ : List (Res D)} → {eo : Option GTy} → ErgExpr D Γ Λ eo → Lbl → St →
      Option (List Block × St)
  | _, _, _, .empty, lb, s =>
      if failOk n none then some ([⟨lb, [], [], .ret (some (.int (retW n none) 0))⟩], s) else none
  | _, _, _, .val (τ := τ) e, lb, s =>
      match τ, e with
      | .int lo hi, e =>
          match lowerE lay cenv e s.r with
          | some (ce, oe, r1) =>
              if failOk n (some (.int lo hi)) then
                match numCode lo hi (retW n (some (.int lo hi))) (n + 1) 0 oe r1 with
                | (cn, on, r2) => some ([⟨lb, [], ce ++ cn, .ret (some on)⟩], { s with r := r2 })
              else none
          | none => none
      | _, _ => none

/-- `return` of a value, in a function with `n` reasons or none. -/
def lowerRet (lay : Layout D) (cenv : List Reg) (n : Nat) {Γ : Ctx} {Λ : List (Res D)} {eo : Option GTy}
    (e : ErgExpr D Γ Λ eo) (lb : Lbl) (s : St) : Option (List Block × St) :=
  if n = 0 then lowerErg lay cenv e lb s else lowerErgF lay cenv n e lb s

/-- `return why r`: the reason's word. -/
def lowerWhy (n : Nat) (eo : Option GTy) (r : Nat) (lb : Lbl) (s : St) : Option (List Block × St) :=
  if failOk n eo then some ([⟨lb, [], [], .ret (some (.int (retW n eo) ((r : Int) + 1)))⟩], s) else none

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
  | _, _, _, _, .onOption (n := n) o p a, lb, k, s =>
      -- the word is `-1` for absent: a signed compare with zero picks the arm; the index of the
      -- present arm is a new local (the word moved to the unsigned width of `0 .. n - 1`)
      match lowerE lay cenv o s.r with
      | some (co, oo, r1) =>
          if Ar.Fits (-1) (n - 1) 128 ∧ Ar.Fits 0 (n - 1) 128 then
            match cvtG (.int (-1) (n - 1)) (.int 0 (n - 1)) oo r1 with
            | some (cv, ov, r2) =>
                match bindCode (.int 0 (n - 1)) ov r2 with
                | some (cb, c, r3) =>
                    match lowerB lay cenv lv a s.l k ⟨r3, s.l + 3⟩ with
                    | some (ba, s1) =>
                        match lowerB lay (c :: cenv) lv p (s.l + 2) k s1 with
                        | some (bp, s2) =>
                            some (⟨lb, [], co, .brc .slt (Ar.wid (-1) (n - 1)) oo
                                    (.int (Ar.wid (-1) (n - 1)) 0) s.l (s.l + 1)⟩ ::
                                  ⟨s.l + 1, [], cv ++ cb, .jmp (s.l + 2)⟩ :: (ba ++ bp), s2)
                        | none => none
                    | none => none
                | none => none
            | none => none
          else none
      | none => none
  | _, _, _, _, .onWhy (n := n) r arms, lb, k, s =>
      -- a `switch` on the reason's number; the arms have the labels `s.l + 1 + i`, a block that is
      -- never entered (`dead`) answers the numbers `>= n`
      match lowerE lay cenv r s.r with
      | some (cr, orr, r1) =>
          if Ar.Fits 0 ((n : Int) - 1) 128 then
            match lowerGA lay cenv lv arms (s.l + 1) k ⟨r1, s.l + 1 + n⟩ with
            | some (ba, s1) =>
                some (⟨lb, [], cr, .sw (Ar.wid 0 ((n : Int) - 1)) orr s.l
                        ((List.range n).map fun (i : Nat) => ((i : Int), (s.l + 1 + i : Nat)))⟩ ::
                      ⟨s.l, [], [], .dead⟩ :: ba, s1)
            | none => none
          else none
      | none => none
  | _, _, _, _, .onTag (cs := cs) v arms, lb, k, s =>
      -- the case number is the word modulo `L`; a `switch` on it picks the arm, which takes its payload
      -- (the word divided by `L`) from the same word (`lowerAr`)
      match lowerE lay cenv v s.r with
      | some (cv, ov, r1) =>
          if Ar.Fits 0 (sumTop cs) 128 then
            match lowerAr lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov arms (s.l + 1) k
                ⟨r1 + 1, s.l + 1 + cs.length⟩ with
            | some (ba, s1) =>
                some (⟨lb, [], cv ++ [.bin r1 .urem (Ar.wid 0 (sumTop cs)) ov
                        (.int (Ar.wid 0 (sumTop cs)) (cs.length : Int))],
                      .sw (Ar.wid 0 (sumTop cs)) (.reg r1) s.l
                        ((List.range cs.length).map fun (i : Nat) => ((i : Int), (s.l + 1 + i : Nat)))⟩ ::
                      ⟨s.l, [], [], .dead⟩ :: ba, s1)
            | none => none
          else none
      | none => none
  | _, _, _, _, .ret e _, lb, k, s => lowerRet lay cenv V.gruende e lb s
  | _, _, _, _, .retWhy r _, lb, k, s => lowerWhy V.gruende V.erg r.val lb s
  | _, _, _, _, .leave _, lb, _, s => some ([⟨lb, [], [], .jmp lv.1⟩], s)
  | _, _, _, _, .next _, lb, _, s => some ([⟨lb, [], [], .jmp lv.2⟩], s)
  | _, _, _, _, .forever _ _ body, lb, k, s => lowerB lay cenv (k, lb) body lb lb s
  | _, _, _, _, .call f args _ _, lb, k, s =>
      match lowerArgs lay cenv args s.r with
      | some (ca, ops, r1) =>
          some ([⟨lb, [], ca ++ [.call none (lay.fno f) ops], .jmp k⟩], { s with r := r1 })
      | none => none
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
  | _, _, _, _, .retry n bis body ueb, lb, k, s =>
      -- a counter register `s.r` counts the passes made; the test of `bis` comes first in every pass
      if retryOk n = true then
        match lowerE lay cenv bis (s.r + 1) with
        | some (cb, ob, r1) =>
            match lowerB lay cenv (k, s.l + 3) body (s.l + 4) (s.l + 3) ⟨r1, s.l + 5⟩ with
            | some (bb, s1) =>
                match lowerB lay cenv lv ueb (s.l + 2) k s1 with
                | some (bo, s2) =>
                    some (⟨lb, [], [.bin s.r .add (Ar.wid 0 (n : Int)) (.int (Ar.wid 0 (n : Int)) 0)
                            (.int (Ar.wid 0 (n : Int)) 0)], .jmp s.l⟩ ::
                          ⟨s.l, [], cb, .br ob k (s.l + 1)⟩ ::
                          ⟨s.l + 1, [], [], .brc .ult (Ar.wid 0 (n : Int)) (.reg s.r)
                            (.int (Ar.wid 0 (n : Int)) (n : Int)) (s.l + 4) (s.l + 2)⟩ ::
                          ⟨s.l + 3, [], [.bin s.r .add (Ar.wid 0 (n : Int)) (.reg s.r)
                            (.int (Ar.wid 0 (n : Int)) 1)], .jmp s.l⟩ :: (bb ++ bo), s2)
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
  | _, _, _, _, Gabbro.Grammatik.Block.bindCall (τ := τ) f args _ _ _ rest, lb, k, s =>
      match lowerArgs lay cenv args s.r with
      | some (ca, ops, r1) =>
          match bindCode τ (.reg r1) (r1 + 1) with
          | some (cb, a, r2) =>
              match lowerB lay (a :: cenv) lv rest s.l k ⟨r2, s.l + 1⟩ with
              | some (b2, s2) =>
                  some (⟨lb, [], ca ++ [.call (some r1) (lay.fno f) ops] ++ cb, .jmp s.l⟩ :: b2, s2)
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

/-- The arms of a `match` on a reason: arm `i` is lowered at label `lb + i`, one after the other. -/
def lowerGA (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
      Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n → Lbl → Lbl → St → Option (List Block × St)
  | _, _, _, _, _, .nil, _, _, s => some ([], s)
  | _, _, _, _, _, .cons b rest, lb, k, s =>
      match lowerB lay cenv lv b lb k s with
      | some (b1, s1) =>
          match lowerGA lay cenv lv rest (lb + 1) k s1 with
          | some (b2, s2) => some (b1 ++ b2, s2)
          | none => none
      | none => none

/-- The arms of a `match` on a tagged value: arm `i` has entry label `lb + i`; an arm with a payload
    first computes it (`payCode`) and makes it a new local, then runs its body; an arm without one is
    just its body. -/
def lowerAr (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (top : Int) (W L : Nat) (ov : Opd) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {cs : List (Option (Int × Int))} →
      Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs → Lbl → Lbl → St → Option (List Block × St)
  | _, _, _, _, _, .nil, _, _, s => some ([], s)
  | _, _, _, _, _, .cons (c := c) b rest, lb, k, s =>
      match c, b with
      | none, b =>
          match lowerB lay cenv lv b lb k s with
          | some (b1, s1) =>
              match lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with
              | some (b2, s2) => some (b1 ++ b2, s2)
              | none => none
          | none => none
      | some (lo, hi), b =>
          match payCode top W L lo hi ov s.r with
          | some (cp, op, r1) =>
              match bindCode (.int lo hi) op r1 with
              | some (cb, a, r2) =>
                  match lowerB lay (a :: cenv) lv b s.l k ⟨r2, s.l + 1⟩ with
                  | some (bb, s1) =>
                      match lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with
                      | some (b2, s2) => some (⟨lb, [], cp ++ cb, .jmp s.l⟩ :: bb ++ b2, s2)
                      | none => none
                  | none => none
              | none => none
          | none => none

def lowerEnd (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Gabbro.Grammatik.Endblock D V l Γ Λ →
      Lbl → St → Option (List Block × St)
  | _, _, _, .ret e _, lb, s => lowerRet lay cenv V.gruende e lb s
  | _, _, _, .retWhy r _, lb, s => lowerWhy V.gruende V.erg r.val lb s
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
