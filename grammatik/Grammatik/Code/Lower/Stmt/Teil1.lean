module

public import Grammatik.Code.Lower.Expr
public import Grammatik.Code.Lower.Fail

@[expose] public section



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
  | .ptr _ => some ([], o, r)
  | .opt n => if Ar.Fits (-1) (n - 1) 128 then some ([], o, r) else none
  | .why n => if Ar.Fits 0 ((n : Int) - 1) 128 then some ([], o, r) else none
  | .sum cs => if supp (.sum cs) then some ([], o, r) else none
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

/-- **A call with a failure channel**, as a lowering with its two continuations given: the call, the case
    number (the answer word modulo `n + 1`), a branch to the value arm (case `0`: the word divided by
    `n + 1` plus `lo`, a new local, then `kRest`) or to the reason arm (the case number minus one, a new
    local, then `kErr`). Labels: `st.l` the value arm's entry, `st.l + 1` the reason arm's entry, `st.l + 2`
    and `st.l + 3` the continuations' entries; their counters start at `st.l + 4` and run on. -/
def lowerElse (lay : Layout D) (cenv : List Reg) (fno n : Nat) (τ : GTy) (ca : List Instr) (ops : List Opd)
    (r1 : Nat) (lb : Lbl) (s : St) (kRest : Reg → St → Option (List Block × St))
    (kErr : Reg → St → Option (List Block × St)) : Option (List Block × St) :=
  match τ with
  | .int lo hi =>
      if failOk n (some (.int lo hi)) ∧ Ar.Fits 0 ((n : Int) - 1) 128 then
        match payCode (failTop n (some (.int lo hi))) (retW n (some (.int lo hi))) (n + 1) lo hi (.reg r1) (r1 + 2) with
        | some (cp, op, r2) =>
            match bindCode (.int lo hi) op r2 with
            | some (cb, a, r3) =>
                match kRest a ⟨r3, s.l + 4⟩ with
                | some (bo, s1) =>
                    match cvt (retW n (some (.int lo hi))) (Ar.wid 0 ((n : Int) - 1)) false (.reg s1.r) (s1.r + 1) with
                    | (cv, ov, r4) =>
                        match bindCode (.why n) ov r4 with
                        | some (cb2, a2, r5) =>
                            match kErr a2 ⟨r5, s1.l⟩ with
                            | some (be, s2) =>
                                some (⟨lb, [], ca ++ [.call (some r1) fno ops,
                                        .bin (r1 + 1) .urem (retW n (some (.int lo hi))) (.reg r1)
                                          (.int (retW n (some (.int lo hi))) ((n + 1 : Nat) : Int))],
                                      .brc .eq (retW n (some (.int lo hi))) (.reg (r1 + 1))
                                        (.int (retW n (some (.int lo hi))) 0) s.l (s.l + 1)⟩ ::
                                      ⟨s.l, [], cp ++ cb, .jmp (s.l + 2)⟩ ::
                                      ⟨s.l + 1, [], .bin s1.r .sub (retW n (some (.int lo hi))) (.reg (r1 + 1))
                                          (.int (retW n (some (.int lo hi))) 1) :: (cv ++ cb2), .jmp (s.l + 3)⟩ ::
                                      (bo ++ be), s2)
                            | none => none
                        | none => none
                | none => none
            | none => none
        | none => none
      else none
  -- fallible indirect calls («C07») have no lowering yet: refused, never a fallback
  | _, _, _, _, .callIndElse .., _, _, _ => none
  | _ => none

variable {V : Vertrag D}

end Gabbro.Code.Lower
