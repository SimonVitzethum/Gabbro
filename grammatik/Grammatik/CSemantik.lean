/-
  File:      Grammatik/CSemantik.lean
  Subject:   A formal semantics for five emitted C forms (measurement lane).

  The emitter writes a C subset (census: 64 forms, `zaehle-c-formen.py`;
  allowed/never lists and UB inventory in `BEWEIS.md` section 1a/2).
  No formal semantics of that subset exists; emitter correctness cannot
  even be stated without one. This file MEASURES the cost on the five
  most-used forms before the full semantics is planned:

    A  `uint32_t` arithmetic with explicit width (binary + - * / % ops)
    B  array indexing with a checked index (`t->slots[i]`)
    C  assignment to a struct field of a table slot (`t->slots[i].f = v;`)
    D  `if` / `else`
    E  the admitted counting `for` (`for (uint32_t x = lo; x < hi; x++)`)

  Memory model: objects are maps from (table, index, field) to machine
  integers of the declared width -- the same shape as Gabbro's `Speicher`,
  so correspondence is direct. Each C undefined / implementation-defined
  behaviour the five forms can trigger is an INVENTORIED predicate, and
  the semantics gets STUCK (returns `none`) there -- so "no UB" is
  "the semantics makes progress".
-/
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-! ## 0. Widths and ranges: the integer types the five forms need -/

/-- The integer widths the emitter uses (`uint{8,16,32,64}_t`,
    `int{8,16,32,64}_t`; `BEWEIS.md` section 1a type row). -/
inductive CWidth where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr

/-- Bits per width. -/
def CWidth.bits : CWidth → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- Lower bound of the range: `0` unsigned, `-2^(w-1)` signed. -/
def cLo (sgn : Bool) (w : CWidth) : Int :=
  if sgn then -(2 ^ (w.bits - 1) : Int) else 0

/-- Upper bound of the range: `2^w - 1` unsigned, `2^(w-1) - 1` signed. -/
def cHi (sgn : Bool) (w : CWidth) : Int :=
  if sgn then (2 ^ (w.bits - 1) : Int) - 1 else (2 ^ w.bits : Int) - 1

/-! ## Infra. C memory over the same shape as Gabbro's `Speicher` -/

/-- C memory: (table, index, field) to machine integer. The same shape as
    Gabbro's `Speicher` (`Maschine.lean`), so correspondence is direct. -/
def CMem := Nat → Nat → Nat → Int

/-- C local environment: variable to machine integer
    (parameters, loop counters, locals). -/
def CEnv := Nat → Int

/-- Geometry: slots per table, for the checked index (form B). -/
def CGeom := Nat → Nat

/-! ## Form A. `uint32_t` arithmetic with explicit width -/

/-- The binary operators the emitter uses (`BEWEIS.md` section 1a
    expression row: `+ - * / % & | ^ << >>`). -/
inductive CBinOp where
  | add | sub | mul | div | mod | band | bor | bxor | shl | shr
  deriving DecidableEq, Repr

/-- C expressions for the five forms: literals, variables, width-tagged
    binary operators, and table-slot reads `t.slots[i].f`. -/
inductive CExpr where
  | lit (v : Int)
  | var (x : Nat)
  | bin (op : CBinOp) (sgn : Bool) (w : CWidth) (l r : CExpr)
  | slot (t : Nat) (i : CExpr) (f : Nat)
  deriving DecidableEq, Repr

/-- Unsigned wraparound: reduction modulo `2^w` into `0 .. 2^w - 1`. -/
def cWrap (w : CWidth) (v : Int) : Int :=
  let m : Int := 2 ^ w.bits
  ((v % m) + m) % m

/-- Apply a binary operator: `none` is STUCK (undefined behaviour).
    Unsigned arithmetic wraps (C11 6.2.5p9: defined); signed overflow,
    division by zero, `INT_MIN / -1`, shifts by a width or more, shifts
    of negative signed values, and signed bitwise operators are stuck
    (C11 6.5p5, 6.5.7p3-4, J.2: undefined or implementation-defined). -/
def cBinApply : CBinOp → Bool → CWidth → Int → Int → Option Int
  | .add, false, w, a, b => some (cWrap w (a + b))
  | .add, true, w, a, b =>
      if cLo true w ≤ a + b ∧ a + b ≤ cHi true w then some (a + b) else none
  | .sub, false, w, a, b => some (cWrap w (a - b))
  | .sub, true, w, a, b =>
      if cLo true w ≤ a - b ∧ a - b ≤ cHi true w then some (a - b) else none
  | .mul, false, w, a, b => some (cWrap w (a * b))
  | .mul, true, w, a, b =>
      if cLo true w ≤ a * b ∧ a * b ≤ cHi true w then some (a * b) else none
  | .div, false, w, a, b =>
      if cWrap w b = 0 then none else some ((cWrap w a) / (cWrap w b))
  | .div, true, w, a, b =>
      if b = 0 then none
      else if a = cLo true w ∧ b = -1 then none
      else if cLo true w ≤ a / b ∧ a / b ≤ cHi true w then some (a / b) else none
  | .mod, false, w, a, b =>
      if cWrap w b = 0 then none else some ((cWrap w a) % (cWrap w b))
  | .mod, true, _, a, b => if b = 0 then none else some (a % b)
  | .band, false, w, a, b =>
      some (((cWrap w a).toNat.land (cWrap w b).toNat : Nat) : Int)
  | .band, true, _, _, _ => none
  | .bor, false, w, a, b =>
      some (((cWrap w a).toNat.lor (cWrap w b).toNat : Nat) : Int)
  | .bor, true, _, _, _ => none
  | .bxor, false, w, a, b =>
      some (((cWrap w a).toNat.xor (cWrap w b).toNat : Nat) : Int)
  | .bxor, true, _, _, _ => none
  | .shl, false, w, a, b =>
      if 0 ≤ b ∧ b < (w.bits : Int) then
        some (cWrap w ((cWrap w a) * (2 : Int) ^ b.toNat)) else none
  | .shl, true, w, a, b =>
      if 0 ≤ b ∧ b < (w.bits : Int) then
        if a < 0 then none
        else if cLo true w ≤ a * (2 : Int) ^ b.toNat ∧
            a * (2 : Int) ^ b.toNat ≤ cHi true w
          then some (a * (2 : Int) ^ b.toNat) else none
      else none
  | .shr, false, w, a, b =>
      if 0 ≤ b ∧ b < (w.bits : Int) then
        some ((cWrap w a) / (2 : Int) ^ b.toNat) else none
  | .shr, true, w, a, b =>
      if 0 ≤ b ∧ b < (w.bits : Int) then
        if a < 0 then none else some (a / (2 : Int) ^ b.toNat)
      else none

/-- Expression evaluation: `none` is STUCK. Slot reads check the index
    against the geometry (form B); operator UB is `cBinApply` (form A). -/
def aEval : CExpr → CMem → CEnv → CGeom → Option Int
  | .lit v, _, _, _ => some v
  | .var x, _, ρ, _ => some (ρ x)
  | .bin op sgn w l r, m, ρ, g =>
      match aEval l m ρ g, aEval r m ρ g with
      | some a, some b => cBinApply op sgn w a b
      | _, _ => none
  | .slot t i f, m, ρ, g =>
      match aEval i m ρ g with
      | some k =>
          if 0 ≤ k ∧ k < (g t : Int) then some (m t k.toNat f) else none
      | none => none

/-! ## Form A, UB inventory: each undefined behaviour as a predicate -/

/-- Value-level UB of one operator application: the inventory for form A.
    Each constructor names one C11 undefined / implementation-defined case:
    zero divisor, `INT_MIN / -1`, signed overflow of `+ - *`, shift count
    outside `0 ..< width`, shift of a negative signed value, and signed
    bitwise operators. -/
inductive ABinUB : CBinOp → Bool → CWidth → Int → Int → Prop where
  | divZeroU (w a b) (h : cWrap w b = 0) : ABinUB .div false w a b
  | divZeroS (w a b) (h : b = 0) : ABinUB .div true w a b
  | modZeroU (w a b) (h : cWrap w b = 0) : ABinUB .mod false w a b
  | modZeroS (w a b) (h : b = 0) : ABinUB .mod true w a b
  | minDiv (w a b) (ha : a = cLo true w) (hb : b = -1) :
      ABinUB .div true w a b
  | ovAdd (w a b) (h : a + b < cLo true w ∨ cHi true w < a + b) :
      ABinUB .add true w a b
  | ovSub (w a b) (h : a - b < cLo true w ∨ cHi true w < a - b) :
      ABinUB .sub true w a b
  | ovMul (w a b) (h : a * b < cLo true w ∨ cHi true w < a * b) :
      ABinUB .mul true w a b
  | shiftBig (op sgn w a b) (hop : op = .shl ∨ op = .shr)
      (h : b < 0 ∨ (w.bits : Int) ≤ b) : ABinUB op sgn w a b
  | shlNeg (w a b) (h : a < 0) : ABinUB .shl true w a b
  | shrNeg (w a b) (h : a < 0) : ABinUB .shr true w a b
  | bitSigned (op w a b)
      (hop : op = .band ∨ op = .bor ∨ op = .bxor) : ABinUB op true w a b

/-- Every inventoried operator UB gets the semantics stuck. -/
theorem aBinUB_stuck : ∀ (op : CBinOp) (sgn : Bool) (w : CWidth) (a b : Int),
    ABinUB op sgn w a b → cBinApply op sgn w a b = none := by
  intro op sgn w a b h
  cases h with
  | divZeroU _ _ _ h => simp only [cBinApply]; rw [if_pos h]
  | divZeroS _ _ _ h => simp only [cBinApply]; rw [if_pos h]
  | modZeroU _ _ _ h => simp only [cBinApply]; rw [if_pos h]
  | modZeroS _ _ _ h => simp only [cBinApply]; rw [if_pos h]
  | minDiv _ _ _ ha hb =>
      simp only [cBinApply]; rw [if_neg (by omega), if_pos ⟨ha, hb⟩]
  | ovAdd _ _ _ h => simp only [cBinApply]; exact if_neg (by omega)
  | ovSub _ _ _ h => simp only [cBinApply]; exact if_neg (by omega)
  | ovMul _ _ _ h => simp only [cBinApply]; exact if_neg (by omega)
  | shiftBig _ _ _ _ _ hop h =>
      cases hop <;> subst_vars <;> cases sgn <;>
        simp only [cBinApply] <;> exact if_neg (by omega)
  | shlNeg _ _ _ h =>
      simp only [cBinApply]
      by_cases hc : 0 ≤ b ∧ b < (w.bits : Int)
      · rw [if_pos hc, if_pos h]
      · rw [if_neg hc]
  | shrNeg _ _ _ h =>
      simp only [cBinApply]
      by_cases hc : 0 ≤ b ∧ b < (w.bits : Int)
      · rw [if_pos hc, if_pos h]
      · rw [if_neg hc]
  | bitSigned _ _ _ _ hop =>
      rcases hop with _|_|_ <;> subst_vars <;> simp only [cBinApply]
