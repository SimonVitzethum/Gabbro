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

/-! ## Form B. array indexing with a checked index -/

/-- Read one cell with its bound check: `none` is STUCK (out of bounds).
    The emitter's index is `uint32_t`; the check is against the declared
    slot count, the same number Gabbro's `.index` type carries. -/
def cIdxRead (m : CMem) (g : CGeom) (t : Nat) (k : Int) (f : Nat) : Option Int :=
  if 0 ≤ k ∧ k < (g t : Int) then some (m t k.toNat f) else none

/-- Index UB: below zero or past the declared slot count. -/
inductive IdxUB : CGeom → Nat → Int → Prop where
  | outLo (g t k) (h : k < 0) : IdxUB g t k
  | outHi (g t k) (h : (g t : Int) ≤ k) : IdxUB g t k

/-- An out-of-bounds index gets the read stuck. -/
theorem cIdxRead_stuck : ∀ (m : CMem) (g : CGeom) (t : Nat) (k : Int) (f : Nat),
    IdxUB g t k → cIdxRead m g t k f = none := by
  intro m g t k f h
  cases h
  case outLo => rename_i h'; simp only [cIdxRead]; exact if_neg (by omega)
  case outHi => rename_i h'; simp only [cIdxRead]; exact if_neg (by omega)

/-- An index that is not UB reads a value: bounds are progress. -/
theorem cIdxRead_progress : ∀ (m : CMem) (g : CGeom) (t : Nat) (k : Int) (f : Nat),
    ¬ IdxUB g t k → ∃ v, cIdxRead m g t k f = some v := by
  intro m g t k f h
  have h0 : 0 ≤ k := by
    cases Classical.em (0 ≤ k) with
    | inl hle => exact hle
    | inr hnle => exact (h (.outLo g t k (by omega))).elim
  have h1 : k < (g t : Int) := by
    cases Classical.em (k < (g t : Int)) with
    | inl hle => exact hle
    | inr hnle => exact (h (.outHi g t k (by omega))).elim
  exact ⟨m t k.toNat f, by simp only [cIdxRead]; rw [if_pos ⟨h0, h1⟩]⟩

/-- Expression-level UB: subexpression UB propagates, operator UB fires
    on evaluated operands, index UB fires on the evaluated index. -/
inductive CExprUB : CExpr → CMem → CEnv → CGeom → Prop where
  | binL (op sgn w l r m ρ g) (h : CExprUB l m ρ g) :
      CExprUB (.bin op sgn w l r) m ρ g
  | binR (op sgn w l r m ρ g a) (ha : aEval l m ρ g = some a)
      (h : CExprUB r m ρ g) : CExprUB (.bin op sgn w l r) m ρ g
  | binOp (op sgn w l r m ρ g a b) (ha : aEval l m ρ g = some a)
      (hb : aEval r m ρ g = some b) (h : ABinUB op sgn w a b) :
      CExprUB (.bin op sgn w l r) m ρ g
  | idxSub (t i f m ρ g) (h : CExprUB i m ρ g) : CExprUB (.slot t i f) m ρ g
  | idxOut (t i f m ρ g k) (hk : aEval i m ρ g = some k) (h : IdxUB g t k) :
      CExprUB (.slot t i f) m ρ g

/-- The "no UB" checker: true exactly when evaluation makes progress.
    Stated with `Option.isSome` for the operators so the checker and the
    semantics agree by construction. -/
def cBinOk (op : CBinOp) (sgn : Bool) (w : CWidth) (a b : Int) : Bool :=
  (cBinApply op sgn w a b).isSome

/-- The checker says yes exactly when the operator delivers a value. -/
theorem cBinOk_some : ∀ (op : CBinOp) (sgn : Bool) (w : CWidth) (a b : Int),
    cBinOk op sgn w a b = true → ∃ v, cBinApply op sgn w a b = some v := by
  intro op sgn w a b h
  unfold cBinOk at h
  cases hv : cBinApply op sgn w a b with
  | some v => exact ⟨v, rfl⟩
  | none => simp [hv] at h

/-- The checker says no exactly when the operator gets stuck. -/
theorem cBinOk_none : ∀ (op : CBinOp) (sgn : Bool) (w : CWidth) (a b : Int),
    cBinOk op sgn w a b = false → cBinApply op sgn w a b = none := by
  intro op sgn w a b h
  unfold cBinOk at h
  cases hv : cBinApply op sgn w a b with
  | some v => simp [hv] at h
  | none => rfl

/-- The expression checker: subexpressions clean and the firing
    rule applies. -/
def cOk : CExpr → CMem → CEnv → CGeom → Bool
  | .lit _, _, _, _ => true
  | .var _, _, _, _ => true
  | .bin op sgn w l r, m, ρ, g =>
      cOk l m ρ g && cOk r m ρ g &&
        match aEval l m ρ g, aEval r m ρ g with
        | some a, some b => cBinOk op sgn w a b
        | _, _ => false
  | .slot t i _, m, ρ, g =>
      cOk i m ρ g &&
        match aEval i m ρ g with
        | some k => if 0 ≤ k ∧ k < (g t : Int) then true else false
        | none => false

/-- Progress: a clean check evaluates to a value. -/
theorem cOk_progress : ∀ (e : CExpr) (m : CMem) (ρ : CEnv) (g : CGeom),
    cOk e m ρ g = true → ∃ v, aEval e m ρ g = some v := by
  intro e
  induction e with
  | lit v => intro m ρ g _; exact ⟨v, rfl⟩
  | var x => intro m ρ g _; exact ⟨ρ x, rfl⟩
  | bin op sgn w l r ihl ihr =>
      intro m ρ g h
      simp only [cOk] at h
      by_cases hl : cOk l m ρ g = true
      · by_cases hr : cOk r m ρ g = true
        · obtain ⟨a, ha⟩ := ihl m ρ g hl
          obtain ⟨b, hb⟩ := ihr m ρ g hr
          have hok' : cBinOk op sgn w a b = true := by
            rw [hl, hr, ha, hb] at h
            simpa using h
          obtain ⟨v, hv⟩ := cBinOk_some op sgn w a b hok'
          exact ⟨v, by simp only [aEval, ha, hb, hv]⟩
        · simp [hr] at h
      · simp [hl] at h
  | slot t i f ihi =>
      intro m ρ g h
      simp only [cOk] at h
      by_cases hi : cOk i m ρ g = true
      · obtain ⟨k, hk⟩ := ihi m ρ g hi
        have hb : 0 ≤ k ∧ k < (g t : Int) := by
          rw [hi, hk] at h
          cases Classical.em (0 ≤ k ∧ k < (g t : Int)) with
          | inl hP => exact hP
          | inr hnP => simp [hnP] at h
        exact ⟨m t k.toNat f, by simp only [aEval, hk]; rw [if_pos hb]⟩
      · simp [hi] at h

/-- A failed check is stuck: the contrapositive of progress. -/
theorem aEval_none_of_ok_false : ∀ (e : CExpr) (m : CMem) (ρ : CEnv) (g : CGeom),
    cOk e m ρ g = false → aEval e m ρ g = none := by
  intro e
  induction e with
  | lit v => intro m ρ g h; simp [cOk] at h
  | var x => intro m ρ g h; simp [cOk] at h
  | bin op sgn w l r ihl ihr =>
      intro m ρ g h
      simp only [cOk] at h
      by_cases hl : cOk l m ρ g = true
      · by_cases hr : cOk r m ρ g = true
        · obtain ⟨a, ha⟩ := cOk_progress l m ρ g hl
          obtain ⟨b, hb⟩ := cOk_progress r m ρ g hr
          have hok : cBinOk op sgn w a b = false := by
            rw [hl, hr, ha, hb] at h
            simpa using h
          have hn := cBinOk_none op sgn w a b hok
          simp only [aEval, ha, hb, hn]
        · have hr' : cOk r m ρ g = false := by simpa using hr
          have hbn := ihr m ρ g hr'
          simp [aEval, hbn]
      · have hl' : cOk l m ρ g = false := by simpa using hl
        have han := ihl m ρ g hl'
        simp [aEval, han]
  | slot t i f ihi =>
      intro m ρ g h
      simp only [cOk] at h
      by_cases hi : cOk i m ρ g = true
      · obtain ⟨k, hk⟩ := cOk_progress i m ρ g hi
        have hok : (if 0 ≤ k ∧ k < (g t : Int) then true else false) = false := by
          rw [hi, hk] at h
          simpa using h
        have hb : ¬ (0 ≤ k ∧ k < (g t : Int)) := by
          intro hP
          simp [hP] at hok
        simp only [aEval, hk]
        rw [if_neg hb]
      · have hi' : cOk i m ρ g = false := by simpa using hi
        have hn := ihi m ρ g hi'
        simp [aEval, hn]

/-- Every inventoried expression UB fails the checker. -/
theorem cExprUB_ok : ∀ (e : CExpr) (m : CMem) (ρ : CEnv) (g : CGeom),
    CExprUB e m ρ g → cOk e m ρ g = false := by
  intro e m ρ g h
  induction h
  case binL => rename_i ih; simp [cOk, ih]
  case binR => rename_i ih; simp [cOk, ih]
  case binOp =>
      rename_i ha hb h
      simp only [cOk, ha, hb, cBinOk]
      rw [aBinUB_stuck _ _ _ _ _ h]
      simp
  case idxSub => rename_i ih; simp [cOk, ih]
  case idxOut =>
      rename_i hk h
      simp only [cOk, hk]
      cases h
      case outLo => rename_i h'; rw [if_neg (by omega)]; simp
      case outHi => rename_i h'; rw [if_neg (by omega)]; simp

/-- Every inventoried expression UB gets the evaluation stuck. -/
theorem cExprUB_stuck : ∀ (e : CExpr) (m : CMem) (ρ : CEnv) (g : CGeom),
    CExprUB e m ρ g → aEval e m ρ g = none := by
  intro e m ρ g h
  exact aEval_none_of_ok_false e m ρ g (cExprUB_ok e m ρ g h)

/-! ## Form C. assignment to a struct field of a table slot -/

/-- C statements for the five forms: `skip`, the slot-field store
    `t->slots[i].f = e;` with the declared field type, sequencing,
    `if`/`else` on a nonzero test (form D), and the counting `for`
    `for (x = lo; x < hi; x++) body` (form E). -/
inductive CStmt where
  | skip
  | assign (t : Nat) (i : CExpr) (f : Nat) (sgn : Bool) (w : CWidth) (e : CExpr)
  | seq (a b : CStmt)
  | cif (c : CExpr) (t e : CStmt)
  | cfor (x : Nat) (lo hi : Int) (body : CStmt)
  deriving DecidableEq, Repr

/-- Update one variable: the loop counter write. -/
def cUpd (ρ : CEnv) (x : Nat) (v : Int) : CEnv :=
  fun y => if y = x then v else ρ y

/-- The counting loop with fuel: `none` is out of fuel (NOT UB -- the
    progress theorem assumes enough fuel). The counter ends at the exit
    value, as in C. `runBody` is the body executor. -/
def cForRun (runBody : CMem → CEnv → Nat → Option (CMem × CEnv)) (x : Nat)
    (cur hi : Int) (m : CMem) (ρ : CEnv) (fuel : Nat) : Option (CMem × CEnv) :=
  match fuel with
  | 0 => none
  | n + 1 =>
      if cur < hi then
        match runBody m (cUpd ρ x cur) n with
        | some (m', ρ') => cForRun runBody x (cur + 1) hi m' ρ' n
        | none => none
      else some (m, cUpd ρ x cur)

/-- Statement execution: `none` is STUCK (UB) or out of fuel. The store
    fires only when the index is in bounds AND the value fits the
    declared field type -- the emitter's range guarantee. -/
def cExec : CStmt → CMem → CEnv → CGeom → Nat → Option (CMem × CEnv)
  | .skip, m, ρ, _, _ => some (m, ρ)
  | .assign t i f sgn w e, m, ρ, g, _ =>
      match aEval i m ρ g, aEval e m ρ g with
      | some k, some v =>
          if 0 ≤ k ∧ k < (g t : Int) ∧ cLo sgn w ≤ v ∧ v ≤ cHi sgn w then
            some ((fun t' k' f' =>
              if t' = t ∧ k' = k.toNat ∧ f' = f then v else m t' k' f'), ρ)
          else none
      | _, _ => none
  | .seq a b, m, ρ, g, fuel =>
      match cExec a m ρ g fuel with
      | some (m', ρ') => cExec b m' ρ' g fuel
      | none => none
  | .cif c t e, m, ρ, g, fuel =>
      match aEval c m ρ g with
      | some v => if v ≠ 0 then cExec t m ρ g fuel else cExec e m ρ g fuel
      | none => none
  | .cfor x lo hi body, m, ρ, g, fuel =>
      cForRun (fun m ρ f => cExec body m ρ g f) x lo hi m ρ fuel

/-- Statement-level UB: subexpression UB, out-of-bounds store index,
    value outside the declared field type, first-iteration body UB.
    Later-iteration body UB is covered by the progress side (form E):
    the body must run from every reachable counter state. -/
inductive CStmtUB : CStmt → CMem → CEnv → CGeom → Prop where
  | assignIdx (t i f sgn w e m ρ g) (h : CExprUB i m ρ g) :
      CStmtUB (.assign t i f sgn w e) m ρ g
  | assignVal (t i f sgn w e m ρ g) (h : CExprUB e m ρ g) :
      CStmtUB (.assign t i f sgn w e) m ρ g
  | assignIdxOut (t i f sgn w e m ρ g k) (hk : aEval i m ρ g = some k)
      (h : IdxUB g t k) : CStmtUB (.assign t i f sgn w e) m ρ g
  | assignRange (t i f sgn w e m ρ g k v) (hk : aEval i m ρ g = some k)
      (hv : aEval e m ρ g = some v)
      (h : v < cLo sgn w ∨ cHi sgn w < v) :
      CStmtUB (.assign t i f sgn w e) m ρ g
  | seqL (a b m ρ g) (h : CStmtUB a m ρ g) : CStmtUB (.seq a b) m ρ g
  | seqR (a b m ρ g)
      (h : ∀ fuel m' ρ', cExec a m ρ g fuel = some (m', ρ') →
        CStmtUB b m' ρ' g) : CStmtUB (.seq a b) m ρ g
  | ifCond (c t e m ρ g) (h : CExprUB c m ρ g) : CStmtUB (.cif c t e) m ρ g
  | forFirst (x lo hi body m ρ g) (hlt : lo < hi)
      (h : CStmtUB body m (cUpd ρ x lo) g) :
      CStmtUB (.cfor x lo hi body) m ρ g

/-- Every inventoried statement UB gets the execution stuck, at any fuel.
    Induction is over the STATEMENT (so both sequence parts and the loop
    body have hypotheses); the UB proof selects the firing case. -/
theorem cStmtUB_stuck : ∀ (s : CStmt) (m : CMem) (ρ : CEnv) (g : CGeom),
    CStmtUB s m ρ g → ∀ fuel, cExec s m ρ g fuel = none := by
  intro s
  induction s with
  | skip => intro m ρ g h fuel; cases h
  | assign t i f sgn w e =>
      intro m ρ g h fuel
      cases h
      case assignIdx =>
          rename_i h'
          have hi := cExprUB_stuck _ _ _ _ h'
          simp [cExec, hi]
      case assignVal =>
          rename_i h'
          have he := cExprUB_stuck _ _ _ _ h'
          simp [cExec, he]
      case assignIdxOut =>
          rename_i k hIdx hEval
          simp only [cExec, hEval]
          cases he : aEval e m ρ g with
          | some v =>
              show (if 0 ≤ k ∧ k < (g t : Int) ∧ cLo sgn w ≤ v ∧ v ≤ cHi sgn w then
                some ((fun t' k' f' =>
                  if t' = t ∧ k' = k.toNat ∧ f' = f then v else m t' k' f'), ρ)
                else none) = none
              cases hIdx
              case outLo => rename_i h''; exact if_neg (by omega)
              case outHi => rename_i h''; exact if_neg (by omega)
          | none => rfl
      case assignRange =>
          rename_i k v hRg hki hve
          simp only [cExec, hki, hve]
          show (if 0 ≤ k ∧ k < (g t : Int) ∧ cLo sgn w ≤ v ∧ v ≤ cHi sgn w then
            some ((fun t' k' f' =>
              if t' = t ∧ k' = k.toNat ∧ f' = f then v else m t' k' f'), ρ)
            else none) = none
          exact if_neg (by cases hRg with | inl h'' => omega | inr h'' => omega)
  | seq a b iha ihb =>
      intro m ρ g h fuel
      cases h
      case seqL =>
          rename_i h'
          have ha := iha m ρ g h' fuel
          simp [cExec, ha]
      case seqR =>
          rename_i h'
          simp only [cExec]
          cases hac : cExec a m ρ g fuel with
          | some pm =>
              cases pm with
              | mk m' ρ' =>
                  have hb := h' fuel m' ρ' hac
                  exact ihb m' ρ' g hb fuel
          | none => rfl
  | cif c t e _ _ =>
      intro m ρ g h fuel
      cases h
      case ifCond =>
          rename_i h'
          have hc := cExprUB_stuck _ _ _ _ h'
          simp [cExec, hc]
  | cfor x lo hi body ih =>
      intro m ρ g h fuel
      cases h
      case forFirst =>
          rename_i hlt h'
          cases fuel with
          | zero => rfl
          | succ n =>
              simp only [cExec, cForRun]
              have hb : cExec body m (cUpd ρ x lo) g n = none :=
                ih m (cUpd ρ x lo) g h' n
              rw [if_pos hlt, hb]

/-- Progress for the store: clean subexpressions plus the emitter's
    range guarantee reach a successor memory. -/
theorem cExec_assign_progress : ∀ (t : Nat) (i : CExpr) (f : Nat) (sgn : Bool)
    (w : CWidth) (e : CExpr) (m : CMem) (ρ : CEnv) (g : CGeom) (fuel : Nat),
    cOk i m ρ g = true → cOk e m ρ g = true →
    (∀ k v, aEval i m ρ g = some k → aEval e m ρ g = some v →
      0 ≤ k ∧ k < (g t : Int) ∧ cLo sgn w ≤ v ∧ v ≤ cHi sgn w) →
    ∃ m', cExec (.assign t i f sgn w e) m ρ g fuel = some (m', ρ) := by
  intro t i f sgn w e m ρ g fuel hi he hrange
  obtain ⟨k, hk⟩ := cOk_progress i m ρ g hi
  obtain ⟨v, hv⟩ := cOk_progress e m ρ g he
  have hc := hrange k v hk hv
  exact ⟨(fun t' k' f' =>
    if t' = t ∧ k' = k.toNat ∧ f' = f then v else m t' k' f'),
    by simp [cExec, hk, hv, hc]⟩
