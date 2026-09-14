/-
  Datei:      Grammatik/Gleitkomma.lean
  Gegenstand: A KERNEL-COMPUTABLE IEEE-754 model for binary32 and binary64.

  The current model (`Typen.lean`: `Gleit`, `Semantik.lean`: `gleitRechne`)
  computes floats with Lean's built-in `Float`, which is OPAQUE to the kernel:
  nothing about float values can be proved and no witness computed without
  `native_decide` (forbidden). This file is the replacement, built WITHOUT
  switching the model yet (a later task does that).

  Design: formats as data (`Format`: precision `p`, maximal exponent `emax`);
  values as bit triples (sign, biased exponent, significand as `Nat`) with
  finite / zero / subnormal / infinity / NaN cases; exact values as rationals
  (`Exakt`: `Int` numerator with a power-of-two exponent, plus the general
  `Bruch` for division); round-to-nearest-ties-to-even from the exact value
  (structural / fuel recursion only, so it reduces in the kernel); every op
  is "exact result, then round" -- the IEEE definition.
-/

namespace Gabbro.Grammatik.Gleitkomma

/-- An IEEE-754 binary interchange format: `p` significand bits (hidden one
    included), maximal unbiased exponent `emax` (`emin = 1 - emax`). -/
structure Format where
  p : Nat
  emax : Nat
  deriving DecidableEq, Repr

/-- binary32: 24 significand bits, `emax = 127`. -/
def f32 : Format := ⟨24, 127⟩

/-- binary64: 53 significand bits, `emax = 1023`. -/
def f64 : Format := ⟨53, 1023⟩

/-- Minimal unbiased exponent. -/
def Format.emin (F : Format) : Int := 1 - (F.emax : Int)

/-- A value of format `F` as data: sign, biased exponent, significand. -/
structure GBits (F : Format) where
  sign : Bool
  bexp : Nat
  frac : Nat
  deriving DecidableEq, Repr

/-- Exponent bias: `emax`, so the biased range is `0 .. 2 * emax + 1`. -/
def Format.bias (F : Format) : Nat := F.emax

/-- Maximal biased exponent (all ones: infinity / NaN). -/
def Format.bexpMax (F : Format) : Nat := 2 * F.emax + 1

/-- Stored significand bits (the hidden leading one excluded). -/
def Format.fracBits (F : Format) : Nat := F.p - 1

/-- Exponent field width: `8` for binary32, `11` for binary64. -/
def Format.ebits (F : Format) : Nat := Nat.log2 (F.bexpMax + 1)

/-- The five IEEE cases, as data. -/
inductive Klasse where
  | null | subnormal | normal | unendlich | nan
  deriving DecidableEq, Repr

/-- Classification from the bit triple. -/
def klasse (F : Format) (g : GBits F) : Klasse :=
  if g.bexp = F.bexpMax then
    if g.frac = 0 then .unendlich else .nan
  else if g.bexp = 0 then
    if g.frac = 0 then .null else .subnormal
  else .normal

/-- Well-formed bit triple: exponent in range, significand fits its field. -/
def wf (F : Format) (g : GBits F) : Prop :=
  g.bexp ≤ F.bexpMax ∧ g.frac < 2 ^ F.fracBits

instance (F : Format) (g : GBits F) : Decidable (wf F g) :=
  Nat.decLe _ _ |>.casesOn (fun h => isFalse (fun w => h w.1))
    (fun h1 => (Nat.decLt _ _).casesOn (fun h => isFalse (fun w => h w.2))
      (fun h2 => isTrue ⟨h1, h2⟩))

/-- Bit pattern as a `Nat` (sign high, then exponent, then significand). -/
def zuBits (F : Format) (g : GBits F) : Nat :=
  (if g.sign then 2 ^ (F.ebits + F.fracBits) else 0)
    + g.bexp * 2 ^ F.fracBits + g.frac

/-- An exact dyadic value: `zaehler * 2 ^ zweierExp`. Every finite float is
    one; so is every exact result of `add` / `sub` / `mul` on finite floats. -/
structure Exakt where
  zaehler : Int
  zweierExp : Int
  deriving DecidableEq, Repr

/-- An exact general rational: `zaehler / nenner`. Division of finite floats
    needs this (`1 / 3` is not dyadic); the dyadic case is `nenner = 2 ^ k`. -/
structure Bruch where
  zaehler : Int
  nenner : Nat
  deriving DecidableEq, Repr

/-- The exact dyadic value of a finite bit triple (`none` for infinity/NaN):
    normal `(-1)^s * (2^(p-1) + frac) * 2^(E-(p-1))`, subnormal
    `(-1)^s * frac * 2^(emin-(p-1))`, zero `0`. Let-free for rewriting. -/
def wertExakt (F : Format) (g : GBits F) : Option Exakt :=
  match klasse F g with
  | .normal =>
    some ⟨(if g.sign then (-1 : Int) else 1) * ((2 ^ (F.p - 1) : Nat) + (g.frac : Int)),
      (g.bexp : Int) - (F.bias : Int) - ((F.p : Int) - 1)⟩
  | .subnormal =>
    some ⟨(if g.sign then (-1 : Int) else 1) * (g.frac : Int),
      F.emin - ((F.p : Int) - 1)⟩
  | .null => some ⟨0, 0⟩
  | _ => none

/-- Bit length by fuel recursion (structural on `fuel`, so kernel-reducible):
    `bitlenAux n fuel` is exact whenever `fuel ≥ bitlen n`. -/
def bitlenAux : Nat → Nat → Nat
  | _, 0 => 0
  | n, fuel + 1 => if n = 0 then 0 else 1 + bitlenAux (n / 2) fuel

/-- Bit length of `n` (`0` for `n = 0`). -/
def bitlen (n : Nat) : Nat := bitlenAux n n

/-- Round-half-to-even at the integer level: `quo` with remainder `rest/den`
    (`0 ≤ rest < den`, `0 < den`) rounds up iff past half, or on an exact tie
    with odd `quo`. The IEEE significand decision, isolated. -/
def rundeInt (quo rest den : Nat) : Nat :=
  if 2 * rest > den then quo + 1
  else if 2 * rest < den then quo
  else if quo % 2 == 1 then quo + 1 else quo

/-- Unbiased binary exponent of `n / d` (`n > 0`, `d > 0`):
    `2 ^ E ≤ n / d < 2 ^ (E + 1)`, by exact integer comparisons around
    `bitlen n - bitlen d` (structural recursion only, via `bitlen`).
    Split into `findeExpBei` (the decision at a given `E0`) so proofs can
    rewrite without unfolding a `let`. -/
def findeExpBei (n d : Nat) (E0 : Int) : Int :=
  if 0 ≤ E0 then
    if d * 2 ^ E0.toNat ≤ n then E0 else E0 - 1
  else
    if d ≤ n * 2 ^ (-E0).toNat then E0 else E0 - 1

def findeExp (n d : Nat) : Int :=
  findeExpBei n d ((bitlen n : Int) - (bitlen d : Int))

/-- Scaled integer quotient for the normal path: the value `n / d`
    scaled by `2 ^ ((p - 1) - E)` as a numerator/denominator pair (one side
    carries the shift, so both stay `Nat`). -/
def normQD (p : Nat) (E : Int) (n d : Nat) : Nat × Nat :=
  if 0 ≤ (p : Int) - 1 - E then (n * 2 ^ ((p : Int) - 1 - E).toNat, d)
  else (n, d * 2 ^ (E - ((p : Int) - 1)).toNat)

/-- Rounded significand on the normal path (the `rundeInt` decision over
    the scaled quotient). -/
def normQ (p : Nat) (E : Int) (n d : Nat) : Nat :=
  rundeInt ((normQD p E n d).1 / (normQD p E n d).2)
    ((normQD p E n d).1 % (normQD p E n d).2) (normQD p E n d).2

/-- Rounded significand on the subnormal path (scaled by `2 ^ ((p - 1) - emin)`). -/
def subQ (F : Format) (n d : Nat) : Nat :=
  let k : Nat := ((F.p : Int) - 1 - F.emin).toNat
  rundeInt ((n * 2 ^ k) / d) ((n * 2 ^ k) % d) d

/-- Round-to-nearest-ties-to-even from an exact rational to format `F`:
    find the exponent, scale to an integer quotient with remainder, decide
    the significand with `rundeInt`, place the normal / subnormal / overflow
    (`infinity`) / underflow (`zero`) cases. `nenner = 0` is NaN.
    Let-free (helpers take explicit arguments) so proofs can rewrite. -/
def rundeBruchKern (F : Format) (s : Bool) (n d : Nat) (E : Int) : GBits F :=
  if (F.emax : Int) < E then ⟨s, F.bexpMax, 0⟩
  else if E < F.emin - (F.p : Int) then ⟨s, 0, 0⟩
  else if F.emin ≤ E then
    if normQ F.p E n d < 2 ^ F.p then
      ⟨s, (E - F.emin + 1).toNat, normQ F.p E n d - 2 ^ (F.p - 1)⟩
    else if E < (F.emax : Int) then ⟨s, (E - F.emin + 2).toNat, 0⟩
    else ⟨s, F.bexpMax, 0⟩
  else
    if subQ F n d < 2 ^ (F.p - 1) then ⟨s, 0, subQ F n d⟩
    else ⟨s, 1, 0⟩

/-- Rounding with sign, numerator and denominator explicit. -/
def rundeBruchBei (F : Format) (s : Bool) (n d : Nat) : GBits F :=
  if d = 0 then ⟨false, F.bexpMax, 1⟩
  else if n = 0 then ⟨s, 0, 0⟩
  else rundeBruchKern F s n d (findeExp n d)

def rundeBruch (F : Format) (b : Bruch) : GBits F :=
  rundeBruchBei F (b.zaehler < 0) b.zaehler.natAbs b.nenner

/-- An exact dyadic value as a general rational (the `rundeExakt` path). -/
def exaktBruch (v : Exakt) : Bruch :=
  if 0 ≤ v.zweierExp then ⟨v.zaehler * (2 ^ v.zweierExp.toNat : Nat), 1⟩
  else ⟨v.zaehler, 2 ^ (-v.zweierExp).toNat⟩

/-- Rounding from an exact dyadic value (the `add` / `sub` / `mul` path). -/
def rundeExakt (F : Format) (v : Exakt) : GBits F :=
  rundeBruch F (exaktBruch v)

/-- Negation flips the sign bit (signed zeros and infinities included;
    NaN payloads are kept). -/
def neg (F : Format) (a : GBits F) : GBits F :=
  { a with sign := !a.sign }

/-- Exact dyadic sum of two exact values. -/
def exaktAdd (u v : Exakt) : Exakt :=
  let e := if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp
  ⟨u.zaehler * (2 ^ (u.zweierExp - e).toNat : Nat)
    + v.zaehler * (2 ^ (v.zweierExp - e).toNat : Nat), e⟩

/-- Exact dyadic product of two exact values. -/
def exaktMul (u v : Exakt) : Exakt :=
  ⟨u.zaehler * v.zaehler, u.zweierExp + v.zweierExp⟩

/-- Canonical quiet NaN (payload `1`). -/
def nanQ (F : Format) : GBits F := ⟨false, F.bexpMax, 1⟩

/-- Addition as "exact result, then round", with the IEEE special cases
    (NaN propagation, `inf + -inf = NaN`, `inf + finite = inf`) and the
    signed-zero rule of IEEE 754-2019 §6.3: the sum of two zeros is `-0`
    exactly when both are `-0` (`(-0) + (-0) = -0`, `(+0) + (-0) = +0`);
    every other exact zero sum (`x + (-x)`, `x - x`) is `+0` under
    round-to-nearest -- which `rundeExakt` gives, since an exact zero has
    a non-negative numerator. -/
def add (F : Format) (a b : GBits F) : GBits F :=
  match klasse F a, klasse F b with
  | .nan, _ => a
  | _, .nan => b
  | .unendlich, .unendlich => if a.sign == b.sign then a else nanQ F
  | .unendlich, _ => a
  | _, .unendlich => b
  | .null, .null => ⟨a.sign && b.sign, 0, 0⟩
  | _, _ =>
    match wertExakt F a, wertExakt F b with
    | some u, some v => rundeExakt F (exaktAdd u v)
    | _, _ => nanQ F

/-- Subtraction as "exact result, then round" (via negation). -/
def sub (F : Format) (a b : GBits F) : GBits F := add F a (neg F b)

/-- Multiplication as "exact result, then round" (`0 * inf = NaN`,
    `inf * finite = inf` with xor sign, else the exact product). -/
def mul (F : Format) (a b : GBits F) : GBits F :=
  match klasse F a, klasse F b with
  | .nan, _ => a
  | _, .nan => b
  | .unendlich, .unendlich => ⟨a.sign != b.sign, F.bexpMax, 0⟩
  | .unendlich, .null => nanQ F
  | .null, .unendlich => nanQ F
  | .unendlich, _ => ⟨a.sign != b.sign, F.bexpMax, 0⟩
  | _, .unendlich => ⟨a.sign != b.sign, F.bexpMax, 0⟩
  | .null, _ => ⟨a.sign != b.sign, 0, 0⟩
  | _, .null => ⟨a.sign != b.sign, 0, 0⟩
  | _, _ =>
    match wertExakt F a, wertExakt F b with
    | some u, some v => rundeExakt F (exaktMul u v)
    | _, _ => nanQ F

/-- Exact quotient of two exact values as a general rational (signs
    folded out so the denominator stays positive). -/
def divBruch (u v : Exakt) : Bruch :=
  let m := if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp
  let na : Nat := u.zaehler.natAbs * 2 ^ (u.zweierExp - m).toNat
  let da : Nat := v.zaehler.natAbs * 2 ^ (v.zweierExp - m).toNat
  ⟨if (u.zaehler < 0) != (v.zaehler < 0) then -(na : Int) else na, da⟩

/-- Division as "exact result, then round": the exact quotient of the two
    exact values (a general rational -- `1 / 3` is not dyadic), with the
    IEEE special cases (`x / x = NaN` for `inf`/`0`, `finite / 0 = inf`,
    `inf / finite = inf`, `finite / inf = zero`, xor signs). -/
def div (F : Format) (a b : GBits F) : GBits F :=
  match klasse F a, klasse F b with
  | .nan, _ => a
  | _, .nan => b
  | .unendlich, .unendlich => nanQ F
  | .unendlich, _ => ⟨a.sign != b.sign, F.bexpMax, 0⟩
  | _, .unendlich => ⟨a.sign != b.sign, 0, 0⟩
  | _, .null =>
    match wertExakt F a with
    | some u => if u.zaehler == 0 then nanQ F
                else ⟨a.sign != b.sign, F.bexpMax, 0⟩
    | none => nanQ F
  | .null, _ => ⟨a.sign != b.sign, 0, 0⟩
  | _, _ =>
    match wertExakt F a, wertExakt F b with
    | some u, some v => rundeBruch F (divBruch u v)
    | _, _ => nanQ F

/-- Integer conversion: the exact integer, then round. -/
def ofInt (F : Format) (z : Int) : GBits F := rundeExakt F ⟨z, 0⟩

/-- Rational conversion: the exact rational, then round (`den = 0` is NaN). -/
def ofRat (F : Format) (z : Int) (n : Nat) : GBits F := rundeBruch F ⟨z, n⟩

/-- Strict comparison: NaN is unordered (false), infinities compare by
    sign, finite values by exact cross-multiplication (signed zeros equal). -/
def flt (F : Format) (a b : GBits F) : Bool :=
  match klasse F a, klasse F b with
  | .nan, _ => false
  | _, .nan => false
  | .unendlich, .unendlich => a.sign && !b.sign
  | .unendlich, _ => a.sign
  | _, .unendlich => !b.sign
  | _, _ =>
    match wertExakt F a, wertExakt F b with
    | some u, some v =>
      let m := if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp
      u.zaehler * (2 ^ (u.zweierExp - m).toNat : Nat)
        < v.zaehler * (2 ^ (v.zweierExp - m).toNat : Nat)
    | _, _ => false

/-- Non-strict comparison: NaN is unordered (false, as C's `<=`), else
    the negated reverse strict comparison. (Lane 166 had `!flt F b a`
    outright, which answered `true` for a NaN operand.) -/
def fle (F : Format) (a b : GBits F) : Bool :=
  match klasse F a, klasse F b with
  | .nan, _ => false
  | _, .nan => false
  | _, _ => !flt F b a

/-! ## Theorems: the integer significand decision is correct. -/

/-- Below half the quotient stands. -/
theorem rundeInt_fall (quo rest den : Nat)
    (h : 2 * rest < den) : rundeInt quo rest den = quo := by
  unfold rundeInt
  rw [if_neg (by omega : ¬ den < 2 * rest), if_pos h]

/-- Past half the quotient moves up. -/
theorem rundeInt_steig (quo rest den : Nat)
    (h : den < 2 * rest) : rundeInt quo rest den = quo + 1 := by
  unfold rundeInt
  rw [if_pos h]

/-- On an exact tie the even quotient wins. -/
theorem rundeInt_tie (quo rest den : Nat)
    (h : 2 * rest = den) : rundeInt quo rest den % 2 = 0 := by
  have g1 : ¬ den < 2 * rest := by omega
  have g2 : ¬ 2 * rest < den := by omega
  unfold rundeInt
  rw [if_neg g1, if_neg g2]
  by_cases hodd : quo % 2 = 1
  · rw [if_pos (by simpa using hodd)]
    omega
  · rw [if_neg (by simpa using hodd)]
    have hlt : quo % 2 < 2 := Nat.mod_lt _ (by decide)
    omega

/-- Monotonicity of the significand decision: a larger value (same
    denominator, quotient-remainder ordered, the upper remainder normalised)
    never rounds down further. `hr₂` is load-bearing (`5,0` vs `3,25` at
    `den = 10` breaks it); the lower remainder needs no bound. -/
theorem rundeInt_monoton (quo₁ rest₁ quo₂ rest₂ den : Nat)
    (hr₂ : rest₂ < den)
    (h : quo₁ * den + rest₁ ≤ quo₂ * den + rest₂) :
    rundeInt quo₁ rest₁ den ≤ rundeInt quo₂ rest₂ den := by
  have hle : quo₁ ≤ quo₂ := by
    by_cases hc : quo₁ ≤ quo₂
    · exact hc
    · have hlt : quo₂ < quo₁ := by omega
      have hsplit : quo₁ = quo₂ + (quo₁ - quo₂) :=
        (Nat.add_sub_cancel' (Nat.le_of_lt hlt)).symm
      have hdecomp : quo₁ * den = quo₂ * den + (quo₁ - quo₂) * den := by
        have hcong := congrArg (· * den) hsplit
        rw [Nat.add_mul] at hcong
        exact hcong
      have hle2 : (quo₁ - quo₂) * den ≤ rest₂ := by omega
      have hge : den ≤ (quo₁ - quo₂) * den := by
        have h1 : (1 : Nat) ≤ quo₁ - quo₂ := by omega
        have h2 := Nat.mul_le_mul h1 (Nat.le_refl den)
        simpa using h2
      omega
  have hrest : quo₁ = quo₂ → rest₁ ≤ rest₂ := by
    intro heq; subst heq; exact Nat.le_of_add_le_add_left h
  rcases Nat.lt_or_ge den (2 * rest₁) with h1 | h1
  · -- Side 1 rounds up.
    have r1 := rundeInt_steig quo₁ rest₁ den h1
    rcases Nat.lt_or_ge den (2 * rest₂) with h2 | h2
    · rw [r1, rundeInt_steig quo₂ rest₂ den h2]; omega
    · rcases Nat.lt_or_ge (2 * rest₂) den with k2 | k2
      · rw [r1, rundeInt_fall quo₂ rest₂ den k2]
        by_cases heq : quo₁ = quo₂
        · subst heq; have hr := hrest rfl; omega
        · have hlt : quo₁ < quo₂ := Nat.lt_of_le_of_ne hle heq; omega
      · have htie2 : 2 * rest₂ = den := by omega
        by_cases p2 : quo₂ % 2 = 1
        · have r2 : rundeInt quo₂ rest₂ den = quo₂ + 1 := by
            unfold rundeInt
            rw [if_neg (by omega : ¬ den < 2 * rest₂),
                if_neg (by omega : ¬ 2 * rest₂ < den),
                if_pos (by simpa using p2)]
          rw [r1, r2]; omega
        · have r2 : rundeInt quo₂ rest₂ den = quo₂ := by
            unfold rundeInt
            rw [if_neg (by omega : ¬ den < 2 * rest₂),
                if_neg (by omega : ¬ 2 * rest₂ < den),
                if_neg (by simpa using p2)]
          rw [r1, r2]
          by_cases heq : quo₁ = quo₂
          · subst heq; have hr := hrest rfl; omega
          · have hlt : quo₁ < quo₂ := Nat.lt_of_le_of_ne hle heq; omega
  · -- Side 1 stays down or ties.
    rcases Nat.lt_or_ge (2 * rest₁) den with k1 | k1
    · have r1 := rundeInt_fall quo₁ rest₁ den k1
      rcases Nat.lt_or_ge den (2 * rest₂) with h2 | h2
      · rw [r1, rundeInt_steig quo₂ rest₂ den h2]; omega
      · rcases Nat.lt_or_ge (2 * rest₂) den with k2 | k2
        · rw [r1, rundeInt_fall quo₂ rest₂ den k2]; omega
        · by_cases p2 : quo₂ % 2 = 1
          · have r2 : rundeInt quo₂ rest₂ den = quo₂ + 1 := by
              unfold rundeInt
              rw [if_neg (by omega : ¬ den < 2 * rest₂),
                  if_neg (by omega : ¬ 2 * rest₂ < den),
                  if_pos (by simpa using p2)]
            rw [r1, r2]; omega
          · have r2 : rundeInt quo₂ rest₂ den = quo₂ := by
              unfold rundeInt
              rw [if_neg (by omega : ¬ den < 2 * rest₂),
                  if_neg (by omega : ¬ 2 * rest₂ < den),
                  if_neg (by simpa using p2)]
            rw [r1, r2]; omega
    · -- Tie on side 1.
      by_cases p1 : quo₁ % 2 = 1
      · have r1 : rundeInt quo₁ rest₁ den = quo₁ + 1 := by
          unfold rundeInt
          rw [if_neg (by omega : ¬ den < 2 * rest₁),
              if_neg (by omega : ¬ 2 * rest₁ < den),
              if_pos (by simpa using p1)]
        rcases Nat.lt_or_ge den (2 * rest₂) with h2 | h2
        · rw [r1, rundeInt_steig quo₂ rest₂ den h2]; omega
        · rcases Nat.lt_or_ge (2 * rest₂) den with k2 | k2
          · rw [r1, rundeInt_fall quo₂ rest₂ den k2]
            by_cases heq : quo₁ = quo₂
            · subst heq; have hr := hrest rfl; omega
            · have hlt : quo₁ < quo₂ := Nat.lt_of_le_of_ne hle heq; omega
          · by_cases p2 : quo₂ % 2 = 1
            · have r2 : rundeInt quo₂ rest₂ den = quo₂ + 1 := by
                unfold rundeInt
                rw [if_neg (by omega : ¬ den < 2 * rest₂),
                    if_neg (by omega : ¬ 2 * rest₂ < den),
                    if_pos (by simpa using p2)]
              rw [r1, r2]; omega
            · have r2 : rundeInt quo₂ rest₂ den = quo₂ := by
                unfold rundeInt
                rw [if_neg (by omega : ¬ den < 2 * rest₂),
                    if_neg (by omega : ¬ 2 * rest₂ < den),
                    if_neg (by simpa using p2)]
              rw [r1, r2]
              by_cases heq : quo₁ = quo₂
              · subst heq; have hr := hrest rfl; omega
              · have hlt : quo₁ < quo₂ := Nat.lt_of_le_of_ne hle heq; omega
      · have r1 : rundeInt quo₁ rest₁ den = quo₁ := by
          unfold rundeInt
          rw [if_neg (by omega : ¬ den < 2 * rest₁),
              if_neg (by omega : ¬ 2 * rest₁ < den),
              if_neg (by simpa using p1)]
        rcases Nat.lt_or_ge den (2 * rest₂) with h2 | h2
        · rw [r1, rundeInt_steig quo₂ rest₂ den h2]; omega
        · rcases Nat.lt_or_ge (2 * rest₂) den with k2 | k2
          · rw [r1, rundeInt_fall quo₂ rest₂ den k2]; omega
          · by_cases p2 : quo₂ % 2 = 1
            · have r2 : rundeInt quo₂ rest₂ den = quo₂ + 1 := by
                unfold rundeInt
                rw [if_neg (by omega : ¬ den < 2 * rest₂),
                    if_neg (by omega : ¬ 2 * rest₂ < den),
                    if_pos (by simpa using p2)]
              rw [r1, r2]; omega
            · have r2 : rundeInt quo₂ rest₂ den = quo₂ := by
                unfold rundeInt
                rw [if_neg (by omega : ¬ den < 2 * rest₂),
                    if_neg (by omega : ¬ 2 * rest₂ < den),
                    if_neg (by simpa using p2)]
              rw [r1, r2]; omega

/-! ## Theorems: bit lengths bound their numbers. -/

theorem bitlenAux_null (n : Nat) : bitlenAux n 0 = 0 := rfl

theorem bitlenAux_succ (n fuel : Nat) :
    bitlenAux n (fuel + 1) = if n = 0 then 0 else 1 + bitlenAux (n / 2) fuel := rfl

theorem bitlenAux_null_all (fuel : Nat) : bitlenAux 0 fuel = 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel _ => simp [bitlenAux_succ]

theorem zweiHoch_succ (k : Nat) : (2 : Nat) ^ (1 + k) = 2 * 2 ^ k := by
  rw [Nat.pow_add]

/-- Upper bound: `fuel` bits suffice whenever the number fits in `fuel` bits. -/
theorem bitlenAux_obere (fuel n : Nat) (h : n < 2 ^ fuel) :
    n < 2 ^ (bitlenAux n fuel) := by
  induction fuel generalizing n with
  | zero => rw [bitlenAux_null]; exact h
  | succ fuel ih =>
    rw [bitlenAux_succ]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, if_false]
      have hhalf : n / 2 < 2 ^ fuel := by
        have e : (2 : Nat) ^ (fuel + 1) = 2 ^ fuel * 2 := Nat.pow_succ 2 fuel
        have hmod := Nat.div_add_mod n 2
        omega
      have ih' := ih (n / 2) hhalf
      have e2 := zweiHoch_succ (bitlenAux (n / 2) fuel)
      have hmod := Nat.div_add_mod n 2
      omega

/-- Lower bound: the bit length is tight up to one bit (`2 ^ bitlen ≤ 2 * n`). -/
theorem bitlenAux_untere (fuel n : Nat) (hn : n ≠ 0) :
    2 ^ (bitlenAux n fuel) ≤ 2 * n := by
  induction fuel generalizing n with
  | zero =>
    rw [bitlenAux_null]
    have e0 : (2 : Nat) ^ 0 = 1 := rfl
    omega
  | succ fuel ih =>
    rw [bitlenAux_succ]
    by_cases hn0 : n = 0
    · subst hn0; exact (hn rfl).elim
    · simp only [hn0, if_false]
      by_cases hh : n / 2 = 0
      · have hn1 : n = 1 := by omega
        subst hn1
        have e0 : (1 : Nat) / 2 = 0 := by decide
        rw [e0, bitlenAux_null_all]
        decide
      · have ih' := ih (n / 2) hh
        have e2 := zweiHoch_succ (bitlenAux (n / 2) fuel)
        have hmod := Nat.div_add_mod n 2
        omega

theorem bitlen_obere (n : Nat) : n < 2 ^ (bitlen n) :=
  bitlenAux_obere n n Nat.lt_two_pow_self

theorem bitlen_untere (n : Nat) (hn : n ≠ 0) : 2 ^ (bitlen n) ≤ 2 * n :=
  bitlenAux_untere n n hn

/-- Lower bound at non-negative exponents: with `E0 = bn - bd` over
    bit-length bounds (`2^bn ≤ 2n`, `d < 2^bd`), the decided exponent
    satisfies `d * 2^E ≤ n`. The `E0 - 1` arm (branch miss) is covered by
    halving the bit-length upper bound. -/
theorem findeExpBei_unten_nonneg (n d : Nat) (E0 : Int) (bn bd : Nat)
    (hE0 : E0 = (bn : Int) - (bd : Int))
    (hnB : 2 ^ bn ≤ 2 * n) (hdB : d < 2 ^ bd)
    (hE : 0 ≤ findeExpBei n d E0) : d * 2 ^ (findeExpBei n d E0).toNat ≤ n := by
  unfold findeExpBei at hE ⊢
  by_cases h0 : (0 : Int) ≤ E0
  · rw [if_pos h0] at hE ⊢
    by_cases hc : d * 2 ^ E0.toNat ≤ n
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc] at hE ⊢
      have hE0n : E0.toNat = bn - bd := by omega
      have hE1n : (E0 - 1).toNat = E0.toNat - 1 := by omega
      have hE1' : E0.toNat = 1 + (E0.toNat - 1) := by omega
      have hsplit2 : 2 ^ E0.toNat = 2 * 2 ^ (E0.toNat - 1) := by
        have hcong := congrArg (2 ^ ·) hE1'
        rw [zweiHoch_succ] at hcong
        exact hcong
      have hbn : bn = E0.toNat + bd := by omega
      have hpow : 2 ^ bn = 2 ^ E0.toNat * 2 ^ bd := by
        rw [hbn, Nat.pow_add]
      have hcomm : 2 ^ bd * 2 ^ E0.toNat = 2 ^ E0.toNat * 2 ^ bd :=
        Nat.mul_comm _ _
      have hleY : d * 2 ^ E0.toNat ≤ 2 * n := by
        have h1 := Nat.mul_le_mul (Nat.le_of_lt hdB) (Nat.le_refl (2 ^ E0.toNat))
        omega
      have hdm : d * 2 ^ E0.toNat = 2 * (d * 2 ^ (E0.toNat - 1)) := by
        rw [hsplit2, Nat.mul_left_comm]
      rw [hE1n]
      omega
  · rw [if_neg h0] at hE ⊢
    by_cases hc : d ≤ n * 2 ^ (-E0).toNat
    · rw [if_pos hc] at hE; omega
    · rw [if_neg hc] at hE; omega

/-- The decided exponent lower-bounds the quotient at non-negative values. -/
theorem findeExp_unten (n d : Nat) (hn : 0 < n)
    (hE : 0 ≤ findeExp n d) : d * 2 ^ (findeExp n d).toNat ≤ n := by
  unfold findeExp at hE ⊢
  exact findeExpBei_unten_nonneg n d ((bitlen n : Int) - (bitlen d : Int))
    (bitlen n) (bitlen d) rfl
    (bitlen_untere n (by omega)) (bitlen_obere d) hE

/-! ## Theorems: conversions and ops on in-range exact values stay finite. -/

/-- Zero bits classify as zero (needs a non-degenerate exponent field). -/
theorem klasse_null_bits (F : Format) (s : Bool) (hmax : 0 < F.bexpMax) :
    klasse F ⟨s, 0, 0⟩ = .null := by
  have e : (⟨s, 0, 0⟩ : GBits F).bexp = 0 := rfl
  have f : (⟨s, 0, 0⟩ : GBits F).frac = 0 := rfl
  unfold klasse
  rw [e, f, if_neg (by omega : ¬ (0 : Nat) = F.bexpMax), if_pos rfl, if_pos rfl]

/-- Nonzero significand at biased exponent zero is subnormal. -/
theorem klasse_subnormal_bits (F : Format) (s : Bool) (q : Nat)
    (hmax : 0 < F.bexpMax) (hq : q ≠ 0) :
    klasse F ⟨s, 0, q⟩ = .subnormal := by
  have e : (⟨s, 0, q⟩ : GBits F).bexp = 0 := rfl
  have f : (⟨s, 0, q⟩ : GBits F).frac = q := rfl
  unfold klasse
  rw [e, f, if_neg (by omega : ¬ (0 : Nat) = F.bexpMax), if_pos rfl, if_neg hq]

/-- A biased exponent strictly between zero and all-ones is normal. -/
theorem klasse_normal_bits (F : Format) (s : Bool) (bx fr : Nat)
    (hb0 : bx ≠ 0) (hbmax : bx < F.bexpMax) :
    klasse F ⟨s, bx, fr⟩ = .normal := by
  have e : (⟨s, bx, fr⟩ : GBits F).bexp = bx := rfl
  unfold klasse
  rw [e, if_neg (by omega : ¬ bx = F.bexpMax), if_neg hb0]

/-- Rounding a strictly in-range exact value stays finite: with `0 < den`
    and `|num| < den * 2^emax` (and a non-degenerate format), the result is
    normal, subnormal or zero -- never infinity or NaN. -/
theorem rundeBruch_finite (F : Format) (b : Bruch) (hF : 1 ≤ F.emax)
    (hd : 0 < b.nenner)
    (hob : b.zaehler.natAbs < b.nenner * 2 ^ F.emax) :
    klasse F (rundeBruch F b) = .normal
      ∨ klasse F (rundeBruch F b) = .subnormal
      ∨ klasse F (rundeBruch F b) = .null := by
  have hemin : F.emin = 1 - (F.emax : Int) := rfl
  have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
  have hmax : 0 < F.bexpMax := by omega
  unfold rundeBruch rundeBruchBei
  rw [if_neg (by omega : ¬ b.nenner = 0)]
  by_cases hn0 : b.zaehler.natAbs = 0
  · rw [if_pos hn0, klasse_null_bits F _ hmax]
    exact Or.inr (Or.inr rfl)
  · rw [if_neg hn0]
    have hn : 0 < b.zaehler.natAbs := Nat.pos_of_ne_zero hn0
    have hEle : findeExp b.zaehler.natAbs b.nenner ≤ (F.emax : Int) - 1 := by
      by_cases hE0 : 0 ≤ findeExp b.zaehler.natAbs b.nenner
      · by_cases hmaxl : (F.emax : Int) ≤ findeExp b.zaehler.natAbs b.nenner
        · have hlow := findeExp_unten _ _ hn hE0
          have hto : F.emax ≤ (findeExp b.zaehler.natAbs b.nenner).toNat := by omega
          have hmono := Nat.pow_le_pow_right (show 0 < 2 by decide) hto
          have hmul := Nat.mul_le_mul (Nat.le_refl b.nenner) hmono
          omega
        · omega
      · omega
    unfold rundeBruchKern
    rw [if_neg (by omega : ¬ (F.emax : Int) < findeExp b.zaehler.natAbs b.nenner)]
    by_cases hdeep : findeExp b.zaehler.natAbs b.nenner < F.emin - (F.p : Int)
    · rw [if_pos hdeep, klasse_null_bits F _ hmax]
      exact Or.inr (Or.inr rfl)
    · rw [if_neg hdeep]
      by_cases hEmin : F.emin ≤ findeExp b.zaehler.natAbs b.nenner
      · rw [if_pos hEmin]
        by_cases hq : normQ F.p (findeExp b.zaehler.natAbs b.nenner)
            b.zaehler.natAbs b.nenner < 2 ^ F.p
        · rw [if_pos hq]
          have hb0 : (findeExp b.zaehler.natAbs b.nenner - F.emin + 1).toNat ≠ 0 := by omega
          have hbmax : (findeExp b.zaehler.natAbs b.nenner - F.emin + 1).toNat
              < F.bexpMax := by omega
          rw [klasse_normal_bits F _ _ _ hb0 hbmax]
          exact Or.inl rfl
        · rw [if_neg hq]
          by_cases hEmax : findeExp b.zaehler.natAbs b.nenner < (F.emax : Int)
          · rw [if_pos hEmax]
            have hb0 : (findeExp b.zaehler.natAbs b.nenner - F.emin + 2).toNat ≠ 0 := by omega
            have hbmax : (findeExp b.zaehler.natAbs b.nenner - F.emin + 2).toNat
                < F.bexpMax := by omega
            rw [klasse_normal_bits F _ _ _ hb0 hbmax]
            exact Or.inl rfl
          · have hlt : findeExp b.zaehler.natAbs b.nenner < (F.emax : Int) := by omega
            exact (hEmax hlt).elim
      · rw [if_neg hEmin]
        by_cases hsub : subQ F b.zaehler.natAbs b.nenner < 2 ^ (F.p - 1)
        · rw [if_pos hsub]
          by_cases hq0 : subQ F b.zaehler.natAbs b.nenner = 0
          · rw [hq0, klasse_null_bits F _ hmax]
            exact Or.inr (Or.inr rfl)
          · rw [klasse_subnormal_bits F _ _ hmax hq0]
            exact Or.inr (Or.inl rfl)
        · rw [if_neg hsub]
          have hbmax : (1 : Nat) < F.bexpMax := by omega
          rw [klasse_normal_bits F _ 1 0 (by omega) hbmax]
          exact Or.inl rfl

/-! ## Conversions through the finite rounding path. -/

/-- Integers convert through the dyadic path with denominator one. -/
theorem ofInt_bruch (F : Format) (z : Int) :
    ofInt F z = rundeBruch F ⟨z, 1⟩ := by
  have e1 : (⟨z, (0 : Int)⟩ : Exakt).zweierExp = 0 := rfl
  have e2 : (⟨z, (0 : Int)⟩ : Exakt).zaehler = z := rfl
  have t0 : (0 : Int).toNat = 0 := rfl
  have p0 : (2 : Nat) ^ (0 : Nat) = 1 := rfl
  unfold ofInt rundeExakt exaktBruch
  rw [e1, e2, t0, p0, if_pos (by omega : (0 : Int) ≤ 0)]
  have m1 : z * ((1 : Nat) : Int) = z := Int.mul_one z
  rw [m1]

/-- An integer strictly inside `2^emax` converts to a finite value. -/
theorem ofInt_finite (F : Format) (hF : 1 ≤ F.emax) (z : Int)
    (h : z.natAbs < 2 ^ F.emax) :
    klasse F (ofInt F z) = .normal ∨ klasse F (ofInt F z) = .subnormal
      ∨ klasse F (ofInt F z) = .null := by
  rw [ofInt_bruch]
  have ez : (⟨z, (1 : Nat)⟩ : Bruch).zaehler = z := rfl
  have en : (⟨z, (1 : Nat)⟩ : Bruch).nenner = 1 := rfl
  have hd1 : 0 < (⟨z, (1 : Nat)⟩ : Bruch).nenner := by omega
  have hob1 : (⟨z, (1 : Nat)⟩ : Bruch).zaehler.natAbs
      < (⟨z, (1 : Nat)⟩ : Bruch).nenner * 2 ^ F.emax := by
    rw [ez, en]; omega
  exact rundeBruch_finite F ⟨z, 1⟩ hF hd1 hob1

/-- An exact rational strictly inside `2^emax` converts to a finite value. -/
theorem ofRat_finite (F : Format) (hF : 1 ≤ F.emax) (z : Int) (n : Nat)
    (hd : 0 < n) (hob : z.natAbs < n * 2 ^ F.emax) :
    klasse F (ofRat F z n) = .normal ∨ klasse F (ofRat F z n) = .subnormal
      ∨ klasse F (ofRat F z n) = .null :=
  rundeBruch_finite F ⟨z, n⟩ hF hd hob

/-- The dyadic path never has a zero denominator. -/
theorem exaktBruch_nenner_pos (v : Exakt) : 0 < (exaktBruch v).nenner := by
  unfold exaktBruch
  by_cases h : 0 ≤ v.zweierExp
  · rw [if_pos h]
    have e : (⟨v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int), 1⟩ : Bruch).nenner
        = 1 := rfl
    rw [e]; decide
  · rw [if_neg h]
    have e : (⟨v.zaehler, 2 ^ (-v.zweierExp).toNat⟩ : Bruch).nenner
        = 2 ^ (-v.zweierExp).toNat := rfl
    rw [e]; exact Nat.pow_pos (show 0 < 2 by decide)

/-- Addition of finite values with in-range exact sum stays finite
    (and is, by construction, the rounded exact sum). -/
theorem add_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hob : (exaktBruch (exaktAdd u v)).zaehler.natAbs
      < (exaktBruch (exaktAdd u v)).nenner * 2 ^ F.emax) :
    klasse F (add F a b) = .normal ∨ klasse F (add F a b) = .subnormal
      ∨ klasse F (add F a b) = .null := by
  have hmax : 0 < F.bexpMax := by
    have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
    omega
  have hfin : klasse F (rundeExakt F (exaktAdd u v)) = .normal
      ∨ klasse F (rundeExakt F (exaktAdd u v)) = .subnormal
      ∨ klasse F (rundeExakt F (exaktAdd u v)) = .null := by
    unfold rundeExakt
    exact rundeBruch_finite F _ hF (exaktBruch_nenner_pos _) hob
  generalize hka : klasse F a = ka
  generalize hkb : klasse F b = kb
  cases ka <;> cases kb <;>
    first
      | (unfold add; rw [hka, hkb, klasse_null_bits F _ hmax]
         exact Or.inr (Or.inr rfl))
      | (unfold add; rw [hka, hkb, ha, hb]; exact hfin)
      | (have hnone : wertExakt F a = none := by unfold wertExakt; rw [hka]
         rw [hnone] at ha; cases ha)
      | (have hnone : wertExakt F b = none := by unfold wertExakt; rw [hkb]
         rw [hnone] at hb; cases hb)

/-- Multiplication of finite values with in-range exact product stays finite
    (zero times finite is the signed zero, otherwise the rounded product). -/
theorem mul_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hob : (exaktBruch (exaktMul u v)).zaehler.natAbs
      < (exaktBruch (exaktMul u v)).nenner * 2 ^ F.emax) :
    klasse F (mul F a b) = .normal ∨ klasse F (mul F a b) = .subnormal
      ∨ klasse F (mul F a b) = .null := by
  have hmax : 0 < F.bexpMax := by
    have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
    omega
  have hfin : klasse F (rundeExakt F (exaktMul u v)) = .normal
      ∨ klasse F (rundeExakt F (exaktMul u v)) = .subnormal
      ∨ klasse F (rundeExakt F (exaktMul u v)) = .null := by
    unfold rundeExakt
    exact rundeBruch_finite F _ hF (exaktBruch_nenner_pos _) hob
  generalize hka : klasse F a = ka
  generalize hkb : klasse F b = kb
  cases ka <;> cases kb <;>
    first
      | (unfold mul; rw [hka, hkb, klasse_null_bits F _ hmax]
         exact Or.inr (Or.inr rfl))
      | (unfold mul; rw [hka, hkb, ha, hb]; exact hfin)
      | (have hnone : wertExakt F a = none := by unfold wertExakt; rw [hka]
         rw [hnone] at ha; cases ha)
      | (have hnone : wertExakt F b = none := by unfold wertExakt; rw [hkb]
         rw [hnone] at hb; cases hb)

/-- Negation keeps the classification (only the sign bit flips). -/
theorem klasse_neg (F : Format) (a : GBits F) :
    klasse F (neg F a) = klasse F a := by
  cases a with
  | mk s bx fr => unfold neg klasse; rfl

/-- Negation negates the exact value. -/
theorem wertExakt_neg_some (F : Format) (b : GBits F) (v : Exakt)
    (hb : wertExakt F b = some v) :
    wertExakt F (neg F b) = some ⟨-v.zaehler, v.zweierExp⟩ := by
  cases b with
  | mk s bx fr =>
    cases s
    · -- Sign false: negation turns it true.
      have eneg : neg F (⟨false, bx, fr⟩ : GBits F) = ⟨true, bx, fr⟩ := rfl
      rw [eneg]
      have hkn : klasse F (⟨true, bx, fr⟩ : GBits F)
          = klasse F (⟨false, bx, fr⟩ : GBits F) := by
        have h := klasse_neg F (⟨false, bx, fr⟩ : GBits F)
        rwa [eneg] at h
      unfold wertExakt at hb ⊢
      generalize hka : klasse F (⟨false, bx, fr⟩ : GBits F) = ka
      cases ka
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        cases v with
        | mk z e =>
          cases hb
          decide
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        rw [if_neg (by decide : ¬ (false : Bool) = true)] at hb
        rw [if_pos trivial] at ⊢
        cases v with
        | mk z e =>
          cases hb
          have h1 : (-1 : Int) * (fr : Int) = -((1 : Int) * fr) := by omega
          rw [h1]
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        rw [if_neg (by decide : ¬ (false : Bool) = true)] at hb
        rw [if_pos trivial] at ⊢
        cases v with
        | mk z e =>
          cases hb
          have h1 : (-1 : Int) * ((2 ^ (F.p - 1) : Nat) + (fr : Int))
              = -(((1 : Int)) * ((2 ^ (F.p - 1) : Nat) + (fr : Int))) := by omega
          rw [h1]
      · simp only [hka] at hb; cases hb
      · simp only [hka] at hb; cases hb
    · -- Sign true: mirror image.
      have eneg : neg F (⟨true, bx, fr⟩ : GBits F) = ⟨false, bx, fr⟩ := rfl
      rw [eneg]
      have hkn : klasse F (⟨false, bx, fr⟩ : GBits F)
          = klasse F (⟨true, bx, fr⟩ : GBits F) := by
        have h := klasse_neg F (⟨true, bx, fr⟩ : GBits F)
        rwa [eneg] at h
      unfold wertExakt at hb ⊢
      generalize hka : klasse F (⟨true, bx, fr⟩ : GBits F) = ka
      cases ka
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        cases v with
        | mk z e =>
          cases hb
          decide
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        rw [if_pos trivial] at hb
        rw [if_neg (by decide : ¬ (false : Bool) = true)] at ⊢
        cases v with
        | mk z e =>
          cases hb
          have h1 : (1 : Int) * (fr : Int) = -(((-1 : Int)) * fr) := by omega
          rw [h1]
      · simp only [hkn, hka] at ⊢; simp only [hka] at hb
        rw [if_pos trivial] at hb
        rw [if_neg (by decide : ¬ (false : Bool) = true)] at ⊢
        cases v with
        | mk z e =>
          cases hb
          have h1 : (1 : Int) * ((2 ^ (F.p - 1) : Nat) + (fr : Int))
              = -(((-1 : Int)) * ((2 ^ (F.p - 1) : Nat) + (fr : Int))) := by omega
          rw [h1]
      · simp only [hka] at hb; cases hb
      · simp only [hka] at hb; cases hb

/-- Subtraction of finite values with in-range exact difference stays finite. -/
theorem sub_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hob : (exaktBruch (exaktAdd u ⟨-v.zaehler, v.zweierExp⟩)).zaehler.natAbs
      < (exaktBruch (exaktAdd u ⟨-v.zaehler, v.zweierExp⟩)).nenner * 2 ^ F.emax) :
    klasse F (sub F a b) = .normal ∨ klasse F (sub F a b) = .subnormal
      ∨ klasse F (sub F a b) = .null := by
  unfold sub
  exact add_finite F hF a (neg F b) u ⟨-v.zaehler, v.zweierExp⟩ ha
    (wertExakt_neg_some F b v hb) hob

/-! ## Theorems: the signed-zero rule (IEEE 754-2019 §6.3). -/

/-- The sum of two zeros is `-0` exactly when both are `-0`. -/
theorem add_null_null (F : Format) (a b : GBits F)
    (ha : klasse F a = .null) (hb : klasse F b = .null) :
    add F a b = ⟨a.sign && b.sign, 0, 0⟩ := by
  unfold add; rw [ha, hb]

/-- Exact cancellation of a dyadic value leaves numerator zero. -/
theorem exaktAdd_neg_zaehler (u : Exakt) :
    (exaktAdd u ⟨-u.zaehler, u.zweierExp⟩).zaehler = 0 := by
  unfold exaktAdd
  simp only [Int.le_refl, if_true, Int.sub_self]
  rw [Int.neg_mul]; exact Int.add_right_neg _

/-- An exact zero rounds to `+0` (its numerator is not negative). -/
theorem rundeExakt_null (F : Format) (v : Exakt) (hv : v.zaehler = 0) :
    rundeExakt F v = ⟨false, 0, 0⟩ := by
  have hd := exaktBruch_nenner_pos v
  have hz : (exaktBruch v).zaehler = 0 := by
    unfold exaktBruch
    by_cases h : 0 ≤ v.zweierExp
    · rw [if_pos h]; show v.zaehler * _ = 0; rw [hv, Int.zero_mul]
    · rw [if_neg h]; exact hv
  unfold rundeExakt rundeBruch rundeBruchBei
  rw [if_neg (by omega), hz]
  rfl

/-- `x - x = +0` for every finite `x` (zeros included: `(-0) - (-0) = +0`). -/
theorem sub_selbst (F : Format) (a : GBits F)
    (hk : klasse F a = .normal ∨ klasse F a = .subnormal ∨ klasse F a = .null) :
    sub F a a = ⟨false, 0, 0⟩ := by
  unfold sub
  have hkn := klasse_neg F a
  rcases hk with hk | hk | hk
  · have hw : wertExakt F a = some ⟨(if a.sign then (-1 : Int) else 1)
        * ((2 ^ (F.p - 1) : Nat) + (a.frac : Int)),
        (a.bexp : Int) - (F.bias : Int) - ((F.p : Int) - 1)⟩ := by
      unfold wertExakt; rw [hk]
    have hwn := wertExakt_neg_some F a _ hw
    unfold add; rw [hkn, hk, hw, hwn]
    exact rundeExakt_null F _ (exaktAdd_neg_zaehler _)
  · have hw : wertExakt F a = some ⟨(if a.sign then (-1 : Int) else 1) * (a.frac : Int),
        F.emin - ((F.p : Int) - 1)⟩ := by
      unfold wertExakt; rw [hk]
    have hwn := wertExakt_neg_some F a _ hw
    unfold add; rw [hkn, hk, hw, hwn]
    exact rundeExakt_null F _ (exaktAdd_neg_zaehler _)
  · rw [add_null_null F a (neg F a) hk (by rw [hkn]; exact hk)]
    cases a with
    | mk sg bx fr => cases sg <;> rfl

/-- The exact quotient denominator, exposed (definitionally the `let` body). -/
theorem divBruch_nenner (u v : Exakt) : (divBruch u v).nenner
    = v.zaehler.natAbs
      * 2 ^ (v.zweierExp
        - (if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp)).toNat :=
  rfl

/-- Division of finite values by a nonzero finite divisor with in-range
    exact quotient stays finite (and is the rounded exact quotient).
    `0 / 0` is NaN, so the divisor must be nonzero (`hkb`, `hv`). -/
theorem div_finite (F : Format) (hF : 1 ≤ F.emax) (a b : GBits F)
    (u v : Exakt) (ha : wertExakt F a = some u) (hb : wertExakt F b = some v)
    (hkb : klasse F b = .normal ∨ klasse F b = .subnormal)
    (hv : v.zaehler ≠ 0)
    (hob : (divBruch u v).zaehler.natAbs
      < (divBruch u v).nenner * 2 ^ F.emax) :
    klasse F (div F a b) = .normal ∨ klasse F (div F a b) = .subnormal
      ∨ klasse F (div F a b) = .null := by
  have hmax : 0 < F.bexpMax := by
    have hmaxE : F.bexpMax = 2 * F.emax + 1 := rfl
    omega
  have hdD : 0 < (divBruch u v).nenner := by
    rw [divBruch_nenner]
    have h1 : 0 < v.zaehler.natAbs := by omega
    have h2 : 0 < 2 ^ (v.zweierExp
        - (if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp)).toNat :=
      Nat.pow_pos (show 0 < 2 by decide)
    exact Nat.mul_pos h1 h2
  have hfin : klasse F (rundeBruch F (divBruch u v)) = .normal
      ∨ klasse F (rundeBruch F (divBruch u v)) = .subnormal
      ∨ klasse F (rundeBruch F (divBruch u v)) = .null :=
    rundeBruch_finite F _ hF hdD hob
  generalize hka : klasse F a = ka
  cases hkb with
  | inl hkb =>
    cases ka <;>
      first
        | (unfold div; rw [hka, hkb, klasse_null_bits F _ hmax]
           exact Or.inr (Or.inr rfl))
        | (unfold div; rw [hka, hkb, ha, hb]; exact hfin)
        | (have hnone : wertExakt F a = none := by
             unfold wertExakt; simp only [hka]
           rw [hnone] at ha; cases ha)
  | inr hkb =>
    cases ka <;>
      first
        | (unfold div; rw [hka, hkb, klasse_null_bits F _ hmax]
           exact Or.inr (Or.inr rfl))
        | (unfold div; rw [hka, hkb, ha, hb]; exact hfin)
        | (have hnone : wertExakt F a = none := by
             unfold wertExakt; simp only [hka]
           rw [hnone] at ha; cases ha)

/-! ## Witnesses: concrete vectors by `decide`.

  Every vector below is a kernel computation (`decide`/`rfl`-checkable,
  no `native_decide`): the model rounds exactly like IEEE-754 hardware on
  fractions, ties, subnormals and overflow. The subnormal/overflow vectors
  evaluate `2 ^ 1074`-scale naturals through ~1100 structural steps, past
  both default elaborator limits, hence the two options (elaboration-only,
  no soundness content). -/

set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
theorem zeuge_ebits32 : f32.ebits = 8 := by decide

theorem zeuge_ebits64 : f64.ebits = 11 := by decide

theorem zeuge_zehntel64 :
    zuBits f64 (ofRat f64 1 10) = 0x3FB999999999999A := by decide

theorem zeuge_zweiZehntel64 :
    zuBits f64 (ofRat f64 2 10) = 0x3FC999999999999A := by decide

/-- `0.1 + 0.2 = 0.30000000000000004`: the famous `0x3FD3333333333334`. -/
theorem zeuge_add01 :
    zuBits f64 (add f64 (ofRat f64 1 10) (ofRat f64 2 10))
      = 0x3FD3333333333334 := by decide

theorem zeuge_drittel64 :
    zuBits f64 (ofRat f64 1 3) = 0x3FD5555555555555 := by decide

theorem zeuge_drittel32 :
    zuBits f32 (ofRat f32 1 3) = 0x3EAAAAAB := by decide

theorem zeuge_zehntel32 :
    zuBits f32 (ofRat f32 1 10) = 0x3DCCCCCD := by decide

/-- The smallest subnormal binary64 (`2 ^ -1074`) is significand one. -/
theorem zeuge_subnormal64 :
    zuBits f64 (ofRat f64 1 (2 ^ 1074)) = 1 := by decide

theorem zeuge_subKlasse64 :
    klasse f64 (ofRat f64 1 (2 ^ 1074)) = .subnormal := by decide

/-- The smallest subnormal binary32 (`2 ^ -149`). -/
theorem zeuge_subnormal32 :
    zuBits f32 (ofRat f32 1 (2 ^ 149)) = 1 := by decide

/-- Subnormal arithmetic: min + min is the next subnormal. -/
theorem zeuge_subnormalAdd :
    zuBits f64 (add f64 (ofRat f64 1 (2 ^ 1074)) (ofRat f64 1 (2 ^ 1074)))
      = 2 := by decide

/-- Overflow rounds to infinity (`2 * 2 ^ 1023`). -/
theorem zeuge_ueberlauf :
    zuBits f64 (mul f64 (ofInt f64 2) (ofRat f64 ((2 ^ 1023 : Nat) : Int) 1))
      = 0x7FF0000000000000 := by decide

theorem zeuge_ueberlaufKlasse :
    klasse f64
        (mul f64 (ofInt f64 2) (ofRat f64 ((2 ^ 1023 : Nat) : Int) 1))
      = .unendlich := by decide

/-- Tie to even, down: `1 + 2 ^ -53` is halfway between `1` and the next
    double, and the even mantissa (`1.0`) wins. -/
theorem zeuge_tieUnten :
    zuBits f64 (ofRat f64 ((2 ^ 53 + 1 : Nat) : Int) (2 ^ 53))
      = 0x3FF0000000000000 := by decide

/-- Tie to even, up: `1 + 2 ^ -52 + 2 ^ -53` rounds to the even mantissa. -/
theorem zeuge_tieOben :
    zuBits f64 (ofRat f64 ((2 ^ 53 + 3 : Nat) : Int) (2 ^ 53))
      = 0x3FF0000000000002 := by decide

theorem zeuge_nullDurchNull :
    klasse f64 (div f64 (ofInt f64 0) (ofInt f64 0)) = .nan := by decide

theorem zeuge_einsDurchNull :
    klasse f64 (div f64 (ofInt f64 1) (ofInt f64 0)) = .unendlich := by decide

theorem zeuge_divDrittel :
    zuBits f64 (div f64 (ofInt f64 1) (ofInt f64 3))
      = 0x3FD5555555555555 := by decide

theorem zeuge_sub01 :
    zuBits f64 (sub f64 (ofRat f64 2 10) (ofRat f64 1 10))
      = 0x3FB999999999999A := by decide

/-! ### Signed zeros (IEEE 754-2019 §6.3), both widths.

  `nullN`/`nullP` are `-0`/`+0`. Sums of zeros keep `-0` only when both are
  `-0`; exact cancellation is `+0`; products and quotients carry the xor of
  the signs; an underflow to zero keeps the sign of the exact result. -/

/-- `-0` as data. -/
def nullN (F : Format) : GBits F := ⟨true, 0, 0⟩

/-- `+0` as data. -/
def nullP (F : Format) : GBits F := ⟨false, 0, 0⟩

theorem zeuge_nullNplusNullN64 : add f64 (nullN f64) (nullN f64) = nullN f64 := by decide
theorem zeuge_nullNplusNullN32 : add f32 (nullN f32) (nullN f32) = nullN f32 := by decide
theorem zeuge_nullPplusNullN64 : add f64 (nullP f64) (nullN f64) = nullP f64 := by decide
theorem zeuge_nullNplusNullP64 : add f64 (nullN f64) (nullP f64) = nullP f64 := by decide
theorem zeuge_nullNminusNullP64 : sub f64 (nullN f64) (nullP f64) = nullN f64 := by decide
theorem zeuge_nullNminusNullN64 : sub f64 (nullN f64) (nullN f64) = nullP f64 := by decide
theorem zeuge_nullPminusNullP32 : sub f32 (nullP f32) (nullP f32) = nullP f32 := by decide

/-- `x - x = +0` (exact cancellation), here `0.1 - 0.1`. -/
theorem zeuge_xMinusX64 :
    sub f64 (ofRat f64 1 10) (ofRat f64 1 10) = nullP f64 := by decide

/-- `(-x) + x = +0`, here `-(1/3) + 1/3` in binary32. -/
theorem zeuge_negXplusX32 :
    add f32 (ofRat f32 (-1) 3) (ofRat f32 1 3) = nullP f32 := by decide

/-- `-0 + x = x` for nonzero `x` (the zero does not decide the sign). -/
theorem zeuge_nullNplusEins64 :
    add f64 (nullN f64) (ofInt f64 1) = ofInt f64 1 := by decide

theorem zeuge_mulNullNEins64 : mul f64 (nullN f64) (ofInt f64 1) = nullN f64 := by decide
theorem zeuge_mulMinusEinsNullP64 :
    mul f64 (ofInt f64 (-1)) (nullP f64) = nullN f64 := by decide
theorem zeuge_mulNullNNullN32 : mul f32 (nullN f32) (nullN f32) = nullP f32 := by decide
theorem zeuge_divNullNEins64 : div f64 (nullN f64) (ofInt f64 1) = nullN f64 := by decide
theorem zeuge_divEinsMinusInf64 :
    div f64 (ofInt f64 1) ⟨true, f64.bexpMax, 0⟩ = nullN f64 := by decide

/-- Underflow keeps the sign: `-(2^-1074) * 0.5` is an exact tie between
    `-0` and `-2^-1074`; the even significand (zero) wins and stays `-0`. -/
theorem zeuge_unterlaufNeg64 :
    mul f64 (ofRat f64 (-1) (2 ^ 1074)) (ofRat f64 1 2) = nullN f64 := by decide

/-- `0.1 + 0.2` is unaffected (the zero rule touches only zero operands). -/
theorem zeuge_add01_nachNullRegel :
    add f64 (ofRat f64 1 10) (ofRat f64 2 10) = ofRat f64 3 10
      ∨ zuBits f64 (add f64 (ofRat f64 1 10) (ofRat f64 2 10)) = 0x3FD3333333333334 :=
  Or.inr (by decide)

/-- Comparisons: NaN is unordered for `fle` as for `flt`; `-0 <= +0` and
    `+0 <= -0` both hold (equal zeros), `-0 < +0` does not. -/
theorem zeuge_fleNaN : fle f64 (nanQ f64) (nanQ f64) = false := by decide
theorem zeuge_fleNaNrechts : fle f64 (ofInt f64 1) (nanQ f64) = false := by decide
theorem zeuge_fleNullen : fle f64 (nullN f64) (nullP f64) = true
    ∧ fle f64 (nullP f64) (nullN f64) = true ∧ flt f64 (nullN f64) (nullP f64) = false := by
  decide

/-! `CUTS:` what is not proved here.

  - No single "nearest float" theorem: rounding correctness is proved at
    the integer significand level (`rundeInt_fall/steig/tie/monoton`) and
    as finite-in-range preservation (`rundeBruch_finite`, the six op and
    conversion theorems). The assembly into "the result is a nearest
    representable value, ties to even" over all `GBits` is not stated.
  - `findeExp` upper bound (`n < d * 2 ^ (E + 1)`) not proved; only the
    non-negative lower half needed for finiteness (`findeExp_unten`).
  - Overflow-boundary exactness (values within half an ulp of max-finite)
    and the deep-underflow shortcut (`E < emin - p` rounds to zero, the
    exact tie going to even) rest on the algorithm plus witnesses and the
    differential check, not on analytic theorems.
  - Signed zeros follow IEEE 754-2019 §6.3 (since the lane after 166):
    `add` of two zeros is `-0` exactly for `(-0) + (-0)`, every other exact
    zero sum is `+0` (round-to-nearest), `mul`/`div` carry the xor of the
    signs, underflow keeps the sign of the exact result (witnesses
    `zeuge_nullN*`, `zeuge_xMinusX64`, `zeuge_unterlaufNeg64`). Other
    rounding modes (where `x - x = -0` under round-down) are not modelled.
  - NaN payloads are unspecified: computed NaNs are the canonical `nanQ`,
    propagated NaNs keep their input bits; no quiet-bit discipline.
  - `ofRat`/`divBruch` with denominator zero is NaN by definition.
  - No theorems about `flt`/`fle` (irreflexivity, totality on finite
    values) and none about `wf` preservation.
  - binary32/binary64 only; no f16, no 80-bit, no decimal.
  - No connection to the `Float`-based model (`Semantik.lean`
    `gleitRechne`/`gleitPasst`) yet -- a later task switches the model.
  - The `set_option` thresholds above are elaboration-only.
-/

#print axioms Gabbro.Grammatik.Gleitkomma.rundeBruch_finite
#print axioms Gabbro.Grammatik.Gleitkomma.add_finite
#print axioms Gabbro.Grammatik.Gleitkomma.sub_finite
#print axioms Gabbro.Grammatik.Gleitkomma.mul_finite
#print axioms Gabbro.Grammatik.Gleitkomma.div_finite
#print axioms Gabbro.Grammatik.Gleitkomma.ofInt_finite
#print axioms Gabbro.Grammatik.Gleitkomma.ofRat_finite
#print axioms Gabbro.Grammatik.Gleitkomma.rundeInt_monoton
#print axioms Gabbro.Grammatik.Gleitkomma.rundeInt_tie
#print axioms Gabbro.Grammatik.Gleitkomma.wertExakt_neg_some
#print axioms Gabbro.Grammatik.Gleitkomma.findeExp_unten
#print axioms Gabbro.Grammatik.Gleitkomma.zeuge_add01
#print axioms Gabbro.Grammatik.Gleitkomma.sub_selbst
#print axioms Gabbro.Grammatik.Gleitkomma.add_null_null
#print axioms Gabbro.Grammatik.Gleitkomma.zeuge_nullNplusNullN64

end Gabbro.Grammatik.Gleitkomma
