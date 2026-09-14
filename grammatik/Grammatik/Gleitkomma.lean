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
    `(-1)^s * frac * 2^(emin-(p-1))`, zero `0`. -/
def wertExakt (F : Format) (g : GBits F) : Option Exakt :=
  match klasse F g with
  | .normal =>
    let m : Int := (2 ^ (F.p - 1) : Nat) + (g.frac : Int)
    let s : Int := if g.sign then -1 else 1
    some ⟨s * m, (g.bexp : Int) - (F.bias : Int) - ((F.p : Int) - 1)⟩
  | .subnormal =>
    let s : Int := if g.sign then -1 else 1
    some ⟨s * (g.frac : Int), F.emin - ((F.p : Int) - 1)⟩
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

/-- Rounding from an exact dyadic value (the `add` / `sub` / `mul` path). -/
def rundeExakt (F : Format) (v : Exakt) : GBits F :=
  if 0 ≤ v.zweierExp then
    rundeBruch F ⟨v.zaehler * (2 ^ v.zweierExp.toNat : Nat), 1⟩
  else
    rundeBruch F ⟨v.zaehler, 2 ^ (-v.zweierExp).toNat⟩

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
    (NaN propagation, `inf + -inf = NaN`, `inf + finite = inf`). -/
def add (F : Format) (a b : GBits F) : GBits F :=
  match klasse F a, klasse F b with
  | .nan, _ => a
  | _, .nan => b
  | .unendlich, .unendlich => if a.sign == b.sign then a else nanQ F
  | .unendlich, _ => a
  | _, .unendlich => b
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
    | some u, some v =>
      let m := if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp
      let na : Nat := u.zaehler.natAbs * 2 ^ (u.zweierExp - m).toNat
      let da : Nat := v.zaehler.natAbs * 2 ^ (v.zweierExp - m).toNat
      let num : Int := if (u.zaehler < 0) != (v.zaehler < 0) then -(na : Int) else na
      rundeBruch F ⟨num, da⟩
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

/-- Non-strict comparison (NaN still unordered). -/
def fle (F : Format) (a b : GBits F) : Bool := !flt F b a

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

end Gabbro.Grammatik.Gleitkomma
