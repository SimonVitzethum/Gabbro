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

/-! `CUTS:` skeleton only -- classification, exact values, rounding, ops,
  theorems and witnesses follow in later commits. -/

end Gabbro.Grammatik.Gleitkomma
