/- Part 3 of 3 of `Gleitkomma` (split by instrumente/teile/lean-teilen.py; the umbrella `Gleitkomma.lean` imports all parts). -/
import Grammatik.Bausteine.Gleitkomma.Gleitkomma.T2

namespace Gabbro.Grammatik.Gleitkomma

set_option maxRecDepth 100000
set_option exponentiation.threshold 2048

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
    values). `wf` preservation of every op is proved in
    `GleitkommaBits.lean` (`add_wf` ... `rundeBruch_wf`).
  - binary32/binary64 only; no f16, no 80-bit, no decimal.
  - The semantics computes with this model since 2026-09-14 (Typen.lean,
    Semantik.lean).
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
