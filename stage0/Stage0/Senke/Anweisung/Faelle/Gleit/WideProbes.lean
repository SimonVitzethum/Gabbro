/- Accepted computed-wide conversion hooks and their canonical rounding outcomes. -/
module
public import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben
public import Stage0.Senke.Ausdruck.Gleit.Wide.Range
@[expose] public section

namespace Gabbro.Stage0.Senke.WideFloatProbe
open Gabbro.Grammatik Gleitkomma Runner.IR FloatProbe ControlProbe
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The input is bound before conversion, so the literal shortcut cannot
    discharge these fixtures. Both comparisons inspect the rounded result. -/
def samples : List (String × Int × Int × Nat) :=
  [("wide-float-tie-even", 2 ^ 80 + 2 ^ 27, 2 ^ 80, 7),
   ("wide-float-sticky", 2 ^ 80 + 2 ^ 27 + 1, 2 ^ 80 + 2 ^ 28, 7),
   ("wide-float-negative", -(2 ^ 80 + 2 ^ 27 + 1), -(2 ^ 80 + 2 ^ 28), 7),
   ("wide-float-tie-carry", 2 ^ 81 - 2 ^ 27, 2 ^ 81, 7),
   ("wide-float-max-finite", 2 ^ 1024 - 2 ^ 971, 2 ^ 1024 - 2 ^ 971, 7),
   ("wide-float-overflow-tie", 2 ^ 1024 - 2 ^ 970, 0, 107),
   ("wide-float-overflow", 2 ^ 1024, 0, 107)]

def images : List (String × Except String (List Runner.B) × Nat) :=
  samples.map fun (name, n, rounded, exit) =>
    (name, blockImageOf (FloatArithmeticProbe.hookConversion n (rounded, 1)
      (-(2 ^ 1025), 1) (2 ^ 1025, 1)), exit)

/-- Values smaller than a word, including zero, still compile when their
    declared interval needs several words. No runtime width is assumed. -/
def smallInWide (n : Int) (lower : -(2 ^ 127) ≤ n) (upper : n ≤ 2 ^ 127) : Body :=
  .bind (.widen lower upper (.lit n))
    (.floatOf (.var .here) (-(2 ^ 129), 1) (2 ^ 129, 1)
      (.floatLit (n, 1) (-(2 ^ 129), 1) (2 ^ 129, 1)
        (.cons (.ite
          (.and (.flle (.var (.there .here)) (.var .here))
            (.flle (.var .here) (.var (.there .here))))
          (returnBlock 7 (by decide) (by decide))
          (returnBlock 41 (by decide) (by decide))) .nil)))

def smallImages : List (String × Except String (List Runner.B) × Nat) :=
  [("wide-float-small-zero", blockImageOf (smallInWide 0 (by decide) (by decide)), 7),
   ("wide-float-small-positive", blockImageOf (smallInWide 37 (by decide) (by decide)), 7),
   ("wide-float-small-negative", blockImageOf (smallInWide (-37) (by decide) (by decide)), 7)]

theorem wide_float_images_zeuge :
    images.length = 7 ∧ images.all (fun x => x.2.1.isOk) = true ∧
    smallImages.length = 3 ∧ smallImages.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- These are the source model's results, independently of image execution. -/
theorem wide_float_rounding_zeuge :
    ofInt f64 (2 ^ 80 + 2 ^ 27) = ofInt f64 (2 ^ 80) ∧
    ofInt f64 (2 ^ 80 + 2 ^ 27 + 1) = ofInt f64 (2 ^ 80 + 2 ^ 28) ∧
    ofInt f64 (-(2 ^ 80 + 2 ^ 27 + 1)) = ofInt f64 (-(2 ^ 80 + 2 ^ 28)) ∧
    ofInt f64 (2 ^ 81 - 2 ^ 27) = ofInt f64 (2 ^ 81) ∧
    computedFloatRangeReject (-(2 ^ 1025), 1) (2 ^ 1025, 1)
      (ofInt f64 (2 ^ 1024 - 2 ^ 970)) = true := by
  decide +kernel

section GenericWitness
variable [Kern] {Decl : Deklaration} (L : Lay Decl)

def operand : Expr Decl [.int (-(2 ^ 80)) (2 ^ 80)] [] (.int (-(2 ^ 80)) (2 ^ 80)) :=
  .var .here

/-- A nonempty multiword interval jointly inhabits emission and the generic
    compiler-hook theorem, including four reserved slots. This is a witness
    of that theorem, not an extra trusted producer hypothesis. -/
theorem computedFloatOfE_wide_ok_zeuge :
    (computedFloatOfE L f64 operand 12 4).isSome = true ∧
    ∀ (σ : World Decl) (ρ : Env Decl [.int (-(2 ^ 80)) (2 ^ 80)])
      (m : Runner.Mem) (pc fp : Runner.W) (K top : Nat) (code : List II),
      LayIn L → computedFloatOfE L f64 operand 12 4 = some (code, top) →
      top ≤ K → Pre L m pc fp K 12 code ρ (fun m => WeltAt m L σ) 4 →
      Ok m pc fp K 12 code
        (· = BitVec.ofNat 64 (zuBits f64 (ofInt f64 (ρ.get .here).n))) := by
  constructor
  · decide +kernel
  · intro σ ρ m pc fp K top code lay emitted fits pre
    exact computedFloatOfE_ok (σ₀ := σ) (σ := σ) emitted pre fits lay rfl (fun _ h => h)

end GenericWitness

/-- Every value above the representable normal range is rejected by the
    same compiled range template, even with infinite declared endpoints. -/
theorem wide_float_overflow_zeuge :
    ∀ z ∈ [2 ^ 1024 - 2 ^ 970, 2 ^ 1024, -(2 ^ 1024)],
      computedFloatRangeReject (-(2 ^ 1025), 1) (2 ^ 1025, 1) (ofInt f64 z) = true := by
  decide +kernel

#print axioms wide_float_images_zeuge
#print axioms computedFloatOfE_wide_ok_zeuge
#print axioms wide_float_overflow_zeuge
end Gabbro.Stage0.Senke.WideFloatProbe
