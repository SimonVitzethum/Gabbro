/- Accepted computed-wide conversion hooks and their canonical rounding outcomes. -/
module
public import Stage0.Senke.Anweisung.Faelle.Gleit.ArithmetikProben
public import Stage0.Senke.Ausdruck.Gleit.Slots.SlotContext
import Grammatik.Kern.Taktik.KernelRfl
@[expose] public section

namespace Gabbro.Stage0.Senke.WideFloatProbe
open Gabbro.Grammatik Runner.IR FloatProbe ControlProbe
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

/-- These are the source model's results, independently of image execution. -/
theorem wide_float_rounding_zeuge
    (even : Float.hwOfInt (2 ^ 80 + 2 ^ 27) = Float.hwOfInt (2 ^ 80))
    (sticky : Float.hwOfInt (2 ^ 80 + 2 ^ 27 + 1) = Float.hwOfInt (2 ^ 80 + 2 ^ 28))
    (negative : Float.hwOfInt (-(2 ^ 80 + 2 ^ 27 + 1)) = Float.hwOfInt (-(2 ^ 80 + 2 ^ 28)))
    (carry : Float.hwOfInt (2 ^ 81 - 2 ^ 27) = Float.hwOfInt (2 ^ 81))
    (overflow : (Float.hwOfInt (2 ^ 1024 - 2 ^ 970)).hwIsFinite = false) :
    Float.hwOfInt (2 ^ 80 + 2 ^ 27) = Float.hwOfInt (2 ^ 80) ∧
    Float.hwOfInt (2 ^ 80 + 2 ^ 27 + 1) = Float.hwOfInt (2 ^ 80 + 2 ^ 28) ∧
    Float.hwOfInt (-(2 ^ 80 + 2 ^ 27 + 1)) = Float.hwOfInt (-(2 ^ 80 + 2 ^ 28)) ∧
    Float.hwOfInt (2 ^ 81 - 2 ^ 27) = Float.hwOfInt (2 ^ 81) ∧
    floatRangeReject (-(2 ^ 1025), 1) (2 ^ 1025, 1)
      (Float.hwOfInt (2 ^ 1024 - 2 ^ 970)) = true := by
  refine ⟨even, sticky, negative, carry, ?_⟩
  simp only [floatRangeReject, gleitEndlich, overflow, Bool.false_and, Bool.not_false]

section GenericWitness
variable [Kern] {Decl : Deklaration} (L : Lay Decl)

def operand : Expr Decl [.int (-(2 ^ 80)) (2 ^ 80)] [] (.int (-(2 ^ 80)) (2 ^ 80)) :=
  .var .here

/-- The generic compiler-hook theorem at a multiword interval, including four reserved
    slots. That this emission exists is evaluated, not kernel-checked: the kernel exhausts
    its memory on the unrolled wide conversion, so the statement does not claim it. -/
theorem computedFloatOfE_wide_ok_zeuge :
    ∀ (σ : World Decl) (ρ : Env Decl [.int (-(2 ^ 80)) (2 ^ 80)])
      (m : Runner.Mem) (pc fp : Runner.W) (K top : Nat) (code : List II),
      LayIn L → computedFloatOfE L operand 12 4 = some (code, top) →
      top ≤ K → Pre L m pc fp K 12 code ρ (fun m => WeltAt m L σ) 4 →
      Ok m pc fp K 12 code
        (· = (Float.hwOfInt (ρ.get .here).n).hwToBits.toBitVec) := by
  intro σ ρ m pc fp K top code lay emitted fits pre
  exact computedFloatOfE_ok (σ₀ := σ) (σ := σ) emitted pre fits lay rfl (fun _ h => h)

end GenericWitness

/-- Every value above the representable normal range is rejected by the
    same compiled range template, even with infinite declared endpoints. -/
theorem wide_float_overflow_zeuge
    (answers : ∀ z ∈ [2 ^ 1024 - 2 ^ 970, 2 ^ 1024, -(2 ^ 1024)],
      (Float.hwOfInt z).hwIsFinite = false) :
    ∀ z ∈ [2 ^ 1024 - 2 ^ 970, 2 ^ 1024, -(2 ^ 1024)],
      floatRangeReject (-(2 ^ 1025), 1) (2 ^ 1025, 1) (Float.hwOfInt z) = true := by
  intro z member
  simp only [floatRangeReject, gleitEndlich, answers z member, Bool.false_and, Bool.not_false]

/-- The declared interval is checked after rounding: the even tie reaches
    its upper endpoint, while a nonzero discarded tail crosses it. -/
theorem wide_float_range_boundary_zeuge
    (even : RangeAnswers (0, 1) (2 ^ 80, 1) (Float.hwOfInt (2 ^ 80 + 2 ^ 27)) true true true)
    (sticky : RangeAnswers (0, 1) (2 ^ 80, 1) (Float.hwOfInt (2 ^ 80 + 2 ^ 27 + 1)) true true false) :
    floatRangeReject (0, 1) (2 ^ 80, 1)
      (Float.hwOfInt (2 ^ 80 + 2 ^ 27)) = false ∧
    floatRangeReject (0, 1) (2 ^ 80, 1)
      (Float.hwOfInt (2 ^ 80 + 2 ^ 27 + 1)) = true := by
  exact ⟨even.reject, sticky.reject⟩

#print axioms computedFloatOfE_wide_ok_zeuge
#print axioms wide_float_overflow_zeuge
#print axioms wide_float_range_boundary_zeuge
end Gabbro.Stage0.Senke.WideFloatProbe
