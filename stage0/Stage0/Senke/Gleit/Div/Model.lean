/- Binary64 division: kernel special cases and an exact rational continuation.
   Operand decoding is shared with multiplication; signs stay outside Nat division. -/
module
public import Stage0.Senke.Gleit.Mul.FiniteModel
public import Stage0.Senke.Gleit.Div.Quotient
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- Kernel priority, including both invalid ratios and xor-signed results. -/
def softDivSpecial (a b : GFloat) : Option GFloat :=
  match klasse f64 a, klasse f64 b with
  | .nan, _ => some a
  | _, .nan => some b
  | .unendlich, .unendlich => some (nanQ f64)
  | .unendlich, _ => some ⟨a.sign != b.sign, 2047, 0⟩
  | _, .unendlich => some ⟨a.sign != b.sign, 0, 0⟩
  | .null, .null => some (nanQ f64)
  | _, .null => some ⟨a.sign != b.sign, 2047, 0⟩
  | .null, _ => some ⟨a.sign != b.sign, 0, 0⟩
  | _, _ => none

theorem softDivSpecial_none (a b : GFloat) (h : softDivSpecial a b = none) :
    (klasse f64 a = .normal ∨ klasse f64 a = .subnormal) ∧
      (klasse f64 b = .normal ∨ klasse f64 b = .subnormal) := by
  cases ca : klasse f64 a <;> cases cb : klasse f64 b <;>
    simp_all [softDivSpecial]

/-- The exact quotient before rounding, with the shared finite decoder. -/
def softDivFraction (a b : GFloat) : Bruch :=
  divBruch
    ⟨if a.sign then -(softSig a.bexp a.frac : Int) else softSig a.bexp a.frac,
      ((max a.bexp 1 : Nat) : Int) - 1075⟩
    ⟨if b.sign then -(softSig b.bexp b.frac : Int) else softSig b.bexp b.frac,
      ((max b.bexp 1 : Nat) : Int) - 1075⟩

def softDivCore (a b : GFloat) : GFloat :=
  match softDivSpecial a b with
  | some r => r
  | none => rundeBruch f64 (softDivFraction a b)

/-- Division by zero is decided before forming the finite rational. The
    class premises ensure that a subnormal numerator is actually nonzero. -/
theorem softDiv_dispatch (a b : GFloat) :
    div f64 a b = match softDivSpecial a b with
      | some r => r
      | none => match wertExakt f64 a, wertExakt f64 b with
        | some u, some v => rundeBruch f64 (divBruch u v)
        | _, _ => nanQ f64 := by
  cases ca : klasse f64 a <;> cases cb : klasse f64 b <;>
    simp only [softDivSpecial, div, ca, cb, wertExakt]
  all_goals first
    | rfl
    | (have positive := softMulSig_positive a (by first | exact Or.inl ca | exact Or.inr ca)
       have decoded := softMul_operand a (by first | exact Or.inl ca | exact Or.inr ca)
       rw [decoded]
       dsimp only
       have nz : (if a.sign then -(softSig a.bexp a.frac : Int)
           else softSig a.bexp a.frac) ≠ 0 := by cases a.sign <;> simp_all
       simp only [beq_eq_false_iff_ne.mpr nz, Bool.false_eq_true, ite_false]
       rfl)

/-- The rational continuation is exactly the existing kernel operation. -/
theorem softDivCore_model (a b : GFloat) : softDivCore a b = div f64 a b := by
  rw [softDiv_dispatch]
  cases h : softDivSpecial a b with
  | some r => simp only [softDivCore, h]
  | none =>
    obtain ⟨fa, fb⟩ := softDivSpecial_none a b h
    rw [softDivCore, h, softMul_operand a fa, softMul_operand b fb]
    rfl

/-- Total word entry, including NaN payloads, infinities and signed zeros. -/
def softDiv (a b : UInt64) : UInt64 :=
  gToU64 (softDivCore (u64ToG a) (u64ToG b))

theorem softDiv_model (a b : UInt64) :
    u64ToG (softDiv a b) = div f64 (u64ToG a) (u64ToG b) := by
  have hw := div_wf f64 f64_p (u64ToG a) (u64ToG b)
    (ausBits_f64_wf _) (ausBits_f64_wf _)
  unfold softDiv
  rw [softDivCore_model]
  exact u64ToG_gToU64 _ hw (zuBits_f64_lt _ hw)

theorem softDiv_bits (a b : UInt64) :
    (softDiv a b).toNat = zuBits f64 (div f64 (u64ToG a) (u64ToG b)) := by
  have hw := div_wf f64 f64_p (u64ToG a) (u64ToG b)
    (ausBits_f64_wf _) (ausBits_f64_wf _)
  unfold softDiv
  rw [softDivCore_model]
  exact gToU64_toNat _ hw (zuBits_f64_lt _ hw)

/-- Exact, rounded, subnormal, zero-divisor and invalid results. -/
theorem softDiv_model_zeuge :
    softDiv 4613937818241073152 4611686018427387904 = 4609434218613702656 ∧
    softDiv 4607182418800017408 4613937818241073152 = 4599676419421066581 ∧
    softDiv 4503599627370496 4611686018427387904 = 2251799813685248 ∧
    softDiv 4607182418800017408 0 = 9218868437227405312 ∧
    softDiv 0 0 = 9218868437227405313 ∧
    softDiv 9223372036854775808 4607182418800017408 = 9223372036854775808 ∧
    softDiv 4607182418800017408 18442240474082181120 = 9223372036854775808 ∧
    softDiv 18442240474082181127 9218868437227405321 = 18442240474082181127 := by
  decide +kernel

#print axioms softDivCore_model
#print axioms softDiv_model
#print axioms softDiv_bits
#print axioms softDiv_model_zeuge
end Gabbro.Stage0.Senke
