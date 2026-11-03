/- Binary64 multiplication with kernel special cases and an exact Nat product.
   The 106 product bits remain unbounded until the shared rounding replay.
   Zero signs and NaN payloads are resolved before this finite computation. -/
module
public import Stage0.Senke.Gleit.Compose
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma
variable [Runner.IR.Kern]

/-- Multiplication's special cases in kernel priority order. -/
def softMulSpecial (a b : GFloat) : Option GFloat :=
  match klasse f64 a, klasse f64 b with
  | .nan, _ => some a
  | _, .nan => some b
  | .unendlich, .unendlich => some ⟨a.sign != b.sign, 2047, 0⟩
  | .unendlich, .null => some (nanQ f64)
  | .null, .unendlich => some (nanQ f64)
  | .unendlich, _ => some ⟨a.sign != b.sign, 2047, 0⟩
  | _, .unendlich => some ⟨a.sign != b.sign, 2047, 0⟩
  | .null, _ => some ⟨a.sign != b.sign, 0, 0⟩
  | _, .null => some ⟨a.sign != b.sign, 0, 0⟩
  | _, _ => none

/-- The exact magnitude uses the adder's unpacked significands. -/
def softMulProduct (a b : GFloat) : Nat :=
  softSig a.bexp a.frac * softSig b.bexp b.frac

/-- Each effective index contributes its unbiased significand scale. -/
def softMulExponent (a b : GFloat) : Int :=
  ((max a.bexp 1 : Nat) : Int) + ((max b.bexp 1 : Nat) : Int) - 2150

/-- Silence of the dispatcher means both inputs are nonzero and finite. -/
theorem softMulSpecial_none (a b : GFloat) (h : softMulSpecial a b = none) :
    (klasse f64 a = .normal ∨ klasse f64 a = .subnormal) ∧
      (klasse f64 b = .normal ∨ klasse f64 b = .subnormal) := by
  cases ca : klasse f64 a <;> cases cb : klasse f64 b <;>
    simp_all [softMulSpecial]

/-- Nonzero finite decoding has a uniform significand and scale. -/
theorem softMul_operand (a : GFloat)
    (finite : klasse f64 a = .normal ∨ klasse f64 a = .subnormal) :
    wertExakt f64 a = some
      ⟨if a.sign then -(softSig a.bexp a.frac : Int) else softSig a.bexp a.frac,
        ((max a.bexp 1 : Nat) : Int) - 1075⟩ := by
  have notMax : a.bexp ≠ 2047 := by
    intro e
    rcases finite with finite | finite <;> by_cases z : a.frac = 0 <;>
      simp [klasse, show f64.bexpMax = 2047 from rfl, e, z] at finite
  by_cases ez : a.bexp = 0
  · have nonzero : a.frac ≠ 0 := by
      intro z
      rcases finite with finite | finite <;>
        simp [klasse, ez, z, show f64.bexpMax = 2047 from rfl] at finite
    rw [show a = ⟨a.sign, 0, a.frac⟩ by cases a; simp_all,
      softWertExakt_subnormal _ _ nonzero]
    cases a.sign <;> simp [softSig, f64, Format.emin]
  · rw [softWertExakt_normal a.sign a.bexp a.frac ez notMax]
    have index : max a.bexp 1 = a.bexp := Nat.max_eq_left (by omega)
    cases a.sign <;> simp [softSig, ez, index, f64, Format.bias] <;> congr 1 <;> omega

/-- The finite implementation multiplies two Nat significands exactly;
    only its final signed dyadic value is passed to canonical rounding. -/
def softMulCore (a b : GFloat) : GFloat :=
  match softMulSpecial a b with
  | some r => r
  | none => rundeExakt f64
      ⟨if a.sign != b.sign then -(softMulProduct a b : Int) else softMulProduct a b,
        softMulExponent a b⟩

/-- The kernel decomposes into the same special dispatcher and exact product. -/
theorem softMul_dispatch (a b : GFloat) :
    mul f64 a b = match softMulSpecial a b with
      | some r => r
      | none => match wertExakt f64 a, wertExakt f64 b with
        | some u, some v => rundeExakt f64 (exaktMul u v)
        | _, _ => nanQ f64 := by
  cases ca : klasse f64 a <;> cases cb : klasse f64 b <;>
    simp only [softMulSpecial, mul, ca, cb, show f64.bexpMax = 2047 from rfl] <;> rfl

/-- The explicit Nat computation equals kernel multiplication on all triples. -/
theorem softMulCore_model (a b : GFloat) : softMulCore a b = mul f64 a b := by
  rw [softMul_dispatch]
  cases h : softMulSpecial a b with
  | some r => simp only [softMulCore, h]
  | none =>
    obtain ⟨fa, fb⟩ := softMulSpecial_none a b h
    rw [softMulCore, h, softMul_operand a fa, softMul_operand b fb]
    apply congrArg (rundeExakt f64)
    unfold exaktMul
    have exponent : softMulExponent a b =
        (((max a.bexp 1 : Nat) : Int) - 1075) + (((max b.bexp 1 : Nat) : Int) - 1075)
        := by
      unfold softMulExponent
      omega
    rw [exponent]
    cases a.sign <;> cases b.sign <;> simp [softMulProduct, Int.natCast_mul]

/-- Word-level multiplication reuses canonical decoding and encoding. -/
def softMul (a b : UInt64) : UInt64 :=
  gToU64 (softMulCore (u64ToG a) (u64ToG b))

/-- No word input is excluded, including NaN payloads and signed zeros. -/
theorem softMul_model (a b : UInt64) :
    u64ToG (softMul a b) = mul f64 (u64ToG a) (u64ToG b) := by
  have hw := mul_wf f64 f64_p (u64ToG a) (u64ToG b)
    (ausBits_f64_wf _) (ausBits_f64_wf _)
  unfold softMul
  rw [softMulCore_model]
  exact u64ToG_gToU64 _ hw (zuBits_f64_lt _ hw)

/-- Canonical output bits, as required by the emitted routine simulation. -/
theorem softMul_bits (a b : UInt64) :
    (softMul a b).toNat = zuBits f64 (mul f64 (u64ToG a) (u64ToG b)) := by
  have hw := mul_wf f64 f64_p (u64ToG a) (u64ToG b)
    (ausBits_f64_wf _) (ausBits_f64_wf _)
  unfold softMul
  rw [softMulCore_model]
  exact gToU64_toNat _ hw (zuBits_f64_lt _ hw)

/-- The finite routine computes precisely the untruncated Nat product. -/
theorem softMul_product (a b : GFloat) (h : softMulSpecial a b = none) :
    softMulCore a b = rundeExakt f64
      ⟨if a.sign != b.sign then -(softMulProduct a b : Int) else softMulProduct a b,
        softMulExponent a b⟩ := by
  rw [softMulCore, h]

/-- The product occupies at most 106 bits, including two subnormals. -/
theorem softMulProduct_lt (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b) :
    softMulProduct a b < 2 ^ 106 := by
  have sig (g : GFloat) (hg : wf f64 g) : softSig g.bexp g.frac < 2 ^ 53 := by
    have frac := hg.2
    change g.frac < 2 ^ 52 at frac
    unfold softSig
    split <;> omega
  calc
    softMulProduct a b < (2 : Nat) ^ 53 * 2 ^ 53 :=
      Nat.mul_lt_mul'' (sig a ha) (sig b hb)
    _ = 2 ^ 106 := by decide

/-- Normal, rounded, subnormal and invalid products plus signed special cases. -/
theorem softMul_model_zeuge :
    softMul 4609434218613702656 4611686018427387904 = 4613937818241073152 ∧
    softMul 4607182418800017409 4607182418800017409 = 4607182418800017410 ∧
    softMul 4503599627370496 4602678819172646912 = 2251799813685248 ∧
    softMul 0 9218868437227405312 = 9218868437227405313 ∧
    softMul 9223372036854775808 4607182418800017408 = 9223372036854775808 ∧
    softMul 18442240474082181120 13830554455654793216 = 9218868437227405312 ∧
    softMul 18442240474082181127 9218868437227405321 = 18442240474082181127 := by
  decide +kernel

#print axioms softMul_model
#print axioms softMul_bits
#print axioms softMul_product
#print axioms softMulProduct_lt
#print axioms softMul_model_zeuge
end Gabbro.Stage0.Senke
