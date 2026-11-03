/- The canonical decoded source sum and the actual aligned routine word. -/
module
public import Stage0.Senke.Gleit.Normal.SourceBounds
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

private theorem decodedFinite (a : GFloat) (u : Exakt)
    (hu : wertExakt f64 a = some u) : a.bexp ≠ 2047 := by
  intro maximum
  have absent : wertExakt f64 a = none := by
    unfold wertExakt klasse
    rw [show f64.bexpMax = 2047 from rfl, maximum]
    by_cases zero : a.frac = 0 <;> simp [zero]
  rw [absent] at hu
  cases hu

private theorem decodedNonzero (a : GFloat) (u : Exakt)
    (hu : wertExakt f64 a = some u) (nonzero : a.bexp ≠ 0 ∨ a.frac ≠ 0) :
    u = ⟨if a.sign then -(softSig a.bexp a.frac : Int) else (softSig a.bexp a.frac : Int),
      (max a.bexp 1 : Int) - 1075⟩ := by
  have finite := decodedFinite a u hu
  by_cases zero : a.bexp = 0
  · have fraction : a.frac ≠ 0 := by rcases nonzero with h | h <;> omega
    have value := softWertExakt_subnormal a.sign a.frac fraction
    have fields : a = ⟨a.sign, 0, a.frac⟩ := by cases a; simp_all
    rw [fields, value] at hu
    have same := Option.some.inj hu
    subst u
    simp only [softSig, zero, ite_true, Nat.max_eq_right (by omega : a.bexp ≤ 1)]
    cases a.sign <;> rfl
  · have value := softWertExakt_normal a.sign a.bexp a.frac zero finite
    rw [value] at hu
    have same := Option.some.inj hu
    subst u
    simp only [softSig, zero, ite_false, Nat.max_eq_left (by omega : 1 ≤ a.bexp)]
    cases a.sign <;> simp <;> congr 1 <;> omega

private theorem roundAddZero (s : Bool) (n : Nat) (e : Int) (positive : 0 < n) :
    rundeExakt f64 (exaktAdd ⟨if s then -(n : Int) else (n : Int), e⟩ ⟨0, 0⟩) =
      rundeExakt f64 ⟨if s then -(n : Int) else (n : Int), e⟩ := by
  rw [floatAdd_align]
  by_cases below : e ≤ 0
  · simp only [if_pos below, zero_mul, add_zero]
  · simp only [if_neg below, sub_zero, add_zero]
    have numerator : (if s then -(n : Int) else (n : Int)) * (2 ^ e.toNat : Nat) =
        if s then -((n * 2 ^ e.toNat : Nat) : Int) else (n * 2 ^ e.toNat : Nat) := by
      cases s <;> simp
    rw [numerator]
    have result := softRound_signed_mul_pow s n e.toNat 0 positive
    have scale : (0 : Int) + (e.toNat : Int) = e := by omega
    rwa [scale] at result

/-- Canonical source-sum link. Both operands are the kernel's actual decoded
    values. The routine's aligned word may discard arbitrarily many bits,
    but applying its sign and guard scale preserves canonical rounding of
    `exaktAdd u v`. Zero operands keep their kernel exponent zero. -/
theorem routineSource_sum (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (u v : Exakt) (hu : wertExakt f64 a = some u) (hv : wertExakt f64 b = some v)
    (order : floatMag b ≤ floatMag a) :
    rundeExakt f64 (exaktAdd u v) =
      rundeExakt f64
        ⟨if a.sign then -((routineDirectionalWord (BitVec.ofNat 64 (zuBits f64 a))
            (BitVec.ofNat 64 (zuBits f64 b))).toNat : Int)
          else ((routineDirectionalWord (BitVec.ofNat 64 (zuBits f64 a))
            (BitVec.ofNat 64 (zuBits f64 b))).toNat : Int),
          (max a.bexp 1 : Int) - 1078⟩ := by
  let l := softSig a.bexp a.frac
  let r := softSig b.bexp b.frac
  let e := max a.bexp 1
  let f := max b.bexp 1
  have lb : l < 2 ^ 53 := by dsimp only [l]; unfold softSig; split <;> have := ha.2 <;> omega
  have rb : r < 2 ^ 53 := by dsimp only [r]; unfold softSig; split <;> have := hb.2 <;> omega
  have indices := routineOrder_indices a b ha hb order
  obtain ⟨equal, different⟩ := routineSource_order a b ha hb order
  have data := softAlignedMagnitude_bounds a.sign b.sign l r e f lb rb
    (by dsimp only [f]; omega) indices equal different
  rw [routineDirectionalWord_canonical a b ha hb order]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show
    softAlignedMagnitude a.sign b.sign l r (e - f) < 2 ^ 64 by have := data.2.2.1; omega)]
  by_cases azero : a.bexp = 0 ∧ a.frac = 0
  · have bzero : b.bexp = 0 ∧ b.frac = 0 := by
      unfold floatMag at order
      rw [azero.1, azero.2] at order
      omega
    have ua : u = ⟨0, 0⟩ := by
      have fields : a = ⟨a.sign, 0, 0⟩ := by cases a; simp_all
      rw [fields, softWertExakt_null] at hu
      exact (Option.some.inj hu).symm
    have vb : v = ⟨0, 0⟩ := by
      have fields : b = ⟨b.sign, 0, 0⟩ := by cases b; simp_all
      rw [fields, softWertExakt_null] at hv
      exact (Option.some.inj hv).symm
    rw [ua, vb, rundeExakt_null f64 _ (by decide)]
    symm
    apply rundeExakt_null
    simp [softAlignedMagnitude, softSig, azero.1, azero.2, bzero.1, bzero.2, softShiftJamNat]
  · have an : a.bexp ≠ 0 ∨ a.frac ≠ 0 := by omega
    have lp : 0 < l := by dsimp only [l]; unfold softSig; split <;> omega
    rw [decodedNonzero a u hu an]
    by_cases bzero : b.bexp = 0 ∧ b.frac = 0
    · have vb : v = ⟨0, 0⟩ := by
        have fields : b = ⟨b.sign, 0, 0⟩ := by cases b; simp_all
        rw [fields, softWertExakt_null] at hv
        exact (Option.some.inj hv).symm
      rw [vb, roundAddZero a.sign l ((e : Int) - 1075) lp]
      have magnitude : softAlignedMagnitude a.sign b.sign l r (e - f) = l * 8 := by
        simp [softAlignedMagnitude, r, softSig, bzero.1, bzero.2, softShiftJamNat]
      rw [magnitude]
      have scale := softRound_signed_mul_pow a.sign l 3 ((e : Int) - 1078) lp
      have exponent : (e : Int) - 1078 + (3 : Nat) = (e : Int) - 1075 := by omega
      rw [exponent] at scale
      exact scale.symm
    · have bn : b.bexp ≠ 0 ∨ b.frac ≠ 0 := by omega
      rw [decodedNonzero b v hv bn]
      have exponent : (f : Int) - 1075 = ((e : Int) - 1075) - ((e - f : Nat) : Int) := by omega
      change rundeExakt f64 (exaktAdd
        ⟨if a.sign then -(l : Int) else (l : Int), (e : Int) - 1075⟩
        ⟨if b.sign then -(r : Int) else (r : Int), (f : Int) - 1075⟩) = _
      rw [exponent]
      have result := softRound_exaktAdd_aligned a.sign b.sign l r (e - f)
        ((e : Int) - 1075) data.1 data.2.1 (by
          intro tail
          have h := data.2.2.2.2 tail
          simpa only [show (e : Int) - 1075 - 3 = (e : Int) - 1078 by omega] using h)
      simpa only [softAlignedMagnitude,
        show (e : Int) - 1075 - 3 = (e : Int) - 1078 by omega] using result

/-- A full-word alignment gap and signed near-cancellation both instantiate
    the source link on real finite decoded operands. -/
theorem routineSource_sum_zeuge :
    let a : GFloat := ⟨false, 1023, 0⟩
    let b : GFloat := ⟨false, 0, 1⟩
    wf f64 a ∧ wf f64 b ∧ floatMag b ≤ floatMag a ∧
    wertExakt f64 a = some ⟨2 ^ 52, -52⟩ ∧
    wertExakt f64 b = some ⟨1, -1074⟩ ∧
    rundeExakt f64 (exaktAdd ⟨2 ^ 52, -52⟩ ⟨1, -1074⟩) =
      rundeExakt f64 ⟨(routineDirectionalWord
        (BitVec.ofNat 64 (zuBits f64 a)) (BitVec.ofNat 64 (zuBits f64 b))).toNat, -55⟩ ∧
    routineDirectionalWord (BitVec.ofNat 64 4607182418800017409)
      (BitVec.ofNat 64 13830554455654793216) = 8 := by
  decide +kernel

#print axioms routineSource_sum
#print axioms routineSource_sum_zeuge
end Gabbro.Stage0.Senke
