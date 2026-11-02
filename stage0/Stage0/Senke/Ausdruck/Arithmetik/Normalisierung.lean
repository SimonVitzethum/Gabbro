/- Exact post-cancellation magnitude extraction from a signed quotient and tail. -/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Normalisierunga
public import Stage0.Senke.Ausdruck.Arithmetik.Output
public import Mathlib.Tactic.Ring
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem Gleitkomma
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Alignment, signed addition and magnitude extraction are one computation;
    no hypothesis supplies the sum's value or a magnitude routine's result. -/
theorem floatNegativeSumMagnitudeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {hi magnitude distance sticky : Nat → Option (List II × Nat)}
    (h : Int) (a k : Runner.W)
    (hh : -(2^61) ≤ h ∧ h ≤ 2^61) (ha : a.toNat ≤ 2^61)
    (hhi : WordCode (L := L) ρ W hi (BitVec.ofInt 64 h))
    (hmag : WordCode (L := L) ρ W magnitude a)
    (hk : WordCode (L := L) ρ W distance k)
    (ht : WordCode (L := L) ρ W sticky (BitVec.ofInt 64
      (if (-(a.toNat : Int)) % (2^k.toNat : Nat) = 0 then 0 else 1))) :
    WordCode (L := L) ρ W
      (fun dst => floatSumMagnitudeL dst
        (fun j => floatNegativeSumL j hi magnitude distance) sticky)
      (BitVec.ofInt 64 (floatSumMagnitude
        (h + (-(a.toNat : Int)) / (2^k.toNat : Nat))
        ((-(a.toNat : Int)) % (2^k.toNat : Nat)))) := by
  have hb := floatNegativeAlign_bounds a.toNat (2^k.toNat)
    (Nat.pow_pos (by decide))
  intro fp K dst code top hc hK m pc hp
  exact floatSumMagnitudeL_ok _ _ (by constructor <;> omega)
    (floatNegativeSumL_ok hhi hmag hk) ht hc hK m pc hp

omit [Kern] in
/-- The magnitude bridge applies directly to the exact numerator of aligned
    subtraction. All remainder bounds follow from Euclidean division. -/
theorem floatNegativeSumMagnitude_reconstruct (h : Int) (a k : Runner.W) :
    let den : Int := (2^k.toNat : Nat)
    let z := h + (-(a.toNat : Int)) / den
    let r := (-(a.toNat : Int)) % den
    ((h * den - (a.toNat : Int)).natAbs : Int) =
      floatSumMagnitude z r * den +
        (if z < 0 then if r = 0 then 0 else den - r else r) := by
  dsimp only
  have hd : (0 : Int) < (2^k.toNat : Nat) := by
    exact_mod_cast Nat.pow_pos (by decide : 0 < 2) (n := k.toNat)
  rw [Int.sub_eq_add_neg, floatSignedAlign_reconstruct h (-(a.toNat : Int)) (2^k.toNat)]
  exact floatSumMagnitude_reconstruct _ _ _ hd
    ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hd⟩

/-- All producer and signed-range premises hold jointly on nonzero negative
    cancellation with an inexact tail. -/
theorem floatNegativeSumMagnitudeL_ok_zeuge {Γ : Ctx}
    (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W
      (fun dst => floatSumMagnitudeL dst
        (fun j => floatNegativeSumL j
          (fun j => some ([ci 1 j (-10) 0], j+1))
          (fun j => some ([ci 1 j 13 0], j+1))
          (fun j => some ([ci 1 j 2 0], j+1)))
        (fun j => some ([ci 1 j 1 0], j+1))) (BitVec.ofInt 64 13) := by
  intro fp K dst code top hc hK m pc hp
  exact floatNegativeSumMagnitudeL_ok (-10) 13 2 (by decide) (by decide)
    (WordCode.const (-10) (by decide)) (WordCode.const 13 (by decide))
    (WordCode.const 2 (by decide)) (WordCode.const 1 (by decide)) hc hK m pc hp

omit [Kern] in
/-- Joint non-degenerate cancellation and tail boundaries of the canonical
    bridge: exact cancellation, a tiny negative result, and both signs. -/
theorem floatSumMagnitude_reconstruct_zeuge :
    floatSumMagnitude (-1) (2^1074-13) = 0 ∧
    floatSumMagnitude (-7) 3 = 6 ∧
    floatSumMagnitude 7 3 = 7 ∧
    floatSumMagnitude 0 0 = 0 ∧
    (((-1 : Int) * 2^1074 + (2^1074-13)).natAbs : Int) = 13 := by
  decide +kernel

#print axioms floatNegativeSumMagnitude_reconstruct
#print axioms floatNegativeSumMagnitudeL_ok_zeuge
#print axioms floatSumMagnitude_reconstruct
#print axioms floatSumMagnitudeL_ok
#print axioms floatNegativeSumMagnitudeL_ok
#print axioms floatSumMagnitude_reconstruct_zeuge
omit [Kern] in
/-- Canonical rounding retains the exact numerator sign, including underflow
    and overflow. Exact cancellation has a nonnegative numerator and yields +0. -/
theorem floatRoundedExact_sign (F : Format) (v : Exakt) :
    (rundeExakt F v).sign = decide (v.zaehler < 0) := by
  have core (s : Bool) (n d : Nat) (E : Int) :
      (rundeBruchKern F s n d E).sign = s := by
    unfold rundeBruchKern
    split <;> try rfl
    split <;> try rfl
    split
    · split <;> try rfl
      split <;> rfl
    · split <;> rfl
  have rational (z : Int) (d : Nat) (hd : d ≠ 0) :
      (rundeBruch F ⟨z,d⟩).sign = decide (z < 0) := by
    simp only [rundeBruch, rundeBruchBei, hd, ↓reduceIte]
    split
    · rfl
    · exact core _ _ _ _
  unfold rundeExakt exaktBruch
  split
  · rw [rational _ 1 (by decide)]
    have hp : (0 : Int) < (2 ^ v.zweierExp.toNat : Nat) := by exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
    simp only [Int.mul_neg_iff]
    simp_all <;> omega
  · exact rational _ _ (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))

omit [Kern] in
/-- Cancellation is canonical positive zero at every scale, including scales
    far outside either IEEE format's exponent range. -/
theorem floatRoundedExact_cancel (F : Format) (e : Int) :
    rundeExakt F ⟨0,e⟩ = ⟨false,0,0⟩ := by
  have hn (n : Nat) : 2^n ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))
  unfold rundeExakt exaktBruch
  split <;> simp [rundeBruch, rundeBruchBei, hn]

#print axioms floatRoundedExact_cancel

omit [Kern] in
/-- The Euclidean quotient comparison is the exact result sign even when the
    quotient is zero or minus one and only the tail carries the magnitude. -/
theorem floatSumSign_exact (z r den : Int) (hd : 0 < den)
    (hr : 0 ≤ r ∧ r < den) :
    (z * den + r < 0) ↔ z < 0 := by
  constructor
  · intro h
    by_contra hn
    have := Int.mul_nonneg (show 0 ≤ z by omega) (show 0 ≤ den by omega)
    omega
  · intro h
    have := Int.mul_le_mul_of_nonneg_right (show z ≤ -1 by omega) (show 0 ≤ den by omega)
    omega

/-- Execute the result-sign comparison and connect it to the canonical IEEE
    result. No result-sign premise is supplied. The exact-tail bounds suffice
    for all denominators; cancellation returns false, independently of format. -/
theorem floatSumSignL_canonical {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {sum : Nat → Option (List II × Nat)} (F : Format) (z r den e : Int)
    (hz : -2^63 ≤ z ∧ z < 2^63) (hd : 0 < den) (hr : 0 ≤ r ∧ r < den)
    (hs : WordCode (L := L) ρ W sum (BitVec.ofInt 64 z)) :
    WordCode (L := L) ρ W (fun j => wordK 13 j (sum j) 0)
      (Runner.IR.bool (rundeExakt F ⟨z * den + r, e⟩).sign) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin hs (WordCode.const 0 (by decide))
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl rfl (by decide : 13 < 256)
  intro fp K dst code top hc hK m pc hp
  apply (result hc hK m pc hp).mono
  intro w hw
  rw [hw, slt_in hz (by decide), floatRoundedExact_sign]
  simp only [floatSumSign_exact z r den hd hr]

#print axioms floatRoundedExact_sign
#print axioms floatSumSign_exact
#print axioms floatSumSignL_canonical

omit [Kern] in
/-- Identify the actual retained-sum sign expression with the canonical rounded
    exact result, including cancellation and an arbitrarily distant exact tail. -/
theorem floatNormalizedSignField_canonical (F : Format) (z r den e : Int)
    (hz : -2^63 ≤ z ∧ z < 2^63) (hd : 0 < den)
    (hr : 0 ≤ r ∧ r < den) :
    Runner.IR.bool ((BitVec.ofInt 64 z).slt 0) *
        BitVec.ofNat 64 (2^(F.ebits+F.fracBits)) =
      BitVec.ofNat 64 (if (rundeExakt F ⟨z*den+r,e⟩).sign then
        2^(F.ebits+F.fracBits) else 0) := by
  have cmp := slt_in hz (y := 0) (by decide)
  change (BitVec.ofInt 64 z).slt 0 = decide (z < 0) at cmp
  rw [cmp, floatRoundedExact_sign]
  simp only [floatSumSign_exact z r den hd hr]
  by_cases h : z < 0 <;> simp [h, Runner.IR.bool]

omit [Kern] in
/-- The executed exponent subtraction is the biased field at the completed
    transfer count. The normal-range condition prevents natural truncation;
    no premise equates a machine result to the requested field. -/
theorem floatNormalizedExponentField_canonical (F : Format) (initial : Int)
    (count : Nat) (normal : F.emin ≤ initial - count) :
    BitVec.ofInt 64 (initial-F.emin+1) - BitVec.ofNat 64 count =
      BitVec.ofNat 64 (initial-(count : Int)-F.emin+1).toNat := by
  have nonneg : 0 ≤ initial-(count : Int)-F.emin+1 := by omega
  rw [← BitVec.ofInt_natCast, BitVec.sub_eq_add_neg,
    ← BitVec.ofInt_neg, ← BitVec.ofInt_add]
  have rearrange : initial-F.emin+1 + -(count : Int) =
      initial-(count : Int)-F.emin+1 := by omega
  rw [rearrange]
  simpa only [BitVec.ofInt_natCast] using
    (congrArg (BitVec.ofInt 64) (Int.toNat_of_nonneg nonneg)).symm

omit [Kern] in
/-- Both IEEE formats jointly exercise a negative nonzero exact tail and an
    exponent decreased by three normalization transfers. -/
theorem floatNormalizedCanonicalFields_zeuge :
    ∀ F ∈ [f32, f64],
      (Runner.IR.bool ((BitVec.ofInt 64 (-1)).slt 0) *
          BitVec.ofNat 64 (2^(F.ebits+F.fracBits)) =
        BitVec.ofNat 64 (if (rundeExakt F ⟨-13,-4⟩).sign then
          2^(F.ebits+F.fracBits) else 0)) ∧
      (BitVec.ofInt 64 (4-F.emin+1) - BitVec.ofNat 64 3 =
        BitVec.ofNat 64 (4-(3 : Int)-F.emin+1).toNat) := by
  intro F member
  constructor
  · simpa using floatNormalizedSignField_canonical F (-1) 3 16 (-4)
      (by norm_num) (by norm_num) (by norm_num)
  · apply floatNormalizedExponentField_canonical
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel

#print axioms floatNormalizedSignField_canonical
#print axioms floatNormalizedExponentField_canonical
#print axioms floatNormalizedCanonicalFields_zeuge

end Gabbro.Stage0.Senke
