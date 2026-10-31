/- Adaptive exact-rational left normalization before guard/sticky compression. -/
import Stage0.Senke.Ausdruck.Arithmetik.Normalisierung

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem Gleitkomma

/-- A threshold of zero stops normalization, including at the subnormal floor.
    Otherwise transfer one exact remainder bit while the magnitude is small. -/
def floatNormalizeActive (q target : Int) : Int := if q < target then 1 else 0

def floatNormalizeCarry (r den : Int) : Int := if r < den - r then 0 else 1

def floatNormalizeStep (q r den target : Int) : Int × Int :=
  let a := floatNormalizeActive q target
  let c := floatNormalizeCarry r den
  (q * (1+a) + a*c, r * (1+a) - a*c*den)

/-- Exactness precedes compression. In particular q=0 with a nonzero tail
    continues to recover bits rather than replacing that tail with sticky. -/
theorem floatNormalizeStep_exact (q r den target : Int) :
    (floatNormalizeStep q r den target).1 * den +
      (floatNormalizeStep q r den target).2 =
      (q * den + r) * (1 + floatNormalizeActive q target) := by
  simp only [floatNormalizeStep]
  ring

/-- Each transferred bit leaves a canonical Euclidean remainder. -/
theorem floatNormalizeStep_bounds (q r den target : Int)
    (hq : 0 ≤ q) (_hd : 0 < den) (hr : 0 ≤ r ∧ r < den) :
    0 ≤ (floatNormalizeStep q r den target).1 ∧
    0 ≤ (floatNormalizeStep q r den target).2 ∧
      (floatNormalizeStep q r den target).2 < den := by
  unfold floatNormalizeStep floatNormalizeActive floatNormalizeCarry
  split <;> split <;> simp_all <;> omega

/-- Both outputs use the same adaptive predicate and exact remainder carry.
    The caller retains the outputs before repeating; no jammed operand enters
    this step. The denominator is an exact word, not a sticky encoding. -/
def floatNormalizeStepL (remainder : Bool) (dst : Nat)
    (q r den target : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let active := fun j => wordL 13 j (q j) (target (j+1))
  let gap := fun j => wordL 4 j (den j) (r (j+1))
  let below := fun j => wordL 13 j (r j) (gap (j+1))
  let carry := fun j => wordL 4 j (some ([ci 1 j 1 0], j+1)) (below (j+1))
  let factor := fun j => wordL 3 j (some ([ci 1 j 1 0], j+1)) (active (j+1))
  let bit := fun j => wordL 5 j (active j) (carry (j+1))
  if remainder then
    wordL 4 dst (wordL 5 dst (r dst) (factor (dst+1)))
      (wordL 5 (dst+1) (bit (dst+1)) (den (dst+2)))
  else wordL 3 dst (wordL 5 dst (q dst) (factor (dst+1))) (bit (dst+1))

/-- Complete exact normalization with an explicit finite shift budget. The
    third component counts transfers, so exponent adjustment is exact even
    when normalization stops early. A zero target represents the format floor. -/
def floatNormalize (fuel : Nat) (q r den target : Int) : Int × Int × Nat :=
  match fuel with
  | 0 => (q, r, 0)
  | n+1 =>
    if q < target then
      let step := floatNormalizeStep q r den target
      let next := floatNormalize n step.1 step.2 den target
      (next.1, next.2.1, next.2.2+1)
    else (q, r, 0)

/-- Whole-iteration invariant: exact reconstruction, canonical remainder,
    finite resource count, and either a normalized quotient or exhausted fuel.
    The denominator has no machine-word restriction. -/
theorem floatNormalize_invariant (fuel : Nat) (q r den target : Int)
    (hq : 0 ≤ q) (hd : 0 < den) (hr : 0 ≤ r ∧ r < den) :
    let out := floatNormalize fuel q r den target
    0 ≤ out.1 ∧ 0 ≤ out.2.1 ∧ out.2.1 < den ∧
      out.1 * den + out.2.1 = (q * den + r) * 2^out.2.2 ∧
      out.2.2 ≤ fuel ∧ (target ≤ out.1 ∨ out.2.2 = fuel) := by
  induction fuel generalizing q r with
  | zero => simp [floatNormalize, hq, hr]
  | succ n ih =>
    by_cases h : q < target
    · have hb := floatNormalizeStep_bounds q r den target hq hd hr
      have hi := ih _ _ hb.1 ⟨hb.2.1, hb.2.2⟩
      have he := floatNormalizeStep_exact q r den target
      simp only [floatNormalizeActive, h, ↓reduceIte] at he
      dsimp only at hi
      simp only [floatNormalize, h, ↓reduceIte]
      refine ⟨hi.1, hi.2.1, hi.2.2.1, ?_, by omega, ?_⟩
      · rw [hi.2.2.2.1, he, pow_succ]
        ring
      · rcases hi.2.2.2.2.2 with ht | hn
        · exact Or.inl ht
        · exact Or.inr (by omega)
    · simp [floatNormalize, h, hq, hr, show target ≤ q by omega]

/-- A positive exact numerator reaches the target within the supplied bound.
    This also covers q=0 and arbitrarily large exact denominators. -/
theorem floatNormalize_complete (fuel : Nat) (q r den target : Int)
    (hq : 0 ≤ q) (hd : 0 < den) (hr : 0 ≤ r ∧ r < den)
    (hn : 0 < q * den + r) (hb : target * den ≤ 2^fuel) :
    target ≤ (floatNormalize fuel q r den target).1 := by
  have hi := floatNormalize_invariant fuel q r den target hq hd hr
  dsimp only at hi
  rcases hi.2.2.2.2.2 with ht | hs
  · exact ht
  · have he := hi.2.2.2.1
    rw [hs] at he
    have hp : (0 : Int) < 2^fuel := Int.pow_pos (by decide)
    have hm : (2 : Int)^fuel ≤ (q * den + r) * 2^fuel := by
      have hh := Int.mul_le_mul_of_nonneg_right (show 1 ≤ q*den+r by omega) (show 0 ≤ (2 : Int)^fuel by omega)
      simpa using hh
    have hl := hi.2.2.1
    by_contra h
    have hq' : (floatNormalize fuel q r den target).1 ≤ target-1 := by omega
    have hu := Int.mul_le_mul_of_nonneg_right hq' (show 0 ≤ den by omega)
    rw [Int.sub_mul, Int.one_mul] at hu
    omega

/-- The required fuel is derived from precision and denominator distance,
    rather than an arbitrary fixed unrolling count. -/
theorem floatNormalize_format_bound (precision distance : Nat) (q r den target : Int)
    (hq : 0 ≤ q) (hd : 0 < den) (hr : 0 ≤ r ∧ r < den)
    (hn : 0 < q * den + r)
    (ht : 0 ≤ target ∧ target ≤ 2^precision) (hden : den ≤ 2^distance) :
    target ≤ (floatNormalize (precision+distance) q r den target).1 := by
  apply floatNormalize_complete _ _ _ _ _ hq hd hr hn
  rw [pow_add]
  exact Int.mul_le_mul ht.2 hden (by omega) (le_of_lt (Int.pow_pos (by decide)))

/-- The actual iterated values are the unique Euclidean quotient and remainder
    of the scaled numerator. This is the canonical interface for rounding;
    no rounded or sticky surrogate appears in the reconstruction. -/
theorem floatNormalize_canonical (fuel : Nat) (q r den target : Int)
    (hq : 0 ≤ q) (hd : 0 < den) (hr : 0 ≤ r ∧ r < den) :
    let out := floatNormalize fuel q r den target
    let numerator := (q * den + r) * 2^out.2.2
    numerator / den = out.1 ∧ numerator % den = out.2.1 := by
  have hi := floatNormalize_invariant fuel q r den target hq hd hr
  dsimp only at hi ⊢
  rw [← hi.2.2.2.1]
  constructor
  · rw [Int.mul_add_ediv_right _ _ (by omega), Int.ediv_eq_zero_of_lt hi.2.1 hi.2.2.1]
    omega
  · simp [Int.add_emod, Int.emod_eq_of_lt hi.2.1 hi.2.2.1]

/-- Joint whole-iteration witnesses: early stopping with exponent adjustment,
    an exact subnormal floor, and completion across a binary64-sized distance. -/
theorem floatNormalize_zeuge :
    floatNormalize 20 0 13 16 8 = (13,0,4) ∧
    floatNormalize 20 0 13 16 0 = (0,13,0) ∧
    2^53 ≤ (floatNormalize (53+1074) 0 1 (2^1074) (2^53)).1 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  apply floatNormalize_format_bound 53 1074 <;> decide +kernel

#print axioms floatNormalize_canonical
#print axioms floatNormalize_zeuge

#print axioms floatNormalize_invariant
#print axioms floatNormalize_complete
#print axioms floatNormalize_format_bound

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The emitted adaptive step works under arbitrary word-code frames and
    footprints. Bounds exclude signed comparison wraparound for the exact tail. -/
theorem floatNormalizeStepL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {q r den target : Nat → Option (List II × Nat)}
    (qn rn dn tn : Int) (out : Bool)
    (hq : 0 ≤ qn ∧ qn < 2^62) (hd : 0 < dn ∧ dn < 2^62)
    (hr : 0 ≤ rn ∧ rn < dn) (ht : 0 ≤ tn ∧ tn < 2^62)
    (cq : WordCode (L := L) ρ W q (BitVec.ofInt 64 qn))
    (cr : WordCode (L := L) ρ W r (BitVec.ofInt 64 rn))
    (cd : WordCode (L := L) ρ W den (BitVec.ofInt 64 dn))
    (ct : WordCode (L := L) ρ W target (BitVec.ofInt 64 tn)) :
    WordCode (L := L) ρ W (fun j => floatNormalizeStepL out j q r den target)
      (BitVec.ofInt 64 (if out then (floatNormalizeStep qn rn dn tn).2
        else (floatNormalizeStep qn rn dn tn).1)) := by
  have active : WordCode (L := L) ρ W _ _ := WordCode.bin cq ct
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl rfl (by decide : 13 < 256)
  have gap : WordCode (L := L) ρ W _ _ := WordCode.bin cd cr
    (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
  have below : WordCode (L := L) ρ W _ _ := WordCode.bin cr gap
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl rfl (by decide : 13 < 256)
  have carry : WordCode (L := L) ρ W _ _ := WordCode.bin (WordCode.const 1 (by decide)) below
    (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
  have factor : WordCode (L := L) ρ W _ _ := WordCode.bin (WordCode.const 1 (by decide)) active
    (g := fun a b => some (a+b)) rfl rfl (by decide : 3 < 256)
  have bit : WordCode (L := L) ρ W _ _ := WordCode.bin active carry
    (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
  have aq : WordCode (L := L) ρ W _ _ := WordCode.bin cq factor
    (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
  have ar : WordCode (L := L) ρ W _ _ := WordCode.bin cr factor
    (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
  have bd : WordCode (L := L) ρ W _ _ := WordCode.bin bit cd
    (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
  have qr : WordCode (L := L) ρ W _ _ := WordCode.bin aq bit
    (g := fun a b => some (a+b)) rfl rfl (by decide : 3 < 256)
  have rr : WordCode (L := L) ρ W _ _ := WordCode.bin ar bd
    (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
  have sub (a b : Int) : BitVec.ofInt 64 a - BitVec.ofInt 64 b = BitVec.ofInt 64 (a-b) := by
    rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, ← Int.sub_eq_add_neg]
  have ac : Runner.IR.bool ((BitVec.ofInt 64 qn).slt (BitVec.ofInt 64 tn)) =
      BitVec.ofInt 64 (floatNormalizeActive qn tn) := by
    rw [slt_in (by constructor <;> omega) (by constructor <;> omega)]
    by_cases h : qn < tn <;> simp [h, Runner.IR.bool, floatNormalizeActive]
  have bc : (BitVec.ofInt 64 1) - Runner.IR.bool
      ((BitVec.ofInt 64 rn).slt ((BitVec.ofInt 64 dn) - (BitVec.ofInt 64 rn))) =
      BitVec.ofInt 64 (floatNormalizeCarry rn dn) := by
    rw [sub dn rn, slt_in (by constructor <;> omega) (by constructor <;> omega)]
    by_cases h : rn < dn-rn <;> simp [h, Runner.IR.bool, floatNormalizeCarry]
  cases out <;> intro fp K dst code top hc hK m pc hp
  · exact (qr hc hK m pc hp).mono fun w hw => by
      rw [ac, bc] at hw
      simpa only [ ← BitVec.ofInt_add, ← BitVec.ofInt_mul,
        floatNormalizeStep, Bool.false_eq_true, ↓reduceIte] using hw
  · exact (rr hc hK m pc hp).mono fun w hw => by
      rw [ac, bc] at hw
      simpa only [ ← BitVec.ofInt_add, ← BitVec.ofInt_mul, sub,
        floatNormalizeStep, ↓reduceIte] using hw

/-- Both emitted outputs have the same jointly satisfiable producer premises. -/
theorem floatNormalizeStepL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    ∀ out : Bool, WordCode (L := L) ρ W
      (fun j => floatNormalizeStepL out j
        (fun j => some ([ci 1 j 0 0], j+1))
        (fun j => some ([ci 1 j 13 0], j+1))
        (fun j => some ([ci 1 j 16 0], j+1))
        (fun j => some ([ci 1 j 8 0], j+1)))
      (BitVec.ofInt 64 (if out then 10 else 1)) := by
  intro out fp K dst code top hc hK m pc hp
  exact floatNormalizeStepL_ok 0 13 16 8 out (by decide) (by decide)
    (by decide) (by decide) (WordCode.const 0 (by decide))
    (WordCode.const 13 (by decide)) (WordCode.const 16 (by decide))
    (WordCode.const 8 (by decide)) hc hK m pc hp

omit [Kern] in
/-- Joint cancellation, carry, exact tie, and stopped subnormal-floor cases. -/
theorem floatNormalizeStep_zeuge :
    floatNormalizeStep 0 13 16 8 = (1,10) ∧
    floatNormalizeStep 1 10 16 8 = (3,4) ∧
    floatNormalizeStep 3 4 16 8 = (6,8) ∧
    floatNormalizeStep 6 8 16 8 = (13,0) ∧
    floatNormalizeStep 0 13 16 0 = (0,13) ∧
    floatNormalizeStep 8 3 16 8 = (8,3) := by decide +kernel

#print axioms floatNormalizeStepL_ok_zeuge
#print axioms floatNormalizeStep_exact
#print axioms floatNormalizeStep_bounds
#print axioms floatNormalizeStepL_ok
#print axioms floatNormalizeStep_zeuge
end Gabbro.Stage0.Senke
