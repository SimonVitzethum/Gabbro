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
