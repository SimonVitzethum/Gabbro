/- Exact signed alignment and addition before the shared canonical rounding.
   This fragment requires an exact word-sized sum. Wide exponent differences
   still need a precision-preserving continuation before add/sub can be enabled. -/
import Stage0.Senke.Ausdruck.Arithmetik.Signifikand
import Stage0.Senke.Ausdruck.Arithmetik.AddSub

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem Gleitkomma

/-- Align the higher-exponent coefficient, then add the lower coefficient.
    No bits are discarded before cancellation. -/
def floatAlignSumWord (lo hi distance : Runner.W) : Runner.W :=
  lo + (hi <<< (distance.toNat % 64))

def floatAlignSumL (d : Nat) (lo hi distance : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 3 d (lo d) (wordL 11 (d + 1) (hi (d + 1)) (distance (d + 2)))

/-- The actual integer operations compute the exact aligned sum modulo the
    word size, for signed coefficients of either sign. -/
theorem floatAlignSumWord_model (lo hi : Int) (k : Nat) (hk : k < 64) :
    floatAlignSumWord (BitVec.ofInt 64 lo) (BitVec.ofInt 64 hi) (BitVec.ofNat 64 k) =
      BitVec.ofInt 64 (lo + hi * (2^k : Nat)) := by
  unfold floatAlignSumWord
  rw [← BitVec.ofInt_natCast, shl_w hi (by omega) (by omega)]
  simp only [Int.toNat_natCast]
  norm_cast
  exact (BitVec.ofInt_add _ _).symm

/-- With an explicit signed-word range, cancellation is exact, and canonical
    rounding receives precisely G's aligned value. This is a bridge to the
    existing rounding semantics, not yet an emitted rounding routine. -/
theorem floatAlignSumWord_round (F : Format) (u v : Exakt)
    (he : u.zweierExp ≤ v.zweierExp)
    (hk : (v.zweierExp - u.zweierExp).toNat < 64)
    (hr : -(2^63) ≤ u.zaehler + v.zaehler * (2^(v.zweierExp - u.zweierExp).toNat : Nat) ∧
      u.zaehler + v.zaehler * (2^(v.zweierExp - u.zweierExp).toNat : Nat) < 2^63) :
    rundeExakt F ⟨(floatAlignSumWord (BitVec.ofInt 64 u.zaehler)
      (BitVec.ofInt 64 v.zaehler)
      (BitVec.ofNat 64 (v.zweierExp - u.zweierExp).toNat)).toInt, u.zweierExp⟩ =
      rundeExakt F (exaktAdd u v) := by
  rw [floatAlignSumWord_model _ _ _ hk, toInt_ofInt_in hr.1 hr.2,
    floatAdd_align, ite_eq_left he]

/-- End-to-end value bridge for the connected coefficient/alignment prefix.
    The dispatcher has excluded special values and established the exact
    exponents; the same continuation rounds the actual integer result. -/
theorem floatCoefficientAlignSumWord_add (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b) (ea eb : Int)
    (hdispatch : floatAddSpecial f64 a b = none)
    (hua : wertExakt f64 a = some ⟨floatCoefficient a, ea⟩)
    (hub : wertExakt f64 b = some ⟨floatCoefficient b, eb⟩)
    (he : ea ≤ eb) (hk : (eb - ea).toNat < 64)
    (hr : -(2^63) ≤ floatCoefficient a + floatCoefficient b * (2^(eb-ea).toNat : Nat) ∧
      floatCoefficient a + floatCoefficient b * (2^(eb-ea).toNat : Nat) < 2^63) :
    rundeExakt f64 ⟨(floatAlignSumWord
      (floatCoefficientWord (BitVec.ofNat 64 (zuBits f64 a)))
      (floatCoefficientWord (BitVec.ofNat 64 (zuBits f64 b)))
      (BitVec.ofNat 64 (eb-ea).toNat)).toInt, ea⟩ = add f64 a b := by
  rw [floatCoefficientWord_canonical a ha, floatCoefficientWord_canonical b hb]
  rw [floatAddSpecial_model, hdispatch, hua, hub]
  exact floatAlignSumWord_round f64 ⟨floatCoefficient a, ea⟩
    ⟨floatCoefficient b, eb⟩ he hk hr

/-- Joint premises for the generic value bridge at exact cancellation down
    to the smallest subnormal. -/
theorem floatCoefficientAlignSumWord_add_zeuge :
    let a : GFloat := ⟨true, 0, 2^52-1⟩
    let b : GFloat := ⟨false, 1, 0⟩
    wf f64 a ∧ wf f64 b ∧ floatAddSpecial f64 a b = none ∧
    wertExakt f64 a = some ⟨floatCoefficient a, -1074⟩ ∧
    wertExakt f64 b = some ⟨floatCoefficient b, -1074⟩ ∧
    (-1074 : Int) ≤ -1074 ∧ ((-1074 : Int) - -1074).toNat < 64 ∧
    (-(2^63) ≤ floatCoefficient a + floatCoefficient b * (2^0 : Nat) ∧
      floatCoefficient a + floatCoefficient b * (2^0 : Nat) < 2^63) ∧
    add f64 a b = ⟨false, 0, 1⟩ := by
  decide +kernel

variable [Kern] {D : Deklaration} {L : Lay D}

/-- Connected simulation inherits the frame, footprint and temporary checks
    of the common word composition mechanism for arbitrary producers. -/
theorem floatAlignSumL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {lo hi distance : Nat → Option (List II × Nat)} {a b k : Runner.W}
    (ha : WordCode (L := L) ρ W lo a) (hb : WordCode (L := L) ρ W hi b)
    (hk : WordCode (L := L) ρ W distance k) :
    WordCode (L := L) ρ W (fun d => floatAlignSumL d lo hi distance)
      (floatAlignSumWord a b k) := by
  exact WordCode.bin ha (WordCode.bin hb hk
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256))
    (g := fun a b => some (a + b)) rfl rfl (by decide : 3 < 256)

/-- The signed IEEE coefficients flow directly into the shared alignment and
    sum; the fragment has no separate implementation for subtraction. -/
theorem floatCoefficientAlignSumL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {lo hi distance : Nat → Option (List II × Nat)} {a b k : Runner.W}
    (ha : WordCode (L := L) ρ W lo a) (hb : WordCode (L := L) ρ W hi b)
    (hk : WordCode (L := L) ρ W distance k) :
    WordCode (L := L) ρ W (fun d => floatAlignSumL d
      (fun j => floatCoefficientL j lo) (fun j => floatCoefficientL j hi) distance)
      (floatAlignSumWord (floatCoefficientWord a) (floatCoefficientWord b) k) :=
  floatAlignSumL_ok (floatCoefficientL_ok ha) (floatCoefficientL_ok hb) hk

omit [Kern] in
/-- Exact instruction and temporary costs, including all three producers. -/
theorem floatAlignSumL_shape (d ta tb tk na nb nk : Nat)
    (a b k : Nat → Option (List II × Nat)) (ca cb ck : Nat → List II)
    (ha : ∀ j, a j = some (ca j, j + ta))
    (hb : ∀ j, b j = some (cb j, j + tb))
    (hk : ∀ j, k j = some (ck j, j + tk))
    (hla : ∀ j, (ca j).length = na) (hlb : ∀ j, (cb j).length = nb)
    (hlk : ∀ j, (ck j).length = nk) :
    ∃ output, floatAlignSumL d a b k =
      some (output, max (d + ta) (max (d + 1 + tb) (max (d + 2 + tk) (d + 3)))) ∧
      output.length = na + nb + nk + 2 := by
  simp [floatAlignSumL, wordL, ha, hb, hk, bin2, hla, hlb, hlk, Nat.add_assoc]

#print axioms floatAlignSumWord_round
#print axioms floatAlignSumL_ok
end Gabbro.Stage0.Senke
