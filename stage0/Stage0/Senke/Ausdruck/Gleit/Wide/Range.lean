/- A computed conversion rejects infinity before the ordinary finite range test. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Slots.Test
public import Stage0.Senke.Gleit.Routine.RoutineModel
public import Stage0.Senke.Gleit.Routine.RoutineBranch
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem

/-- Integer conversion may overflow even when either endpoint is infinite.
    The source float value must still be finite. -/
def computedFloatRangeReject (lo hi : Int × Int) (x : GFloat) : Bool :=
  if x.bexp = 2047 then true else floatRangeReject lo hi x

private theorem computedFloat_finite (x : GFloat) :
    gleitEndlich x = decide (x.bexp ≠ 2047) := by
  by_cases maximum : x.bexp = 2047 <;>
    by_cases zero : x.bexp = 0 <;> by_cases frac : x.frac = 0 <;>
    simp [gleitEndlich, klasse, show f64.bexpMax = 2047 from rfl, maximum, zero, frac]

theorem computedFloatRangeReject_none {lo hi : Int × Int} {x : GFloat}
    (hw : wf f64 x) :
    gleitPasst lo hi x = none ↔ computedFloatRangeReject lo hi x = true := by
  by_cases infinite : x.bexp = 2047
  · have notFinite : gleitEndlich x = false := by
      simp [computedFloat_finite, infinite]
    simp [computedFloatRangeReject, infinite, gleitPasst, notFinite]
  · have finite : gleitEndlich x = true := by
      simpa only [computedFloat_finite, decide_eq_true_eq] using infinite
    simpa only [computedFloatRangeReject, if_neg infinite] using floatRangeReject_none hw finite

def computedFloatRangeL (d : Nat) (lo hi : Int × Int)
    (producer : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  routineChooseL d
    (fun j => wordK 14 j (unpackBexpL j producer) 2047)
    (fun j => some ([ci 1 j 1 0], j + 1))
    (fun j => canonicalFloatRangeL j lo hi producer)

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The exponent check and the existing range comparison both consume the
    very same proved producer. No finite-conversion premise is needed. -/
theorem computedFloatRangeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {reserved : Nat} (x : GFloat) (hw : wf f64 x)
    (lo hi : Int × Int) (producer : Nat → Option (List II × Nat))
    (run : ∀ {fp K d c top}, producer d = some (c, top) → top ≤ K → ∀ m pc,
      Pre L m pc fp K d c ρ W reserved → Ok m pc fp K d c
        (fun w => wf f64 x ∧ w = BitVec.ofNat 64 (zuBits f64 x))) :
    WordCode (L := L) ρ W (fun d => computedFloatRangeL d lo hi producer)
      (Runner.IR.bool (computedFloatRangeReject lo hi x)) reserved := by
  have source : WordCode (L := L) ρ W producer (BitVec.ofNat 64 (zuBits f64 x)) reserved := by
    intro fp K d c top emitted fits m pc pre
    exact (run emitted fits m pc pre).mono (fun _ h => h.2)
  have exponent : WordCode (L := L) ρ W (fun d => unpackBexpL d producer)
      (unpackBexpWord (BitVec.ofNat 64 (zuBits f64 x))) reserved := unpackBexpL_ok source
  rw [(routineUnpack_canonical x hw).2.1] at exponent
  have equal : (BitVec.ofNat 64 x.bexp == (2047 : Runner.W)) = decide (x.bexp = 2047) := by
    apply Bool.eq_iff_iff.mpr
    have bound : x.bexp < 2 ^ 64 := by
      have := hw.1
      change x.bexp ≤ 2047 at this
      omega
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] <;> rfl
  have check : WordCode (L := L) ρ W
      (fun j => wordK 14 j (unpackBexpL j producer) 2047)
      (Runner.IR.bool (BitVec.ofNat 64 x.bexp == BitVec.ofInt 64 2047)) reserved :=
    WordCode.bin exponent (WordCode.const 2047 (by decide))
      (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
  rw [show BitVec.ofInt 64 2047 = (2047 : Runner.W) from rfl, equal] at check
  have yes : decide (x.bexp = 2047) = true →
      WordCode (L := L) ρ W (fun j => some ([ci 1 j 1 0], j + 1))
        (Runner.IR.bool true) reserved := fun _ => WordCode.const 1 (by decide)
  have no : decide (x.bexp = 2047) = false →
      WordCode (L := L) ρ W (fun j => canonicalFloatRangeL j lo hi producer)
        (Runner.IR.bool (floatRangeReject lo hi x)) reserved := by
    intro flag fp K d c top emitted fits m pc pre
    have nonmax : x.bexp ≠ 2047 := by simpa using flag
    have finite : gleitEndlich x = true := by
      simpa only [computedFloat_finite, decide_eq_true_eq] using nonmax
    exact canonicalFloatRangeL_ok (fp := fp) (K := K) (d := d) (top := top)
      (reserved := reserved) x hw finite producer
      (fun d c top hc ht m pc hp => run (fp := fp) (K := K) hc ht m pc hp)
      emitted fits pre
  have result : WordCode (L := L) ρ W (fun d => computedFloatRangeL d lo hi producer)
      (if decide (x.bexp = 2047) then Runner.IR.bool true
        else Runner.IR.bool (floatRangeReject lo hi x)) reserved :=
    routineChooseL_ok check yes no
  intro fp K d c top emitted fits m pc pre
  have executed := result emitted fits m pc pre
  by_cases nonfinite : x.bexp = 2047
  · simpa only [computedFloatRangeL, computedFloatRangeReject, nonfinite,
      decide_true, ite_true] using executed
  · simpa only [computedFloatRangeL, computedFloatRangeReject, nonfinite,
      decide_false, Bool.false_eq_true, ite_false] using executed

/-- The finite path is exactly the established inclusive decision, including
    its NaN-endpoint rejection. The extra guard changes overflow only. -/
theorem computedFloatRangeReject_finite {lo hi : Int × Int} {x : GFloat}
    (finite : gleitEndlich x = true) :
    computedFloatRangeReject lo hi x = floatRangeReject lo hi x := by
  have notMax : x.bexp ≠ 2047 := by
    simpa only [computedFloat_finite, decide_eq_true_eq] using finite
  exact if_neg notMax

/-- Overflow must reject even when the declared upper endpoint is infinite. -/
theorem computedFloatRangeReject_overflow_zeuge :
    computedFloatRangeReject (0, 1) (2 ^ 1025, 1) (gleitAusInt (2 ^ 1024)) = true ∧
    computedFloatRangeReject (0, 1) (2 ^ 129, 1) (gleitAusInt (2 ^ 127 + 1)) = false ∧
    computedFloatRangeReject (-(2 ^ 129), 1) (0, 1) (gleitAusInt (-(2 ^ 127 + 1))) = false := by
  decide +kernel

#print axioms computedFloatRangeL_ok
#print axioms computedFloatRangeReject_none
#print axioms computedFloatRangeReject_overflow_zeuge
end Gabbro.Stage0.Senke
