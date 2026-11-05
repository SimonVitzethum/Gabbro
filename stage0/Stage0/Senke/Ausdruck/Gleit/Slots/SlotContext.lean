/- Complete source integers are converted by native CPU instructions. -/
module
public import Stage0.Senke.Gleit.Native.SourceCode
public import NativeFloat.IntScaling
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.SInt.Float
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

private theorem wideFloat_numeric (z : Int) (big : 2 ^ 55 ≤ z.natAbs) :
    Float.mul
      (Int64.ofInt (integerFloatJam z.natAbs (integerFloatShift z.natAbs) : Int)).toFloat
      (Float.ofBits (UInt64.ofNat ((if z < 0 then 2 ^ 63 else 0) +
        (integerFloatIndex z.natAbs - 55) * 2 ^ 52))) = gleitAusInt z := by
  dsimp only [gleitAusInt, integerFloatJam, integerFloatShift, integerFloatIndex]
  exact (RootNativeFloat.ofInt_jam56 z big).symm

private theorem wideFloat_power_decode (z : Int) (index : Nat) (word : Runner.W)
    (encoded : word = BitVec.ofNat 64 ((if decide (z < 0) then 2 ^ 63 else 0) +
      (index - 55) * 2 ^ 52)) :
    Runner.readFloat word = Float.ofBits (UInt64.ofNat ((if z < 0 then 2 ^ 63 else 0) +
      (index - 55) * 2 ^ 52)) := by
  have sign : (if decide (z < 0) then 2 ^ 63 else 0 : Nat) =
      (if z < 0 then 2 ^ 63 else 0) := by
    by_cases negative : z < 0 <;>
      simp only [negative, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  have bits : UInt64.ofBitVec word = UInt64.ofNat ((if z < 0 then 2 ^ 63 else 0) +
      (index - 55) * 2 ^ 52) := by
    rw [encoded, sign]
    apply UInt64.eq_of_toBitVec_eq
    rw [UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat']
  unfold Runner.readFloat
  exact congrArg Float.ofBits bits

variable [Kern] {D : Deklaration} {L : Lay D}

private theorem wideComputedFloatOfE_value_ok {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    {σ₀ σ : World D} (same : σ₀ = σ) (lay : LayIn L)
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (world : ∀ m, W m → WeltAt m L σ)
    (reserved : Nat) :
    NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => wideComputedFloatOfE L e d reserved) (gleitAusInt (eval σ₀ e σ ρ).n) := by
  let w := WideFloat.width lo hi
  let z := (eval σ₀ e σ ρ).n
  have bound : (z.natAbs : Int) ≤ WideFloat.upper w := WideFloat.magnitude_bound _
  have magnitude := WideFloat.magnitude_value (σ₀ := σ₀) (σ := σ) (ρ := ρ) (e := e) bound
  have condition : WordCode (L := L) (reserved := reserved) ρ W
      (fun d => lowE L (.lt (WideFloat.magnitude w e) (.lit (2 ^ 55))) d reserved)
      (Runner.IR.bool (wahr? (eval σ₀ (.lt (WideFloat.magnitude w e) (.lit (2 ^ 55))) σ ρ))) :=
    WideFloat.boolean (ρ := ρ) (σ₀ := σ₀) (σ := σ)
      (.lt (WideFloat.magnitude w e) (.lit (2 ^ 55))) lay same world reserved
  change WordCode (L := L) (reserved := reserved) ρ W _
    (Runner.IR.bool (decide ((eval σ₀ (WideFloat.magnitude w e) σ ρ).n < (2 : Int) ^ 55))) at condition
  rw [magnitude] at condition
  have small : decide ((z.natAbs : Int) < 2 ^ 55) = true →
      NativeFloatCode (L := L) (reserved := reserved) ρ W
        (fun j => nativeIntegerFloatL true j (fun d => lowE L (WideFloat.small e) d reserved))
        (gleitAusInt z) := by
    intro flag
    have narrow : z.natAbs < 2 ^ 55 := by
      have cast : (z.natAbs : Int) < 2 ^ 55 := of_decide_eq_true flag
      exact_mod_cast cast
    have child : WordCode (L := L) (reserved := reserved) ρ W
        (fun d => lowE L (WideFloat.small e) d reserved)
        (BitVec.ofInt 64 (eval σ₀ (WideFloat.small e) σ ρ).n) :=
      WideFloat.word (ρ := ρ) (σ₀ := σ₀) (σ := σ)
        (WideFloat.small e) (by decide) lay same world reserved
    rw [WideFloat.small_value (σ₀ := σ₀) (σ := σ) (ρ := ρ) (e := e) narrow] at child
    intro fp K d c top hc ht m pc pre
    exact nativeIntegerFloatL_source_ok
      (child := fun (j : Nat) => lowE L (WideFloat.small e) j reserved)
      true z ⟨by omega, by omega⟩ child hc ht m pc pre
  have sign : WordCode (L := L) (reserved := reserved) ρ W
      (fun d => lowE L (.lt e (.lit 0)) d reserved)
      (Runner.IR.bool (wahr? (eval σ₀ (.lt e (.lit 0)) σ ρ))) :=
    WideFloat.boolean (ρ := ρ) (σ₀ := σ₀) (σ := σ) (.lt e (.lit 0)) lay same world reserved
  change WordCode (L := L) (reserved := reserved) ρ W _
    (Runner.IR.bool (decide (z < 0))) at sign
  have large : decide ((z.natAbs : Int) < 2 ^ 55) = false →
      NativeFloatCode (L := L) (reserved := reserved) ρ W
        (fun j => nativeFPWordL (.mul .f64) j
          (nativeIntegerFloatL true j (fun d => lowE L (WideFloat.guard w e) d reserved))
          (nativeFloatScaleL (j + 1) (fun d => lowE L (.lt e (.lit 0)) d reserved)
            (fun d => lowE L (WideFloat.index w e) d reserved))) (gleitAusInt z) := by
    intro flag
    have big : 2 ^ 55 ≤ z.natAbs := by
      have cast : ¬ (z.natAbs : Int) < 2 ^ 55 := of_decide_eq_false flag
      omega
    have guard : WordCode (L := L) (reserved := reserved) ρ W
        (fun d => lowE L (WideFloat.guard w e) d reserved)
        (BitVec.ofInt 64 (eval σ₀ (WideFloat.guard w e) σ ρ).n) :=
      WideFloat.word (ρ := ρ) (σ₀ := σ₀) (σ := σ)
        (WideFloat.guard w e) (by decide) lay same world reserved
    have index : WordCode (L := L) (reserved := reserved) ρ W
        (fun d => lowE L (WideFloat.index w e) d reserved)
        (BitVec.ofInt 64 (eval σ₀ (WideFloat.index w e) σ ρ).n) :=
      WideFloat.word (ρ := ρ) (σ₀ := σ₀) (σ := σ)
        (WideFloat.index w e) (by decide) lay same world reserved
    rw [WideFloat.guard_value (σ₀ := σ₀) (σ := σ) (ρ := ρ) (e := e) bound (by omega)] at guard
    rw [WideFloat.index_value (σ₀ := σ₀) (σ := σ) (ρ := ρ) (e := e) bound big,
      BitVec.ofInt_natCast] at index
    let retainedValue : Float :=
      (Int64.ofInt (integerFloatJam z.natAbs (integerFloatShift z.natAbs) : Int)).toFloat
    let powerValue : Float := Float.ofBits (UInt64.ofNat ((if z < 0 then 2 ^ 63 else 0) +
      (integerFloatIndex z.natAbs - 55) * 2 ^ 52))
    have converted : NativeFloatCode (L := L) (reserved := reserved) ρ W
        (fun j => nativeIntegerFloatL true j
          (fun d => lowE L (WideFloat.guard w e) d reserved)) retainedValue := by
      intro fp K d c top hc ht m pc pre
      exact nativeIntegerFloatL_ok
        (child := fun (j : Nat) => lowE L (WideFloat.guard w e) j reserved) true
        (BitVec.ofInt 64 (integerFloatJam z.natAbs (integerFloatShift z.natAbs) : Int))
        guard hc ht m pc pre
    have scale : WordCode (L := L) (reserved := reserved) ρ W
        (fun j => nativeFloatScaleL j (fun d => lowE L (.lt e (.lit 0)) d reserved)
          (fun d => lowE L (WideFloat.index w e) d reserved))
        (nativeFloatScaleWord (decide (z < 0)) (integerFloatIndex z.natAbs)) := by
      intro fp K d c top hc ht m pc pre
      exact nativeFloatScaleL_ok
        (sign := fun (j : Nat) => lowE L (.lt e (.lit 0)) j reserved)
        (index := fun (j : Nat) => lowE L (WideFloat.index w e) j reserved)
        sign index hc ht m pc pre
    have lower : 55 ≤ integerFloatIndex z.natAbs := by unfold integerFloatIndex; omega
    have upper : integerFloatIndex z.natAbs ≤ 2047 := by unfold integerFloatIndex; omega
    rw [nativeFloatScaleWord_eq _ _ lower upper] at scale
    have power : NativeFloatCode (L := L) (reserved := reserved) ρ W
        (fun j => nativeFloatScaleL j (fun d => lowE L (.lt e (.lit 0)) d reserved)
          (fun d => lowE L (WideFloat.index w e) d reserved)) powerValue := by
      intro fp K d c top hc ht m pc pre
      exact (scale hc ht m pc pre).mono
        (fun word hw => wideFloat_power_decode z (integerFloatIndex z.natAbs) word hw)
    have multiplied : NativeFloatCode (L := L) (reserved := reserved) ρ W
        (fun j => nativeFPWordL (.mul .f64) j
          (nativeIntegerFloatL true j (fun d => lowE L (WideFloat.guard w e) d reserved))
          (nativeFloatScaleL (j + 1) (fun d => lowE L (.lt e (.lit 0)) d reserved)
            (fun d => lowE L (WideFloat.index w e) d reserved)))
        (Float.mul retainedValue powerValue) := by
      intro fp K d c top hc ht m pc pre
      exact nativeFloatMulL_ok
        (a := fun (j : Nat) => nativeIntegerFloatL true j
          (fun (k : Nat) => lowE L (WideFloat.guard w e) k reserved))
        (b := fun (j : Nat) => nativeFloatScaleL j
          (fun (k : Nat) => lowE L (.lt e (.lit 0)) k reserved)
          (fun (k : Nat) => lowE L (WideFloat.index w e) k reserved))
        (x := retainedValue) (y := powerValue) converted power hc ht m pc pre
    have numeric : Float.mul retainedValue powerValue = gleitAusInt z := wideFloat_numeric z big
    intro fp K d c top hc ht m pc pre
    exact (multiplied hc ht m pc pre).mono (fun word decoded => decoded.trans numeric)
  have chosen : NativeFloatCode (L := L) (reserved := reserved) ρ W
      (fun d => wideComputedFloatOfE L e d reserved)
      (if decide ((z.natAbs : Int) < 2 ^ 55) then gleitAusInt z else gleitAusInt z) := by
    intro fp K d c top hc ht m pc pre
    exact nativeFloatChooseL_ok
      (flag := decide ((z.natAbs : Int) < 2 ^ 55)) (yv := gleitAusInt z) (nv := gleitAusInt z)
      (condition := fun (j : Nat) => lowE L (.lt (WideFloat.magnitude w e) (.lit (2 ^ 55))) j reserved)
      (yes := fun (j : Nat) => nativeIntegerFloatL true j
        (fun (k : Nat) => lowE L (WideFloat.small e) k reserved))
      (no := fun (j : Nat) => nativeFPWordL (.mul .f64) j
        (nativeIntegerFloatL true j (fun (k : Nat) => lowE L (WideFloat.guard w e) k reserved))
        (nativeFloatScaleL (j + 1) (fun (k : Nat) => lowE L (.lt e (.lit 0)) k reserved)
          (fun (k : Nat) => lowE L (WideFloat.index w e) k reserved)))
      condition small large hc ht m pc pre
  intro fp K d c top hc ht m pc pre
  simpa only [ite_self] using chosen (fp := fp) (K := K) (d := d) (c := c) (top := top) hc ht m pc pre

/-- The former complete-word guarantee is retained also for overflow to signed
    infinity. Integer conversion is never NaN; this is derived internally. -/
theorem wideComputedFloatOfE_ok {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    {σ₀ σ : World D} (same : σ₀ = σ) (lay : LayIn L)
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (world : ∀ m, W m → WeltAt m L σ)
    (reserved : Nat) :
    WordCode (L := L) (reserved := reserved) ρ W (fun d => wideComputedFloatOfE L e d reserved)
      (gleitAusInt (eval σ₀ e σ ρ).n).toBits.toBitVec := by
  intro fp K d c top hc ht m pc pre
  exact (wideComputedFloatOfE_value_ok e same lay world reserved hc ht m pc pre).mono
    (fun word decoded => nativeFloat_word_eq_nonNaN (RootNativeFloat.ofInt_not_nan _) decoded)

/-- All emitting branches consume the original expression theorem. The world,
    old/current-world identity, reservation and full memory footprint stay exact. -/
theorem computedFloatOfE_ok {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {σ₀ σ : World D}
    {m : Runner.Mem} {pc fp : Runner.W} {K d top reserved : Nat} {code : List II}
    (hc : computedFloatOfE L e d reserved = some (code, top))
    (hp : Pre L m pc fp K d code ρ W reserved) (ht : top ≤ K)
    (lay : LayIn L) (same : σ₀ = σ) (world : ∀ m, W m → WeltAt m L σ) :
    Ok m pc fp K d code (· = (gleitAusInt (eval σ₀ e σ ρ).n).toBits.toBitVec) := by
  have child : WordCode (L := L) (reserved := reserved) ρ W
      (fun j => lowE L e j reserved) (BitVec.ofInt 64 (eval σ₀ e σ ρ).n) := by
    intro fp K d c top he ht m pc pre
    exact (lowE_ok (same := fun _ => same) σ₀ σ world lay e d c top he ht m pc ρ pre).word trivial
  have lower := (eval σ₀ e σ ρ).lo_le
  have upper := (eval σ₀ e σ ρ).le_hi
  unfold computedFloatOfE at hc
  split at hc
  · next range =>
    exact (nativeIntegerFloatL_source_ok true (eval σ₀ e σ ρ).n ⟨by omega, by omega⟩
      child hc ht m pc hp).mono
        (fun word decoded => nativeFloat_word_eq_nonNaN (RootNativeFloat.ofInt_not_nan _) decoded)
  · split at hc
    · next range =>
      exact (nativeIntegerFloatL_source_ok false (eval σ₀ e σ ρ).n ⟨by omega, by omega⟩
        child hc ht m pc hp).mono
          (fun word decoded => nativeFloat_word_eq_nonNaN (RootNativeFloat.ofInt_not_nan _) decoded)
    · exact wideComputedFloatOfE_ok e same lay world reserved hc ht m pc hp

end Gabbro.Stage0.Senke
