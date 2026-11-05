/- The actual native-result range guard, with the original complete frame ABI. -/
module
public import NativeFloat.Hardware
public import Stage0.Senke.Gleit.Native.Values
public import Stage0.Senke.Ausdruck.Gleit.Bereich
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

private theorem finite_mask (word : Runner.W) :
    (Runner.readFloat word).hwIsFinite = !((word &&& (0x7ff0000000000000 : Runner.W)) ==
      (0x7ff0000000000000 : Runner.W)) := by
  have h := RootNativeFloat.finite_word_mask (UInt64.ofBitVec word)
  have same : (((UInt64.ofBitVec word) &&& 0x7ff0000000000000) == 0x7ff0000000000000) =
      ((word &&& (0x7ff0000000000000 : Runner.W)) ==
        (0x7ff0000000000000 : Runner.W)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← UInt64.toBitVec_inj, UInt64.toBitVec_and,
      UInt64.toBitVec_ofBitVec]
    rfl
  change (Runner.readFloat word).hwIsFinite =
    !(((UInt64.ofBitVec word) &&& 0x7ff0000000000000) == 0x7ff0000000000000) at h
  rwa [same] at h

/-- The range proof needs only the actual allocation context of its caller.
    The operand callback is the existing expression induction hypothesis. -/
theorem nativeFloatRangeL_at_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {fp : Runner.W} {K d top : Nat} {c : List II}
    {producer : Nat → Option (List II × Nat)} (lo hi : Int × Int) (x : GFloat)
    (source : ∀ j code ceiling, producer j = some (code, ceiling) → ceiling ≤ K →
      ∀ m pc, Pre L m pc fp K j code ρ W reserved →
        Ok m pc fp K j code (fun w => Runner.readFloat w = x))
    (emitted : floatRangeL d lo hi producer = some (c, top)) (fits : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (pre : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = Runner.IR.bool (floatRangeReject lo hi x)) := by
  let proves (a : Nat → Option (List II × Nat)) (P : Runner.W → Prop) :=
    ∀ j code ceiling, a j = some (code, ceiling) → ceiling ≤ K →
      ∀ m pc, Pre L m pc fp K j code ρ W reserved → Ok m pc fp K j code P
  have binary {a b : Nat → Option (List II × Nat)}
      {Pa Pb P : Runner.W → Prop} {o : Nat} {g : Runner.W → Runner.W → Option Runner.W}
      (ha : proves a Pa) (hb : proves b Pb)
      (hg : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r)
      (hop : op o = bin g) (ho : o < 256) :
      proves (fun j => wordL o j (a j) (b (j + 1))) P := by
    intro j code ceiling hc ht m pc hp
    exact wordL_ok hc ht (fun _ _ he ht => ha _ _ _ he ht)
      (fun _ _ he ht => hb _ _ _ he ht) hg hop ho hp
  have constant (v : GFloat) : proves (fun j => some (floatConstL v j)) (fun w => Runner.readFloat w = v) := by
    intro j code ceiling hc ht m pc hp
    cases hc
    exact (konstWL_ok 4 v.hwToBits.toNat (by exact v.hwToBits.toBitVec.isLt)
      (by simp only [floatConstL, konstWL, bin2] at ht; omega) hp).mono
        (fun w hw => by
          rw [hw]
          rw [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          exact nativeFloat_read_word v)
  have le {a b : Nat → Option (List II × Nat)} {av bv : GFloat}
      (ha : proves a (fun w => Runner.readFloat w = av))
      (hb : proves b (fun w => Runner.readFloat w = bv)) :
      proves (fun j => nativeFPWordL (.le .f64) j (a j) (b (j + 1)))
        (fun w => w = Runner.IR.bool (gleitLe av bv)) := by
    intro j code ceiling hc ht m pc hp
    refine nativeFPWordL_ok (.le .f64) (op_fp rfl) hc ht
      (fun _ _ he ht => ha _ _ _ he ht) (fun _ _ he ht => hb _ _ _ he ht) ?_ hp
    intro wa wb hx hy
    refine ⟨_, ?_, rfl⟩
    simp only [Runner.NativeFPEval, Runner.nativeFP, Runner.NativeFPValue.Matches,
      hx, hy]
    rfl
  have mask : proves (fun j => some (konstWL 4 0x7ff0000000000000 j)) (· = 0x7ff0000000000000) := by
    intro j code ceiling hc ht m pc hp
    exact WordCode.konst (L := L) (reserved := reserved) (ρ := ρ) (W := W)
      0x7ff0000000000000 (by decide) hc ht m pc hp
  have one : proves (fun j => some ([ci 1 j 1 0], j + 1)) (· = 1) := by
    intro j code ceiling hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  have masked : proves (fun j => wordL 8 j (producer j)
      (some (konstWL 4 0x7ff0000000000000 (j + 1))))
      (fun w => ∃ original, Runner.readFloat original = x ∧
        w = original &&& 0x7ff0000000000000) :=
    binary source mask (g := fun a b => some (a &&& b))
      (fun a b ha hb => ⟨_, rfl, a, ha, by rw [hb]⟩) rfl (by decide : 8 < 256)
  have equal := binary masked mask (g := fun a b => some (Runner.IR.bool (a == b)))
    (P := fun w => w = Runner.IR.bool (!gleitEndlich x))
    (fun a b ha hb => by
      obtain ⟨original, decoded, rfl⟩ := ha
      subst b
      refine ⟨_, rfl, ?_⟩
      have finite := finite_mask original
      rw [decoded] at finite
      rw [show gleitEndlich x = x.hwIsFinite from rfl, finite, Bool.not_not])
    rfl (by decide : 14 < 256)
  have inverted := binary equal one (g := fun a b => some (a ^^^ b))
    (P := fun w => w = Runner.IR.bool (gleitEndlich x))
    (fun a b ha hb => ⟨_, rfl, by
      rw [ha, hb]
      cases gleitEndlich x <;> rfl⟩)
    rfl (by decide : 10 < 256)
  have finite : proves (fun j => nativeFloatFiniteL j producer)
      (fun w => w = Runner.IR.bool (gleitEndlich x)) := inverted
  have lower := le (constant (bruch lo)) source
  have upper := le source (constant (bruch hi))
  have bounds := binary lower upper (g := fun a b => some (a &&& b))
    (P := fun w => w = Runner.IR.bool (gleitLe (bruch lo) x && gleitLe x (bruch hi)))
    (fun a b ha hb => ⟨_, rfl, by rw [ha, hb, bool_word, bool_word, and_word, ← bool_word]⟩)
    rfl (by decide : 8 < 256)
  have valid := binary finite bounds (g := fun a b => some (a &&& b))
    (P := fun w => w = Runner.IR.bool
      (gleitEndlich x && (gleitLe (bruch lo) x && gleitLe x (bruch hi))))
    (fun a b ha hb => ⟨_, rfl, by rw [ha, hb, bool_word, bool_word, and_word, ← bool_word]⟩)
    rfl (by decide : 8 < 256)
  have rejected := binary valid one (g := fun a b => some (a ^^^ b))
    (P := fun w => w = Runner.IR.bool (floatRangeReject lo hi x))
    (fun a b ha hb => ⟨_, rfl, by
      rw [ha, hb]
      unfold floatRangeReject
      cases gleitEndlich x && (gleitLe (bruch lo) x && gleitLe x (bruch hi)) <;> rfl⟩)
    rfl (by decide : 10 < 256)
  simp only [floatRangeL, Option.map_eq_some_iff] at emitted
  obtain ⟨⟨body, ceiling⟩, hb, he⟩ := emitted
  cases he
  exact rejected _ _ _ hb (by omega) m pc pre

/-- Allocation-polymorphic producers use exactly the same local guard proof. -/
theorem nativeFloatRangeL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {producer : Nat → Option (List II × Nat)} (lo hi : Int × Int) (x : GFloat)
    (source : NativeFloatCode (L := L) (reserved := reserved) ρ W producer x) :
    WordCode (L := L) (reserved := reserved) ρ W
      (fun d => floatRangeL d lo hi producer) (Runner.IR.bool (floatRangeReject lo hi x)) := by
  intro fp K d c top emitted fits m pc pre
  exact nativeFloatRangeL_at_ok lo hi x (fun _ _ _ hc ht => source hc ht)
    emitted fits pre

end Gabbro.Stage0.Senke
