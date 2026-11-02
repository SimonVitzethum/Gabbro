module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil4

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

omit [Kern] in
/-- Saturating alignment by a positive distance is bounded by half the input
    plus one sticky increment, with no premise about the discarded remainder. -/
theorem floatShiftJamWord_half_bound (a k : Runner.W) (positive : 0 < k.toNat) :
    (floatShiftJamWord a k).toNat ≤ a.toNat / 2 + 1 := by
  unfold floatShiftJamWord
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  let b := (Runner.IR.bool (!(a == ((a >>> k.toNat) <<< k.toNat)))).toNat
  change (a.toNat / 2^k.toNat ||| b) ≤ a.toNat / 2 + 1
  have bit : b ≤ 1 := by
    dsimp only [b]
    unfold Runner.IR.bool
    split <;> decide
  have halves : (a.toNat / 2^k.toNat ||| b) / 2 = (a.toNat / 2^k.toNat) / 2 := by
    rw [Nat.or_div_two, show b / 2 = 0 by omega, Nat.or_zero]
  have rem := Nat.mod_lt (a.toNat / 2^k.toNat ||| b) (by decide : 0 < 2)
  have division := Nat.mod_add_div (a.toNat / 2^k.toNat ||| b) 2
  have denominator : 2 ≤ 2^k.toNat := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) positive
    simpa using this
  have quotient := Nat.div_le_div_left (a := a.toNat) denominator (by decide)
  omega

#print axioms floatShiftJamWord_half_bound
omit [Kern] in
/-- Actual decoded word subtraction at unequal exponents is positive after
    saturating SHIFTJAM; no NONZERO or result-invariant premise is needed. -/
theorem finiteAddRemainingValue_unequal_positive (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax) :
    let v := finiteAddRemainingValue F
      (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F b))
    (v 1).toNat < (v 0).toNat →
      0 < (v 2 - floatShiftJamWord (v 3) (v 0-v 1)).toInt := by
  dsimp only
  let v := finiteAddRemainingValue F
    (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
    (BitVec.ofNat 64 (Gleitkomma.zuBits F b))
  change (v 1).toNat < (v 0).toNat →
    0 < (v 2 - floatShiftJamWord (v 3) (v 0-v 1)).toInt
  intro order
  have delta : 0 < (v 0-v 1).toNat := by
    rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def] using Nat.le_of_lt order)]
    omega
  have half := floatShiftJamWord_half_bound (v 3) (v 0-v 1) delta
  have gap := finiteAddRemainingValue_unequal F dense width precision exponents
    a b ha hb fa fb order
  change (v 3).toNat / 2 + 1 < (v 2).toNat at gap
  have bound := finiteAddRemainingValue_bounds F dense width precision exponents
    a b ha hb fa fb 2 (by decide)
  change (v 2).toNat < 2^56 at bound
  have qint : (v 2).toInt = ((v 2).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have jint : (floatShiftJamWord (v 3) (v 0-v 1)).toInt =
      ((floatShiftJamWord (v 3) (v 0-v 1)).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  rw [BitVec.toInt_sub, qint, jint, Int.bmod_eq_of_le (by omega) (by omega)]
  omega

#print axioms finiteAddRemainingValue_unequal_positive

omit [Kern] in
/-- Both precisions jointly realize strict SORT order, opposite signs, a
    subnormal smaller input, nonzero discarded bits, and positive subtraction. -/
theorem finiteAddRemainingValue_unequal_positive_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      let a : Gleitkomma.GBits F := ⟨false,5,1⟩
      let b : Gleitkomma.GBits F := ⟨true,0,2^F.fracBits-1⟩
      let v := finiteAddRemainingValue F
        (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
        (BitVec.ofNat 64 (Gleitkomma.zuBits F b))
      Gleitkomma.wf F a ∧ Gleitkomma.wf F b ∧
      a.bexp ≠ F.bexpMax ∧ b.bexp ≠ F.bexpMax ∧
      (v 1).toNat < (v 0).toNat ∧
      (v 3).toNat % 2^(v 0-v 1).toNat ≠ 0 ∧
      0 < (v 2 - floatShiftJamWord (v 3) (v 0-v 1)).toInt := by
  intro F member
  have format : F = Gleitkomma.f32 ∨ F = Gleitkomma.f64 := by simpa using member
  rcases format with rfl | rfl <;> decide +kernel

#print axioms finiteAddRemainingValue_unequal_positive_zeuge


/-- All four actual decoder expressions are sound in the reconstructed frame. -/
theorem finiteAddRemaining_sound {Δ : Ctx} (η : Env D Δ)
    (F : Gleitkomma.Format) (dst : Nat) (a b : Runner.W)
    (frac : F.fracBits < 64) (mask : 2^F.ebits-1 < 2^64)
    (fracMask : 2^F.fracBits-1 < 2^64) (hiddenBound : 2^F.fracBits < 2^64)
    (ha : WordCode (L := L) η (fun _ => True)
      (fun j => some ([ci 2 j (dst+1) 0],j+1)) a)
    (hb : WordCode (L := L) η (fun _ => True)
      (fun j => some ([ci 2 j (dst+2) 0],j+1)) b) :
    ∀ i, (hi : i < (finiteAddRemaining F dst).length) →
      WordCode (L := L) η (fun _ => True) (finiteAddRemaining F dst)[i]
        (finiteAddRemainingValue F a b i) := by
  have decoder : ∀ (p : Nat → Option (List II × Nat)) (w : Runner.W),
      WordCode (L := L) η (fun _ => True) p w →
      WordCode (L := L) η (fun _ => True)
        (fun j => wordL 3 j (floatFieldL F.fracBits F.ebits j p)
          (wordK 14 (j+1) (floatFieldL F.fracBits F.ebits (j+1) p) 0))
        (floatFieldWord w F.fracBits F.ebits + Runner.IR.bool (floatFieldWord w F.fracBits F.ebits == 0)) ∧
      WordCode (L := L) η (fun _ => True)
        (fun j => wordK 5 j
          (wordL 3 j (floatFieldL 0 F.fracBits j p)
            (wordL 5 (j+1)
              (wordL 4 (j+1) (some ([ci 1 (j+1) 1 0],j+2))
                (wordK 14 (j+2) (floatFieldL F.fracBits F.ebits (j+2) p) 0))
              (some (konstWL 4 (2^F.fracBits) (j+2))))) 8)
        ((floatFieldWord w 0 F.fracBits +
          (1 - Runner.IR.bool (floatFieldWord w F.fracBits F.ebits == 0)) * BitVec.ofNat 64 (2^F.fracBits)) * 8) := by
    intro p w hp
    have e : WordCode (L := L) η (fun _ => True) _ _ := floatFieldL_ok F.fracBits F.ebits frac mask hp
    have f : WordCode (L := L) η (fun _ => True) _ _ := floatFieldL_ok 0 F.fracBits (by decide) fracMask hp
    have z : WordCode (L := L) η (fun _ => True) _ _ := WordCode.const (L := L) (ρ := η) (W := fun _ => True) 0 (by decide)
    have one : WordCode (L := L) η (fun _ => True) _ _ := WordCode.const (L := L) (ρ := η) (W := fun _ => True) 1 (by decide)
    have eight : WordCode (L := L) η (fun _ => True) _ _ := WordCode.const (L := L) (ρ := η) (W := fun _ => True) 8 (by decide)
    have zero : WordCode (L := L) η (fun _ => True) _ _ := WordCode.bin e z (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
    have normal : WordCode (L := L) η (fun _ => True) _ _ := WordCode.bin one zero (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
    have hidden : WordCode (L := L) η (fun _ => True) _ _ := WordCode.bin normal (WordCode.konst (2^F.fracBits) hiddenBound)
      (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
    have mag : WordCode (L := L) η (fun _ => True) _ _ := WordCode.bin f hidden (g := fun a b => some (a+b)) rfl rfl (by decide : 3 < 256)
    exact ⟨WordCode.bin e zero (g := fun a b => some (a+b)) rfl rfl (by decide : 3 < 256),
      WordCode.bin mag eight (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)⟩
  intro i hi
  have bound : i < 4 := hi
  interval_cases i <;>
    intro fp K d c top hc ht mm pp hp
  all_goals simp only [finiteAddRemaining, List.getElem_cons_zero,
    List.getElem_cons_succ] at hc
  · simpa [finiteAddRemainingValue] using (decoder _ _ ha).1 hc ht mm pp hp
  · simpa [finiteAddRemainingValue] using (decoder _ _ hb).1 hc ht mm pp hp
  · simpa [finiteAddRemainingValue] using (decoder _ _ ha).2 hc ht mm pp hp
  · simpa [finiteAddRemainingValue] using (decoder _ _ hb).2 hc ht mm pp hp

#print axioms finiteAddRemaining_sound

theorem floatFiniteAddL_remaining_code (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code,top)) :
    ∃ ca ta cb tb cf tf cg tg remaining rt tail,
      a (dst+1) = some (ca,ta) ∧ b (dst+2) = some (cb,tb) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+3)
        (fun j => some ([ci 2 j (dst+1) 0],j+1)) = some (cf,tf) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+4)
        (fun j => some ([ci 2 j (dst+2) 0],j+1)) = some (cg,tg) ∧
      floatStateSlotsL (dst+5) (finiteAddRemaining F dst) = some (remaining,rt) ∧
      code = (ca ++ cb) ++ (cf ++ (cg ++ (remaining ++ tail))) ∧
      ta ≤ top ∧ tb ≤ top ∧ tf ≤ top ∧ tg ≤ top ∧ rt ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  rw [floatStateSlotsL] at hi
  simp only [bind, pure, Option.bind_eq_some_iff] at hi
  obtain ⟨av, hav, afterA, hb, inputEq⟩ := hi
  rw [floatStateSlotsL] at hb
  simp only [bind, pure, Option.bind_eq_some_iff] at hb
  obtain ⟨bv, hbv, afterB, hc, afterEq⟩ := hb
  rw [floatStateSlotsL] at hc
  simp only [bind, pure, Option.bind_eq_some_iff] at hc
  obtain ⟨fv, hfv, afterF, hd, fieldEq⟩ := hc
  rw [floatStateSlotsL] at hd
  simp only [bind, pure, Option.bind_eq_some_iff] at hd
  obtain ⟨gv, hgv, afterG, he, signEq⟩ := hd
  rcases afterG with ⟨gCode,gTop⟩
  rcases inputs with ⟨inputCode,inputTop⟩
  rcases afterA with ⟨aCode,aTop⟩
  rcases afterB with ⟨bCode,bTop⟩
  rcases afterF with ⟨fCode,fTop⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at inputEq afterEq fieldEq signEq result
  refine ⟨av.1,av.2,bv.1,bv.2,fv.1,fv.2,gv.1,gv.2,
    gCode,gTop,code.drop inputCode.length,hav,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using hbv
  · simpa [Nat.add_assoc] using hfv
  · simpa [Nat.add_assoc] using hgv
  · simpa [finiteAddRemaining, Nat.add_assoc] using he
  · calc
      code = inputCode ++ code.drop inputCode.length := by
        rw [← result.1]
        simp [List.drop_append, List.append_assoc]
      _ = _ := by
        rw [← inputEq.1, ← afterEq.1, ← fieldEq.1, ← signEq.1]
        simp only [List.append_assoc]
  all_goals omega

#print axioms floatFiniteAddL_remaining_code


end Gabbro.Stage0.Senke
