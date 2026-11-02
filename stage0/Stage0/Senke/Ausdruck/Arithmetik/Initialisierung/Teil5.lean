module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil4

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

theorem floatFiniteAddL_read_fields {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (frac : F.fracBits < 64) (mask : 2^F.ebits-1 < 2^64)
    (fracMask : 2^F.fracBits-1 < 2^64) (hiddenBound : 2^F.fracBits < 2^64)
    (room : top ≤ K) (slots : dst+9 ≤ K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ executed tail m', code = executed ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*executed.length),fp⟩ m' ∧
      Agree fp (dst+1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+1))) = some wa ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+2))) = some wb ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+3))) =
        some (floatFieldWord wa (F.fracBits+F.ebits) 1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+4))) =
        some (floatFieldWord wb (F.fracBits+F.ebits) 1) ∧
      (∀ i, i < 4 → m'.rd64 (slot fp (BitVec.ofNat 64 (dst+5+i))) =
        some (finiteAddRemainingValue F wa wb i)) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*executed.length)) fp K (dst+9) tail ρ W reserved ∧
      ∃ inputTop, floatStateSlotsL (dst+1)
        ([a,b,
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (dst+1) 0],k+1)),
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (dst+2) 0],k+1))] ++
          finiteAddRemaining F dst) = some (executed,inputTop) := by
  obtain ⟨ca,ta,cb,tb,cf,tf,cg,tg,remaining,rt,tail,ha,hb,hf,hg,hr,hcode,hta,htb,htf,htg,htr⟩ :=
    floatFiniteAddL_remaining_code F dst a b compiled
  rw [hcode] at pre
  obtain ⟨m1,runA,agreeA,w,readA,valueA⟩ :=
    producerA ca ta ha (by omega) m pc pre.left.left
  subst w
  have preB := pre.left.next agreeA (show dst+1 ≤ dst+2 by omega) (by omega)
  obtain ⟨m2,runB,agreeB,w,readB,valueB⟩ :=
    producerB cb tb hb (by omega) m1 _ preB
  subst w
  have agreeAB := agreeA.trans (agreeB.mono (show dst+1 ≤ dst+2 by omega))
  have readA2 := slotRead_agree preB.frame agreeB (by omega) (by omega) readA
  have preF := pre.next agreeAB (show dst+1 ≤ dst+3 by omega) (by omega)
  obtain ⟨m3,runF,agreeF,w,readF,valueF⟩ :=
    floatFieldL_retained (input := dst+1) (dst := dst+3) (F.fracBits+F.ebits) 1 width (by decide) wa hf
      (by omega) lower (by omega) readA2 preF.left
  subst w
  have preG := preF.next agreeF (show dst+3 ≤ dst+4 by omega) (by omega)
  have readB3 := slotRead_agree preF.frame agreeF (by omega) (by omega) readB
  obtain ⟨m4,runG,agreeG,w,readG,valueG⟩ :=
    floatFieldL_retained (input := dst+2) (dst := dst+4) (F.fracBits+F.ebits) 1 width
      (by decide) wb hg (by omega) (by omega) (by omega) readB3 preG.left
  subst w
  have agreeFG := agreeF.trans (agreeG.mono (show dst+3 ≤ dst+4 by omega))
  have preR := preG.next agreeG (show dst+4 ≤ dst+5 by omega) (by omega)
  have readA4 := slotRead_agree preF.frame agreeFG (by omega) (by omega) readA2
  have readB4 := slotRead_agree preF.frame agreeFG (by omega) (by omega) readB
  obtain ⟨m5,runR,agreeR,reads,rest⟩ := retainedWordCodes_ok (L := L)
    (finiteAddRemaining F dst) (finiteAddRemainingValue F wa wb) (by
      intro Δ η loads
      exact finiteAddRemaining_sound η F dst wa wb frac mask fracMask hiddenBound
        (loads (dst+1) wa lower (by omega) readA4)
        (loads (dst+2) wb (by omega) (by omega) readB4))
    hr (by omega) (by omega) (by simpa [finiteAddRemaining] using slots) preR
  have runPrefix := ((runA.trans runB).trans
    (by simpa only [List.length_append, pc_add] using runF)).trans
      (by simpa only [List.length_append, pc_add] using runG)
  refine ⟨(((ca++cb)++cf)++cg)++remaining,tail,m5,
    by simpa [List.append_assoc] using hcode,?_,
    agreeAB.trans ((agreeFG.trans (agreeR.mono (by omega))).mono (by omega)),
    slotRead_agree preR.frame agreeR (by omega) (by omega) readA4,
    slotRead_agree preR.frame agreeR (by omega) (by omega) readB4,
    slotRead_agree preR.frame agreeR (by omega) (by omega)
      (slotRead_agree preG.frame agreeG (by omega) (by omega) readF),
    slotRead_agree preR.frame agreeR (by omega) (by omega) readG,?_,?_,?_⟩
  · simpa only [List.length_append, pc_add] using runPrefix.trans
      (by simpa only [List.length_append, pc_add] using runR)
  · simpa only [finiteAddRemaining, List.length_cons, List.length_nil,
      List.length_append, pc_add] using reads
  · simpa only [finiteAddRemaining, List.length_cons, List.length_nil,
      List.length_append, pc_add, Nat.add_assoc] using rest

  · refine ⟨max ta (max tb (max tf (max tg rt))), ?_⟩
    simp only [List.cons_append, List.nil_append]
    rw [floatStateSlotsL, ha]
    simp only [bind, pure, Option.bind_some]
    rw [floatStateSlotsL]
    simp only [Nat.add_assoc, hb, bind, pure, Option.bind_some]
    rw [floatStateSlotsL]
    simp only [Nat.add_assoc, hf, bind, pure, Option.bind_some]
    rw [floatStateSlotsL]
    simp only [Nat.add_assoc, hg, bind, pure, Option.bind_some, hr,
      List.append_assoc]

#print axioms floatFiniteAddL_read_fields

theorem floatFiniteAddL_read_fields_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 25 ≤ K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ operandCode tail m',
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp 17 K m m' ∧
      m'.rd64 (slot fp 17) = some 7 ∧ m'.rd64 (slot fp 18) = some 11 ∧
      m'.rd64 (slot fp 19) = some (floatFieldWord 7 (F.fracBits+F.ebits) 1) ∧
      m'.rd64 (slot fp 20) = some (floatFieldWord 11 (F.fracBits+F.ebits) 1) ∧
      (∀ i, i < 4 → m'.rd64 (slot fp (BitVec.ofNat 64 (21+i))) =
        some (finiteAddRemainingValue F 7 11 i)) ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 25 tail ρ W 13 ∧
      ∃ inputTop, floatStateSlotsL (16+1)
        ([ (fun (j : Nat) => some ([ci 1 j 7 0],j+1)), (fun (j : Nat) => some ([ci 1 j 11 0],j+1)),
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (16+1) 0],k+1)),
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (16+2) 0],k+1))] ++
          finiteAddRemaining F 16) = some (operandCode,inputTop) := by
  apply floatFiniteAddL_read_fields F 16
    (fun j => some ([ci 1 j 7 0],j+1))
    (fun j => some ([ci 1 j 11 0],j+1)) 7 11
    (top := ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> decide +kernel
  · decide +kernel
  all_goals try { simp only [List.mem_cons, List.not_mem_nil, or_false] at format
                  rcases format with rfl | rfl <;> decide +kernel }
  · exact room
  · exact slots
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre


#print axioms floatFiniteAddL_read_fields_zeuge

/-- Successful whole compilation fixes the continuation after all eight input
    producers. In particular the ordering prefix uses the actual retained
    exponent and magnitude slots, and its three scratch slots start at dst+9.
    This is a code boundary only; it does not assert execution of the swap. -/
theorem floatFiniteAddL_order_continuation (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code,top)) :
    ∃ inputs inputTop tail,
      floatStateSlotsL (dst+1)
        ([a,b,
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (dst+1) 0],k+1)),
          fun j => floatFieldL (F.fracBits+F.ebits) 1 j
            (fun k => some ([ci 2 k (dst+2) 0],k+1))] ++
          finiteAddRemaining F dst) = some (inputs,inputTop) ∧
      code = inputs ++
        ([ci 13 (dst+9) (dst+5) (dst+6),
          ci 14 (dst+10) (dst+5) (dst+6),
          ci 13 (dst+11) (dst+7) (dst+8),
          ci 5 (dst+10) (dst+10) (dst+11),
          ci 9 (dst+9) (dst+9) (dst+10)] ++ tail) ∧
      inputTop ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  refine ⟨inputs.1,inputs.2,code.drop (inputs.1.length+5),?_,?_,?_⟩
  · simpa [finiteAddRemaining] using hi
  · simp only [Option.some.injEq, Prod.mk.injEq] at result
    rw [← result.1]
    simp [List.drop_append, List.append_assoc]
  · simp only [Option.some.injEq, Prod.mk.injEq] at result
    omega

#print axioms floatFiniteAddL_order_continuation

/-- The first ordering instruction consumes the two retained effective
    exponents and returns the actual continuation Pre, at the same scratch
    boundary. It makes no universally quantified fixed-slot WordCode claim. -/
theorem floatFiniteAddL_order_first {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {tail : List II} {ex ey : Runner.W}
    (room : dst+9 < K)
    (rx : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (ry : m.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey)
    (pre : Pre L m pc fp K (dst+9)
      ([ci 13 (dst+9) (dst+5) (dst+6)] ++ tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ m' ∧
      Agree fp (dst+9) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (Runner.IR.bool (ex.slt ey)) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey ∧
      Pre L m' (pc+16) fp K (dst+9) tail ρ W reserved := by
  obtain ⟨m',run,agree,w,read,value⟩ := eng_bin_ok (a := dst+5) (b := dst+6) (d := dst+9) pre.left room
    (by omega) (by omega) rx ry
    (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  subst w
  refine ⟨m',?_,agree,read,
    slotRead_agree pre.frame agree (by omega) (by omega) rx,
    slotRead_agree pre.frame agree (by omega) (by omega) ry,?_⟩
  · simpa using run
  · simpa using pre.next agree (Nat.le_refl _) (by omega)

#print axioms floatFiniteAddL_order_first

end Gabbro.Stage0.Senke
