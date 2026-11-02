module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

set_option maxHeartbeats 2000000 in
/-- Execute the complete field materialization against actual retained memory.
    This proves the machine field expressions jointly, including preservation
    of every earlier output and the arbitrary reserved prefix. Identification
    of sign and exponent with the canonical IEEE result is a separate boundary. -/
theorem FloatNormalizeHead.write_fields
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp next : Runner.W}
    {K base reserved dst top signedSum exponent signBit : Nat} {code out : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r)
    (input : FB ≤ base) (sumInput : FB ≤ signedSum) (exInput : FB ≤ exponent)
    (retained : base+6 ≤ dst) (sumRetained : signedSum < dst)
    (exRetained : exponent < dst) (bitBound : signBit < 64)
    (sumWord exponentWord : Runner.W)
    (readSum : m.rd64 (slot fp (BitVec.ofNat 64 signedSum)) = some sumWord)
    (readExponent : m.rd64 (slot fp (BitVec.ofNat 64 exponent)) = some exponentWord)
    (compiled : floatStateSlotsL dst
      (floatNormalizedFieldsL base signedSum exponent signBit) = some (out,top))
    (room : top ≤ K) (slots : dst+5 ≤ K)
    (pre : Pre L m next fp K dst out ρ W reserved) :
    ∃ m', Star ⟨next,fp⟩ m ⟨next + BitVec.ofNat 64 (16*out.length),fp⟩ m' ∧
      Agree fp dst K m m' ∧
      ∀ i, (hi : i < 5) →
        m'.rd64 (slot fp (BitVec.ofNat 64 (dst+i))) = some
          (([Runner.IR.bool (sumWord.slt 0) * BitVec.ofNat 64 (2^signBit),
            exponentWord - BitVec.ofNat 64 count, BitVec.ofInt 64 (q/8),
            BitVec.ofInt 64 q &&& 7,
            1 - Runner.IR.bool (BitVec.ofInt 64 r == 0)] : List Runner.W)[i]'(by simpa using hi)) := by
  obtain ⟨env, envAt⟩ := frameWordEnv (L := L) (n := dst-FB) pre.frame (by omega)
  have loads : ∀ s v, FB ≤ s → s < dst →
      m.rd64 (slot fp (BitVec.ofNat 64 s)) = some v →
      WordCode (L := L) env (fun _ => True)
        (fun j => some ([ci 2 j s 0],j+1)) v := by
    intro s v low high read
    have idx : s-FB < dst-FB := by omega
    have slotEq : FB+(s-FB) = s := by omega
    obtain ⟨w, hr, he⟩ := ValueAt.word frameWordTy _ trivial (envAt _ (frameWordVar (dst-FB) (s-FB) idx))
    rw [frameWordVar_slot, slotEq, read] at hr
    cases hr
    change v = BitVec.ofInt 64 (env.get (frameWordVar (dst-FB) (s-FB) idx)).n at he
    rw [he]
    have slotInt : (FB : Int) + ((s-FB : Nat) : Int) = s := by omega
    intro fp' K' j c t hc ht mm pp hp
    exact frameWordLoad (L := L) (dst-FB) (s-FB) idx env
      (by simpa only [slotInt] using hc) ht mm pp hp
  have lq : WordCode (L := L) env (fun _ => True) _ _ := loads base _ input (by omega) head.readQ
  have lr : WordCode (L := L) env (fun _ => True) _ _ := loads (base+1) _ (by omega) (by omega) head.readR
  have lc : WordCode (L := L) env (fun _ => True) _ _ := loads (base+5) _ (by omega) (by omega) head.readCount
  have ls : WordCode (L := L) env (fun _ => True) _ _ := loads signedSum _ sumInput sumRetained readSum
  have le : WordCode (L := L) env (fun _ => True) _ _ := loads exponent _ exInput exRetained readExponent
  have zero : WordCode (L := L) env (fun _ => True) _ _ := WordCode.const (L := L) (ρ := env) (W := fun _ => True) 0 (by decide)
  have sign : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin ls zero
    (g := fun a b => some (Runner.IR.bool (a.slt b)))
    rfl rfl (by decide : 13 < 256)
  have signField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin sign
    (WordCode.konst (2^signBit) (by exact Nat.pow_lt_pow_right (by decide) bitBound))
    (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
  have exponentField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin le lc
    (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
  have div := sdiv_w (a := q) (b := 8)
    (by have := head.quotient; omega) (by have := head.quotient; omega)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Gabbro.Grammatik.Int.tdiv_eq_ediv_nonneg head.quotient.1] at div
  have quotientField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin lq (WordCode.const 8 (by decide)) div
    (rfl : op 6 = bin sdiv) (by decide : 6 < 256)
  have guardField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin lq (WordCode.const 7 (by decide))
    (g := fun a b => some (a &&& b)) rfl rfl (by decide : 8 < 256)
  have same : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin lr zero
    (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
  have stickyField : WordCode (L := L) env (fun _ => True) _ _ := WordCode.bin (WordCode.const 1 (by decide)) same
    (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
  have pre' : Pre L m next fp K dst out env (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx]; omega, pre.small, pre.frame, pre.code,
      pre.far, envAt, trivial, wstab_true _ _⟩
  let values : Nat → Runner.W := fun i =>
    if i = 0 then Runner.IR.bool (sumWord.slt 0) * BitVec.ofNat 64 (2^signBit)
    else if i = 1 then exponentWord - BitVec.ofNat 64 count
    else if i = 2 then BitVec.ofInt 64 (q/8)
    else if i = 3 then BitVec.ofInt 64 q &&& 7
    else 1 - Runner.IR.bool (BitVec.ofInt 64 r == 0)
  obtain ⟨m', run, agree, reads⟩ := floatStateSlotsL_ok (L := L) (ρ := env) (W := fun _ => True)
    (base := dst) (top := top) (code := out) (K := K) (reserved := 0) (fp := fp)
    (floatNormalizedFieldsL base signedSum exponent signBit) values compiled room (by simpa [floatNormalizedFieldsL] using slots)
    (by
      intro i hi c t hc ht mm pp hp
      have bound : i < 5 := by simpa [floatNormalizedFieldsL] using hi
      interval_cases i <;> dsimp only [values] <;>
        dsimp only [floatNormalizedFieldsL, List.getElem_cons_zero, List.getElem_cons_succ] at hc
      · exact signField hc ht mm pp hp
      · exact exponentField hc ht mm pp hp
      · exact quotientField hc ht mm pp hp
      · exact guardField hc ht mm pp hp
      · exact stickyField hc ht mm pp hp)
    m next pre'
  refine ⟨m', run, agree, ?_⟩
  intro i hi
  interval_cases i
  · simpa [values] using reads 0 (by simp [floatNormalizedFieldsL])
  · simpa [values] using reads 1 (by simp [floatNormalizedFieldsL])
  · simpa [values] using reads 2 (by simp [floatNormalizedFieldsL])
  · simpa [values] using reads 3 (by simp [floatNormalizedFieldsL])
  · simpa [values] using reads 4 (by simp [floatNormalizedFieldsL])

#print axioms FloatNormalizeHead.write_fields

/-- Carry a source dyadic denominator through the canonical normalizer.
    `scale + 3` is the source denominator exponent; three bits are consumed
    by the emitted guard split. The output exponent changes with that scale,
    while quotient and exact remainder follow from the executed loop head. -/
theorem FloatNormalizeHead.normQD_source_output
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p scale : Nat) :
    let nd := Gleitkomma.normQD p ((p : Int)-1-count-scale)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale))
    nd.1 / nd.2 = (q/8).toNat ∧
    nd.1 % nd.2 = ((q%8).toNat * 2^(distance+originDistance) +
      r.toNat * 2^originDistance) * 2^scale ∧
    nd.2 = (8 * 2^(distance+originDistance)) * 2^scale := by
  have shift : (p : Int)-1-((p : Int)-1-count-scale) = (count+scale : Nat) := by
    push_cast; omega
  have pair := head.normQD_output p
  simp only [Gleitkomma.normQD, show (p : Int)-1-((p : Int)-1-count) = count by omega,
    shift, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast] at pair ⊢
  rw [pow_add (2:Nat) count scale, pow_add (2:Nat) (distance+originDistance) scale]
  simp only [← Nat.mul_assoc]
  rw [Nat.mul_div_mul_right _ _ (by positivity : 0 < (2:Nat)^scale),
    Nat.mul_mod_mul_right]
  exact ⟨pair.1, congrArg (· * 2^scale) pair.2.1, True.intro⟩

#print axioms FloatNormalizeHead.normQD_source_output

/-- A target derived from format precision supplies the hidden bit after
    the actual three-bit quotient split, for every precision. -/
theorem floatGuardTarget_hiddenBit (p : Nat) (q : Int)
    (reached : (2 : Int)^(p-1+3) ≤ q) :
    (2 : Int)^(p-1) ≤ q/8 := by
  have power : (2 : Int)^(p-1+3) = 8 * 2^(p-1) := by
    rw [pow_add]; ring
  rw [power] at reached
  omega

theorem floatGuardTarget_hiddenBit_zeuge :
    (2 : Int)^52 ≤ (2^55 : Int)/8 ∧
    (2 : Int)^23 ≤ (2^26 : Int)/8 := by
  exact ⟨floatGuardTarget_hiddenBit 53 (2^55) (by decide),
    floatGuardTarget_hiddenBit 24 (2^26) (by decide)⟩

#print axioms floatGuardTarget_hiddenBit
#print axioms floatGuardTarget_hiddenBit_zeuge

/-- Every reached head supplies bounded canonical output fields, for any
    precision and source scale. No output-field bounds are caller premises.
    This word bound does not assert the tighter format normalization bound. -/
theorem FloatNormalizeHead.normQD_source_bounds
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p scale : Nat) :
    let nd := Gleitkomma.normQD p ((p : Int)-1-count-scale)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale))
    0 < nd.2 ∧ nd.1 / nd.2 < 2^58 ∧ nd.1 % nd.2 < nd.2 ∧
      (q%8).toNat < 8 := by
  dsimp only
  have fields := head.normQD_source_output p scale
  have positive : 0 < (8 * 2^(distance+originDistance) : Nat) * 2^scale := by
    positivity
  have denominator := fields.2.2
  have denPositive : 0 < (Gleitkomma.normQD p ((p : Int)-1-count-scale)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale))).2 := by
    rw [denominator]
    exact positive
  refine ⟨denPositive, ?_, Nat.mod_lt _ denPositive, ?_⟩
  · rw [fields.1]
    have := head.quotient
    have : q / 8 < (2^58 : Int) := by omega
    omega
  · have lo := Int.emod_nonneg q (by decide : (8 : Int) ≠ 0)
    have hi := Int.emod_lt_of_pos q (by decide : (0 : Int) < 8)
    omega

#print axioms FloatNormalizeHead.normQD_source_bounds

/-- Canonical rounding of the source-scaled rational is exactly the emitted
    guard/sticky decision for every reached head. This includes both tie
    parities and arbitrarily large denominator distances, uniformly in p. -/
theorem FloatNormalizeHead.normQ_source_guard
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p scale : Nat) :
    Gleitkomma.normQ p ((p : Int)-1-count-scale)
      (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale)) =
      Gleitkomma.rundeInt (q/8).toNat
        (2 * (q%8).toNat + if r = 0 then 0 else 1) 16 := by
  have fields := head.normQD_source_output p scale
  have ranges := head.output_ranges
  let den : Nat := 2^(distance+originDistance) * 2^scale
  let rest : Nat := r.toNat * 2^originDistance * 2^scale
  have hd : 0 < den := by dsimp [den]; positivity
  have tail : r.toNat * 2^originDistance < (2 : Nat)^(distance+originDistance) := by
    apply Int.ofNat_lt.mp
    push_cast
    rw [Int.toNat_of_nonneg head.remainder.1]
    exact ranges.2.2.2.2.2
  have hr : rest < den := Nat.mul_lt_mul_of_pos_right tail (by positivity)
  have hg : (q%8).toNat < 8 := by
    have := ranges.2.2.1
    have := ranges.2.2.2.1
    omega
  have hz : rest = 0 ↔ r = 0 := by
    simp only [rest, Nat.mul_eq_zero, pow_ne_zero _ (by decide : (2 : Nat) ≠ 0),
      or_false]
    have := head.remainder.1
    omega
  unfold Gleitkomma.normQ
  rw [fields.1, fields.2.1, fields.2.2]
  have remEq : ((q%8).toNat * 2^(distance+originDistance) +
      r.toNat * 2^originDistance) * 2^scale = (q%8).toNat * den + rest := by
    dsimp [den, rest]; ring
  have denEq : (8 * 2^(distance+originDistance)) * 2^scale = 8 * den := by
    dsimp [den]; ring
  rw [remEq, denEq, floatGuardSticky_round _ _ _ _ hd hr hg]
  simp only [hz]

#print axioms FloatNormalizeHead.normQ_source_guard

/-- The emitted rounding fragment implements the canonical source-scaled
    normQ for every reached head. Field producers still carry their ordinary
    execution contracts; format-specific packing and operand entry are separate. -/
theorem FloatNormalizeHead.round_source_ok
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat} {code : List II}
    {origin target q r : Int} {originDistance budget fuel count distance : Nat}
    (head : FloatNormalizeHead L ρ W pc fp K base reserved code origin
      originDistance budget target m fuel count distance q r) (p scale : Nat)
    {quotient guard sticky : Nat → Option (List II × Nat)}
    (hq : WordCode (L := L) ρ W quotient (BitVec.ofNat 64 (q/8).toNat))
    (hg : WordCode (L := L) ρ W guard (BitVec.ofNat 64 (q%8).toNat))
    (hs : WordCode (L := L) ρ W sticky
      (BitVec.ofNat 64 (if r = 0 then 0 else 1))) :
    WordCode (L := L) ρ W (fun j => floatGuardRoundL j quotient guard sticky)
      (BitVec.ofNat 64 (Gleitkomma.normQ p ((p : Int)-1-count-scale)
        (origin.toNat * 2^distance) (8 * 2^(distance+originDistance+scale)))) := by
  have hd : 0 < (2 : Nat)^distance := by positivity
  have hr : r.toNat < (2 : Nat)^distance := by
    have := head.remainder
    apply Int.ofNat_lt.mp
    push_cast
    rw [Int.toNat_of_nonneg this.1]
    exact this.2.2
  have hgBound : (q%8).toNat < 8 := by
    have lo := Int.emod_nonneg q (by decide : (8 : Int) ≠ 0)
    have hi := Int.emod_lt_of_pos q (by decide : (0 : Int) < 8)
    omega
  have hz : r.toNat = 0 ↔ r = 0 := by
    have := head.remainder.1
    omega
  have hs' : WordCode (L := L) ρ W sticky
      (BitVec.ofNat 64 (if r.toNat = 0 then 0 else 1)) := by
    intro fp' K' j c t hc ht mm pp hp
    simpa only [hz] using hs hc ht mm pp hp
  have rounded : WordCode (L := L) ρ W
      (fun j => floatGuardRoundL j quotient guard sticky)
      (BitVec.ofNat 64 (Gleitkomma.rundeInt (q/8).toNat
        ((q%8).toNat * 2^distance + r.toNat) (8 * 2^distance))) := by
    intro fp' K' j c t hc ht mm pp hp
    exact floatGuardRoundL_ok (q/8).toNat (q%8).toNat r.toNat
      (2^distance) hd hr hgBound hq hg hs' hc ht mm pp hp
  rw [floatGuardSticky_round _ _ _ _ hd hr hgBound] at rounded
  simp only [hz] at rounded
  rw [head.normQ_source_guard p scale]
  intro fp' K' j c t hc ht mm pp hp
  exact rounded hc ht mm pp hp

#print axioms FloatNormalizeHead.round_source_ok

omit [Kern] in
/-- Bounds for the actual finite candidate's decoded input words. They follow
    from the packed source operand, including either zero sign and subnormals;
    neither an exponent slot nor a magnitude slot is assumed correct. The
    three guard bits leave room for signed comparisons and a sum of two inputs. -/
theorem floatFiniteAdd_input_bounds (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a : Gleitkomma.GBits F) (valid : Gleitkomma.wf F a)
    (finite : a.bexp ≠ F.bexpMax) :
    let w := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
    let e := (floatFieldWord w F.fracBits F.ebits).toNat
    let m := (floatFieldWord w 0 F.fracBits).toNat +
      (if e = 0 then 0 else 2^F.fracBits)
    1 ≤ max e 1 ∧ max e 1 < F.bexpMax ∧
      8*m < 2^(F.fracBits+4) ∧ 8*m < 2^56 := by
  obtain ⟨fraction, exponent⟩ := floatFieldWord_canonical F dense width a valid
  dsimp only
  rw [fraction, exponent]
  have hb := valid.1
  have hf := valid.2
  have hp : 0 < (2^F.fracBits : Nat) := Nat.pow_pos (by decide)
  have magnitude : a.frac + (if a.bexp = 0 then 0 else 2^F.fracBits) <
      2 * 2^F.fracBits := by
    split <;> omega
  have scale : (2 : Nat)^(F.fracBits+4) = 16 * 2^F.fracBits := by
    rw [Nat.pow_add]; omega
  have cap : (2 : Nat)^(F.fracBits+4) ≤ 2^56 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨Nat.le_max_right _ _, ?_, ?_, ?_⟩
  · omega
  · rw [scale]; omega
  · rw [scale] at cap; omega

omit [Kern] in
/-- Canonical finite operands bound the ordered alignment distance and both
    guard-extended significands. The distance bound includes subnormals and
    either operand order; it is not a premise about a manually filled slot. -/
theorem floatFiniteAdd_ordered_input_bounds (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax) :
    let wa := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
    let wb := BitVec.ofNat 64 (Gleitkomma.zuBits F b)
    let ea := max (floatFieldWord wa F.fracBits F.ebits).toNat 1
    let eb := max (floatFieldWord wb F.fracBits F.ebits).toNat 1
    let ma := 8*((floatFieldWord wa 0 F.fracBits).toNat +
      if (floatFieldWord wa F.fracBits F.ebits).toNat = 0 then 0 else 2^F.fracBits)
    let mb := 8*((floatFieldWord wb 0 F.fracBits).toNat +
      if (floatFieldWord wb F.fracBits F.ebits).toNat = 0 then 0 else 2^F.fracBits)
    max ea eb - min ea eb ≤ F.bexpMax-2 ∧
      ma + mb < 2^57 ∧ ma < 2^56 ∧ mb < 2^56 := by
  have ba := floatFiniteAdd_input_bounds F dense width precision exponents a ha fa
  have bb := floatFiniteAdd_input_bounds F dense width precision exponents b hb fb
  dsimp only at ba bb ⊢
  have hi : max
      (max (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a)) F.fracBits F.ebits).toNat 1)
      (max (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) F.fracBits F.ebits).toNat 1)
      < F.bexpMax := max_lt ba.2.1 bb.2.1
  have lo : 1 ≤ min
      (max (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a)) F.fracBits F.ebits).toNat 1)
      (max (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) F.fracBits F.ebits).toNat 1) :=
    le_min ba.1 bb.1
  omega

omit [Kern] in
/-- Joint finite fixtures attain the maximum distance in both formats: a
    negative minimum subnormal and a positive maximum finite operand. -/
theorem floatFiniteAdd_ordered_input_bounds_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      let a : Gleitkomma.GBits F := ⟨true,0,1⟩
      let b : Gleitkomma.GBits F := ⟨false,F.bexpMax-1,2^F.fracBits-1⟩
      let wa := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
      let wb := BitVec.ofNat 64 (Gleitkomma.zuBits F b)
      let ea := max (floatFieldWord wa F.fracBits F.ebits).toNat 1
      let eb := max (floatFieldWord wb F.fracBits F.ebits).toNat 1
      Gleitkomma.wf F a ∧ Gleitkomma.wf F b ∧
      a.bexp ≠ F.bexpMax ∧ b.bexp ≠ F.bexpMax ∧
      max ea eb - min ea eb = F.bexpMax-2 := by
  intro F member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

#print axioms floatFiniteAdd_ordered_input_bounds_zeuge

#print axioms floatFiniteAdd_ordered_input_bounds

omit [Kern] in
/-- Both supported formats satisfy all generic decoding premises jointly.
    The operand fixture crosses the hidden-bit boundary without a normal
    exponent and retains a negative sign in its packed representation. -/
theorem floatFiniteAdd_input_bounds_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      let a : Gleitkomma.GBits F := ⟨true, 0, 1⟩
      let w := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
      let e := (floatFieldWord w F.fracBits F.ebits).toNat
      let m := (floatFieldWord w 0 F.fracBits).toNat +
        (if e = 0 then 0 else 2^F.fracBits)
      1 ≤ max e 1 ∧ max e 1 < F.bexpMax ∧
        8*m < 2^(F.fracBits+4) ∧ 8*m < 2^56 := by
  intro F member
  apply floatFiniteAdd_input_bounds
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals first | exact Gleitkomma.f32_dicht | exact Gleitkomma.f64_dicht | decide +kernel

#print axioms floatFiniteAdd_input_bounds
#print axioms floatFiniteAdd_input_bounds_zeuge

end Gabbro.Stage0.Senke
