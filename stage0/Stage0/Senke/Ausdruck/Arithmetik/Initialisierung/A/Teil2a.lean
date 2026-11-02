module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil1

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


end Gabbro.Stage0.Senke
