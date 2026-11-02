module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil2a

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
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
