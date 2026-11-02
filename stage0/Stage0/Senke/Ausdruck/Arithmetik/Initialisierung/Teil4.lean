module
public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil4a

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil3

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

#print axioms floatFiniteAddL_sign_fields_code

/-- The four remaining producers, literally the exponent and magnitude
    expressions emitted by `floatFiniteAddL`. -/
def finiteAddRemaining (F : Gleitkomma.Format) (dst : Nat) :=
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  let field := fun start width j p => floatFieldL start width j p
  let exponent := fun p j => wordL 3 j (field F.fracBits F.ebits j p)
    (wordK 14 (j+1) (field F.fracBits F.ebits (j+1) p) 0)
  let magnitude := fun p j => wordK 5 j
    (wordL 3 j (field 0 F.fracBits j p)
      (wordL 5 (j+1)
        (wordL 4 (j+1) (some ([ci 1 (j+1) 1 0],j+2))
          (wordK 14 (j+2) (field F.fracBits F.ebits (j+2) p) 0))
        (some (konstWL 4 (2^F.fracBits) (j+2))))) 8
  [exponent (load (dst+1)), exponent (load (dst+2)),
    magnitude (load (dst+1)), magnitude (load (dst+2))]

def finiteAddRemainingValue (F : Gleitkomma.Format) (a b : Runner.W) (i : Nat) : Runner.W :=
  let w := if i % 2 = 0 then a else b
  let e := floatFieldWord w F.fracBits F.ebits
  if i < 2 then e + Runner.IR.bool (e == 0)
  else (floatFieldWord w 0 F.fracBits +
    (1 - Runner.IR.bool (e == 0)) * BitVec.ofNat 64 (2^F.fracBits)) * 8

omit [Kern] in
/-- Exact canonical decoder values retain the exponent/significand correlation
    needed by unequal-exponent subtraction after the actual SORT. -/
theorem finiteAddRemainingValue_canonical (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax)
    (i : Nat) (hi : i < 4) :
    let x := if i % 2 = 0 then a else b
    (finiteAddRemainingValue F
      (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) i).toNat =
      if i < 2 then max x.bexp 1
      else 8 * (x.frac + if x.bexp = 0 then 0 else 2^F.fracBits) := by
  have one (x : Gleitkomma.GBits F) (hx : Gleitkomma.wf F x)
      (fx : x.bexp ≠ F.bexpMax) :
      let w := BitVec.ofNat 64 (Gleitkomma.zuBits F x)
      let e := floatFieldWord w F.fracBits F.ebits
      let f := floatFieldWord w 0 F.fracBits
      (e + Runner.IR.bool (e == 0)).toNat = max x.bexp 1 ∧
      ((f + (1 - Runner.IR.bool (e == 0)) *
        BitVec.ofNat 64 (2^F.fracBits)) * 8).toNat =
        8 * (x.frac + if x.bexp = 0 then 0 else 2^F.fracBits) := by
    obtain ⟨fraction, exponent⟩ := floatFieldWord_canonical F dense width x hx
    have bounds := floatFiniteAdd_input_bounds F dense width precision exponents x hx fx
    dsimp only at bounds ⊢
    rw [fraction, exponent] at bounds
    have cap : (2 : Nat)^F.fracBits < 2^64 :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) precision) (by decide)
    have ecap : x.bexp < 2^64 := by
      have := (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F x))
        F.fracBits F.ebits).isLt
      rw [exponent] at this
      exact this
    have fcap : x.frac < 2^64 := lt_trans hx.2 cap
    have ez : (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F x))
        F.fracBits F.ebits == 0#64) = decide (x.bexp = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
        exponent, BitVec.toNat_zero]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [ez]
    norm_num only at cap ecap fcap
    by_cases hz : x.bexp = 0 <;>
      simp only [hz, ↓reduceIte] at bounds <;>
      simp only [hz, decide_true, decide_false, Runner.IR.bool, ↓reduceIte,
        Bool.false_eq_true, BitVec.ofNat_eq_ofNat, BitVec.sub_self,
        BitVec.sub_zero, BitVec.zero_mul, BitVec.one_mul, BitVec.add_zero,
        BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
        fraction, exponent] <;>
      norm_num only [BitVec.toNat_ofNat] <;>
      (try simp only [Nat.mod_eq_of_lt cap]) <;> omega
  have aa := one a ha fa
  have bb := one b hb fb
  interval_cases i <;> simp_all [finiteAddRemainingValue]

#print axioms finiteAddRemainingValue_canonical

omit [Kern] in
/-- Unequal exponents and nonzero fractions jointly witness the decoder
    correlation in both supported precisions, including a subnormal operand. -/
theorem finiteAddRemainingValue_canonical_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      let a : Gleitkomma.GBits F := ⟨false,2,1⟩
      let b : Gleitkomma.GBits F := ⟨true,0,2^F.fracBits-1⟩
      Gleitkomma.wf F a ∧ Gleitkomma.wf F b ∧
      a.bexp ≠ F.bexpMax ∧ b.bexp ≠ F.bexpMax ∧
      ∀ i, i < 4 →
        let x := if i % 2 = 0 then a else b
        (finiteAddRemainingValue F
          (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
          (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) i).toNat =
            if i < 2 then max x.bexp 1
            else 8*(x.frac + if x.bexp = 0 then 0 else 2^F.fracBits) := by
  intro F member
  have format : F = Gleitkomma.f32 ∨ F = Gleitkomma.f64 := by simpa using member
  have dense : F.dicht := by
    rcases format with rfl | rfl
    · exact Gleitkomma.f32_dicht
    · exact Gleitkomma.f64_dicht
  have width : F.ebits + F.fracBits + 1 ≤ 64 := by
    rcases format with rfl | rfl <;> decide +kernel
  have precision : F.fracBits ≤ 52 := by rcases format with rfl | rfl <;> decide +kernel
  have exponents : 1 < F.bexpMax := by rcases format with rfl | rfl <;> decide +kernel
  have ha : Gleitkomma.wf F ⟨false,2,1⟩ := by
    rcases format with rfl | rfl <;> decide +kernel
  have hb : Gleitkomma.wf F ⟨true,0,2^F.fracBits-1⟩ := by
    rcases format with rfl | rfl <;> decide +kernel
  have fa : 2 ≠ F.bexpMax := by rcases format with rfl | rfl <;> decide +kernel
  have fb : 0 ≠ F.bexpMax := by omega
  exact ⟨ha,hb,fa,fb,fun i hi =>
    finiteAddRemainingValue_canonical F dense width precision exponents
      ⟨false,2,1⟩ ⟨true,0,2^F.fracBits-1⟩ ha hb fa fb i hi⟩

#print axioms finiteAddRemainingValue_canonical_zeuge

omit [Kern] in
/-- Bounds transfer through the literal decoder arithmetic without word wrap. -/
theorem finiteAddRemainingValue_bounds (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax)
    (i : Nat) (hi : i < 4) :
    let w := finiteAddRemainingValue F
      (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) i
    if i < 2 then 1 ≤ w.toNat ∧ w.toNat < F.bexpMax
    else w.toNat < 2^56 := by
  have one (x : Gleitkomma.GBits F) (hx : Gleitkomma.wf F x)
      (fx : x.bexp ≠ F.bexpMax) :
      let w := BitVec.ofNat 64 (Gleitkomma.zuBits F x)
      let e := floatFieldWord w F.fracBits F.ebits
      let f := floatFieldWord w 0 F.fracBits
      (1 ≤ (e + Runner.IR.bool (e == 0)).toNat ∧
        (e + Runner.IR.bool (e == 0)).toNat < F.bexpMax) ∧
      ((f + (1 - Runner.IR.bool (e == 0)) *
        BitVec.ofNat 64 (2^F.fracBits)) * 8).toNat < 2^56 := by
    have bounds := floatFiniteAdd_input_bounds F dense width precision exponents x hx fx
    dsimp only at bounds ⊢
    let e := floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F x)) F.fracBits F.ebits
    let f := floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F x)) 0 F.fracBits
    change 1 ≤ max e.toNat 1 ∧ max e.toNat 1 < F.bexpMax ∧
      8*(f.toNat + if e.toNat = 0 then 0 else 2^F.fracBits) < 2^(F.fracBits+4) ∧
      8*(f.toNat + if e.toNat = 0 then 0 else 2^F.fracBits) < 2^56 at bounds
    have cap : (2 : Nat)^F.fracBits < 2^64 :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) precision) (by decide)
    change (1 ≤ (e + Runner.IR.bool (e == 0)).toNat ∧
      (e + Runner.IR.bool (e == 0)).toNat < F.bexpMax) ∧
      ((f + (1 - Runner.IR.bool (e == 0)) * BitVec.ofNat 64 (2^F.fracBits)) * 8).toNat < 2^56
    by_cases hz : e = 0
    · simp [hz, Runner.IR.bool, BitVec.toNat_mul] at bounds ⊢
      omega
    · have hn : e.toNat ≠ 0 := by
        intro h
        exact hz (BitVec.eq_of_toNat_eq h)
      have ep : 1 ≤ e.toNat := by omega
      have test : (e == 0#64) = false := by
        exact beq_eq_false_iff_ne.mpr hz
      simp only [Runner.IR.bool, BitVec.ofNat_eq_ofNat, test, Bool.false_eq_true, ↓reduceIte,
        BitVec.add_zero, BitVec.sub_zero, BitVec.one_mul]
      simp only [hn, ↓reduceIte, Nat.max_eq_left ep] at bounds
      constructor
      · exact ⟨ep,bounds.2.1⟩
      · simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
        norm_num only [BitVec.toNat_ofNat]
        rw [show 2^F.fracBits % 18446744073709551616 = 2^F.fracBits from Nat.mod_eq_of_lt cap, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega
  have aa := one a ha fa
  have bb := one b hb fb
  interval_cases i
  · simpa [finiteAddRemainingValue] using aa.1
  · simpa [finiteAddRemainingValue] using bb.1
  · simpa [finiteAddRemainingValue] using aa.2
  · simpa [finiteAddRemainingValue] using bb.2

omit [Kern] in
theorem finiteAddRemainingValue_bounds_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64], ∀ i < 4,
      let a : Gleitkomma.GBits F := ⟨true,0,1⟩
      let b : Gleitkomma.GBits F := ⟨false,F.bexpMax-1,2^F.fracBits-1⟩
      let w := finiteAddRemainingValue F
        (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
        (BitVec.ofNat 64 (Gleitkomma.zuBits F b)) i
      if i < 2 then 1 ≤ w.toNat ∧ w.toNat < F.bexpMax
      else w.toNat < 2^56 := by
  intro F member i hi
  apply finiteAddRemainingValue_bounds F
  all_goals try { simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                  rcases member with rfl | rfl
                  all_goals first | exact Gleitkomma.f32_dicht | exact Gleitkomma.f64_dicht | decide +kernel }
  exact hi

#print axioms finiteAddRemainingValue_bounds_zeuge

#print axioms finiteAddRemainingValue_bounds

omit [Kern] in
/-- A strictly larger decoded exponent supplies a normal significand. Even
    half of the smaller significand plus a sticky increment is strictly smaller.
    This is derived from encoded operands, including subnormal smaller inputs. -/
theorem finiteAddRemainingValue_unequal (F : Gleitkomma.Format)
    (dense : F.dicht) (width : F.ebits + F.fracBits + 1 ≤ 64)
    (precision : F.fracBits ≤ 52) (exponents : 1 < F.bexpMax)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    (hb : Gleitkomma.wf F b)
    (fa : a.bexp ≠ F.bexpMax) (fb : b.bexp ≠ F.bexpMax) :
    let v := finiteAddRemainingValue F
      (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F b))
    (v 1).toNat < (v 0).toNat → (v 3).toNat / 2 + 1 < (v 2).toNat := by
  dsimp only
  have eqs := finiteAddRemainingValue_canonical F dense width precision exponents
    a b ha hb fa fb
  have e0 := eqs 0 (by decide)
  have e1 := eqs 1 (by decide)
  have m0 := eqs 2 (by decide)
  have m1 := eqs 3 (by decide)
  norm_num only [Nat.reduceMod, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] at e0 e1 m0 m1
  rw [e0,e1,m0,m1]
  intro order
  have normal : a.bexp ≠ 0 := by omega
  have af := ha.2
  have bf := hb.2
  simp only [normal, ↓reduceIte]
  split <;> omega

#print axioms finiteAddRemainingValue_unequal

end Gabbro.Stage0.Senke
