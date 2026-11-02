module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil3

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

#print axioms floatFiniteAddL_sign_fields_code

/-- Execute both sign decoders while retaining both operands and the first result. -/
theorem floatFiniteAddL_read_sign_fields {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (room : top ≤ K) (slots : dst+5 ≤ K)
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
      Pre L m' (pc+BitVec.ofNat 64 (16*executed.length)) fp K (dst+5) tail ρ W reserved := by
  obtain ⟨ca,ta,cb,tb,cf,tf,cg,tg,tail,ha,hb,hf,hg,hcode,hta,htb,htf,htg⟩ :=
    floatFiniteAddL_sign_fields_code F dst a b compiled
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
  refine ⟨((ca++cb)++cf)++cg,tail,m4,by simpa [List.append_assoc] using hcode,
    ?_,agreeAB.trans (agreeFG.mono (by omega)),
    slotRead_agree preF.frame agreeFG (by omega) (by omega) readA2,
    slotRead_agree preF.frame agreeFG (by omega) (by omega) readB,
    slotRead_agree preG.frame agreeG (by omega) (by omega) readF,readG,?_⟩
  · simpa only [List.length_append, pc_add] using
      ((runA.trans runB).trans (by simpa only [List.length_append, pc_add] using runF)).trans
        (by simpa only [List.length_append, pc_add] using runG)
  · simpa only [List.length_append, pc_add] using
      preG.next agreeG (show dst+4 ≤ dst+5 by omega) (by omega)

#print axioms floatFiniteAddL_read_sign_fields

/-- Joint f32/f64 execution witness with distinct operands and reserved prefix. -/
theorem floatFiniteAddL_read_sign_fields_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 21 ≤ K)
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
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 21 tail ρ W 13 := by
  apply floatFiniteAddL_read_sign_fields F 16
    (fun j => some ([ci 1 j 7 0],j+1))
    (fun j => some ([ci 1 j 11 0],j+1)) 7 11
    (top := ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> decide +kernel
  · decide +kernel
  · exact room
  · exact slots
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre


#print axioms floatFiniteAddL_read_sign_fields_zeuge

/-- Execute a whole batch from retained frame reads in one reconstructed context.
    Every producer uses the same concrete input frame; later temporary writes are
    handled by the existing sequential slot theorem. -/
theorem retainedWordCodes_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base top reserved : Nat}
    {code tail : List II}
    (ps : List (Nat → Option (List II × Nat))) (values : Nat → Runner.W)
    (sound : ∀ {Δ : Ctx} (η : Env D Δ),
      (∀ input w, FB ≤ input → input < base →
        m.rd64 (slot fp (BitVec.ofNat 64 input)) = some w →
        WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j input 0],j+1)) w) →
      ∀ i, (hi : i < ps.length) →
        WordCode (L := L) η (fun _ => True) ps[i] (values i))
    (compiled : floatStateSlotsL base ps = some (code,top))
    (room : top ≤ K) (lower : FB ≤ base) (slots : base+ps.length ≤ K)
    (pre : Pre L m pc fp K base (code++tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*code.length),fp⟩ m' ∧
      Agree fp base K m m' ∧
      (∀ i, i < ps.length →
        m'.rd64 (slot fp (BitVec.ofNat 64 (base+i))) = some (values i)) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*code.length)) fp K (base+ps.length) tail ρ W reserved := by
  obtain ⟨η, env⟩ := frameWordEnv (L := L) (n := base-FB) pre.frame (by omega)
  have loads : ∀ input w, FB ≤ input → input < base →
      m.rd64 (slot fp (BitVec.ofNat 64 input)) = some w →
      WordCode (L := L) η (fun _ => True)
        (fun j => some ([ci 2 j input 0],j+1)) w := by
    intro input w lo hi read
    let x := frameWordVar (base-FB) (input-FB) (by omega)
    have hx : vslot x = input := by
      dsimp only [x]
      rw [frameWordVar_slot]
      omega
    obtain ⟨v, rv, ev⟩ := ValueAt.word frameWordTy _ trivial (env _ x)
    rw [hx, read] at rv
    cases rv
    change w = BitVec.ofInt 64 (η.get x).n at ev
    intro fp' K' d c t hc ht mm pp hp
    have hc' : (fun (j : Nat) => some ([ci 2 j (FB+(input-FB)) 0],j+1)) d =
        some (c,t) := by
      have eq : (FB : Int) + ((input : Int) - FB) = input := by omega
      simpa only [eq] using hc
    have run := frameWordLoad (L := L) (base-FB) (input-FB) (by omega) η
      (by simpa only [Nat.cast_add, Nat.cast_sub lo] using hc') ht mm pp hp
    simpa only [x, ← ev] using run
  have hp : Pre L m pc fp K base code η (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx]; omega, pre.left.small, pre.frame,
      pre.left.code, pre.left.far, env, trivial, wstab_true _ _⟩
  obtain ⟨m',run,agree,reads⟩ := floatStateSlotsL_ok ps values compiled room slots
    (fun i hi c t hc ht mm pp hp => sound η loads i hi hc ht mm pp hp) m pc hp
  exact ⟨m',run,agree,reads,pre.next agree (by omega) (by omega)⟩

#print axioms retainedWordCodes_ok

/-- Four consecutive retained reads jointly witness the batch rule, with
    distinct operands, an arbitrary continuation and reserved prefix thirteen. -/
theorem retainedWordCodes_ok_zeuge {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K : Nat} {tail : List II}
    (room : 25 ≤ K)
    (readA : m.rd64 (slot fp 17) = some 7)
    (readB : m.rd64 (slot fp 18) = some 11)
    (pre : Pre L m pc fp K 21
      ([ci 2 21 17 0,ci 2 22 18 0,ci 2 23 17 0,ci 2 24 18 0]++tail) ρ W 13) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ m' ∧ Agree fp 21 K m m' ∧
      (∀ i, i < 4 → m'.rd64 (slot fp (BitVec.ofNat 64 (21+i))) =
        some (if i % 2 = 0 then 7 else 11)) ∧
      Pre L m' (pc+64) fp K 25 tail ρ W 13 := by
  let load := fun (input j : Nat) => some ([ci 2 j input 0],j+1)
  let ps := [load 17,load 18,load 17,load 18]
  let values := fun (i : Nat) => (if i % 2 = 0 then 7 else 11 : Runner.W)
  have compiled : floatStateSlotsL 21 ps =
      some ([ci 2 21 17 0,ci 2 22 18 0,ci 2 23 17 0,ci 2 24 18 0],25) := rfl
  have result := retainedWordCodes_ok (L := L) ps values (by
    intro Δ η loads i hi
    have bound : i < 4 := hi
    interval_cases i <;> norm_num [ps,values] <;>
      intro fp K d c top hc ht mm pp hp <;>
      first | exact loads 17 7 (by decide) (by decide) readA hc ht mm pp hp
            | exact loads 18 11 (by decide) (by decide) readB hc ht mm pp hp)
    compiled room (by decide) room pre
  simpa [ps,values] using result

#print axioms retainedWordCodes_ok_zeuge

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
