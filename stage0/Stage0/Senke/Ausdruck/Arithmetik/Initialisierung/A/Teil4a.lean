module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil3

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


end Gabbro.Stage0.Senke
