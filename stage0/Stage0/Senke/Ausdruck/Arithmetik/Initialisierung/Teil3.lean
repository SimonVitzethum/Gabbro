module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Shared finite add candidate. Operands are decoded at runtime; alignment
    retains guard/round/sticky bits before signed cancellation. No validator
    hook is enabled until the complete source-to-bytes theorem is available. -/
def floatFiniteAddL (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) := do
  let load := fun (s j : Nat) => some ([ci 2 j s 0], j+1)
  let branch := fun (c : Nat) (yes no : List II) =>
    [ci 19 c (16*(yes.length+2)) 0] ++ yes ++
      [ci 18 (16*(no.length+1)) 0 0] ++ no
  let x := dst+1; let y := dst+2
  let sx := dst+3; let sy := dst+4
  let ex := dst+5; let ey := dst+6
  let q := dst+7; let r := dst+8
  let t := dst+9; let u := dst+10; let v := dst+11
  let field := fun start width j p => floatFieldL start width j p
  let exponent := fun p j => wordL 3 j (field F.fracBits F.ebits j p)
    (wordK 14 (j+1) (field F.fracBits F.ebits (j+1) p) 0)
  let magnitude := fun p j => wordK 5 j
    (wordL 3 j (field 0 F.fracBits j p)
      (wordL 5 (j+1)
        (wordL 4 (j+1) (some ([ci 1 (j+1) 1 0],j+2))
          (wordK 14 (j+2) (field F.fracBits F.ebits (j+2) p) 0))
        (some (konstWL 4 (2^F.fracBits) (j+2))))) 8
  let inputs ← floatStateSlotsL x [a,b,
    fun j => field (F.fracBits+F.ebits) 1 j (load x),
    fun j => field (F.fracBits+F.ebits) 1 j (load y),
    exponent (load x), exponent (load y), magnitude (load x), magnitude (load y)]
  let swap := [ci 2 t sx 0, ci 2 sx sy 0, ci 2 sy t 0,
    ci 2 t ex 0, ci 2 ex ey 0, ci 2 ey t 0,
    ci 2 t q 0, ci 2 q r 0, ci 2 r t 0]
  let sort := [ci 13 t ex ey, ci 14 u ex ey, ci 13 v q r,
    ci 5 u u v, ci 9 t t u] ++ branch t swap []
  let aligned ← floatShiftJamL (dst+16) (load r)
    (fun j => wordL 4 j (load ex j) (load ey (j+1)))
  let signed := [ci 2 r (dst+16) 0, ci 14 t sx sy] ++
    branch t [ci 3 q q r] [ci 4 q q r]
  let shift ← floatShiftJamL (dst+16) (load q)
    (fun j => some ([ci 1 j 1 0],j+1))
  let right := (konstWL 4 (2^(F.fracBits+4)) u).1 ++
    [ci 13 t q u, ci 1 u 1 0, ci 4 t u t] ++
    branch t (shift.1 ++ [ci 2 q (dst+16) 0, ci 3 ex ex u]) []
  let condition := (konstWL 4 (2^(F.fracBits+3)) u).1 ++
    [ci 13 t q u, ci 1 u 1 0, ci 13 v u ex, ci 5 t t v,
     ci 1 u 0 0, ci 14 v q u, ci 1 u 1 0, ci 4 v u v, ci 5 t t v]
  let body := [ci 1 u 2 0, ci 5 q q u, ci 1 u 1 0, ci 4 ex ex u]
  let left := condition ++ [ci 19 t (16*(body.length+2)) 0] ++ body ++
    [ci 18 (-(16*(condition.length+body.length+1) : Int)) 0 0]
  let rounded ← floatGuardRoundL (dst+16)
    (fun j => wordK 6 j (load q j) 8)
    (fun j => wordK 8 j (load q j) 7)
    (fun j => some ([ci 1 j 0 0],j+1))
  let carry := (konstWL 4 (2^(F.fracBits+1)) u).1 ++ [ci 14 t q u] ++
    branch t [ci 1 u 1 0, ci 12 q q u, ci 3 ex ex u] []
  let pack := (konstWL 4 (2^F.fracBits) u).1 ++ [ci 13 t q u] ++
    branch t [ci 1 ex 0 0] [ci 4 q q u] ++
    (konstWL 4 F.bexpMax u).1 ++ [ci 13 t ex u] ++
    branch t [] [ci 2 ex u 0, ci 1 q 0 0] ++
    (konstWL 4 (2^F.fracBits) u).1 ++ [ci 5 ex ex u, ci 3 q q ex]
  let sign := (konstWL 4 (2^(F.fracBits+F.ebits)) u).1 ++
    [ci 5 sx sx u, ci 3 dst sx q]
  let zero := [ci 5 sx sx sy, ci 1 q 0 0]
  let finish := [ci 1 u 0 0, ci 14 t q u] ++ branch t zero
    (right ++ left ++ rounded.1 ++ [ci 2 q (dst+16) 0] ++ carry ++ pack)
  pure (inputs.1 ++ sort ++ aligned.1 ++ signed ++ finish ++ sign,
    max inputs.2 (max aligned.2 (max shift.2 rounded.2)))

/-- Recover the actual operand-code prefix from successful compilation of the
    complete candidate. No separately supplied instruction-list decomposition
    is trusted by the execution theorem. -/
theorem floatFiniteAddL_operand_code (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code, top)) :
    ∃ ca ta cb tb tail, a (dst+1) = some (ca,ta) ∧
      b (dst+2) = some (cb,tb) ∧ code = (ca ++ cb) ++ tail ∧
      ta ≤ top ∧ tb ≤ top := by
  simp only [floatFiniteAddL, bind, pure, Option.bind_eq_some_iff] at compiled
  obtain ⟨inputs, hi, aligned, ha, shift, hs, rounded, hr, result⟩ := compiled
  rw [floatStateSlotsL] at hi
  simp only [bind, pure, Option.bind_eq_some_iff] at hi
  obtain ⟨av, hav, afterA, hb, inputEq⟩ := hi
  rw [floatStateSlotsL] at hb
  simp only [bind, pure, Option.bind_eq_some_iff] at hb
  obtain ⟨bv, hbv, afterB, hc, afterEq⟩ := hb
  rcases inputs with ⟨inputCode,inputTop⟩
  rcases afterA with ⟨restCode,restTop⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at inputEq afterEq result
  refine ⟨av.1, av.2, bv.1, bv.2, code.drop (av.1.length + bv.1.length), hav, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hbv
  · rw [← result.1, ← inputEq.1, ← afterEq.1]
    simp [List.drop_append, List.append_assoc]
  · omega
  · omega

#print axioms floatFiniteAddL_operand_code

/-- Execute both operand producers inside the actual compiled finite candidate.
    The continuation is fetched from preserved code, with the environment,
    permissions and arbitrary reserved prefix carried through both writes.
    This stops before field decoding; it does not assert IEEE correctness of
    the subsequent sort, jam, normalization or packing instructions. -/
theorem floatFiniteAddL_read_operands {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (room : top ≤ K) (slots : dst+3 ≤ K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ operandCode tail m', code = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp (dst+1) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+1))) = some wa ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+2))) = some wb ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K (dst+3)
        tail ρ W reserved := by
  obtain ⟨ca,ta,cb,tb,tail,ha,hb,hcode,hta,htb⟩ :=
    floatFiniteAddL_operand_code F dst a b compiled
  rw [hcode] at pre
  obtain ⟨m1,runA,agreeA,w,readA,valueA⟩ :=
    producerA ca ta ha (by omega) m pc pre.left.left
  subst w
  have preB := pre.left.next agreeA (show dst+1 ≤ dst+2 by omega) (by omega)
  obtain ⟨m2,runB,agreeB,w,readB,valueB⟩ :=
    producerB cb tb hb (by omega) m1 _ preB
  subst w
  have agree := agreeA.trans (agreeB.mono (show dst+1 ≤ dst+2 by omega))
  refine ⟨ca ++ cb,tail,m2,hcode,?_,agree,?_,readB,?_⟩
  · simpa only [List.length_append, pc_add] using runA.trans runB
  · exact slotRead_agree preB.frame agreeB (by omega) (by omega) readA
  · exact pre.next agree (by omega) (by omega)

#print axioms floatFiniteAddL_read_operands

/-- Both IEEE formats compile and execute distinct operands jointly with a
    nonzero reserved environment prefix and an arbitrary enclosing frame. -/
theorem floatFiniteAddL_read_operands_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 19 ≤ K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ operandCode tail m',
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = operandCode ++ tail ∧
      Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 (16*operandCode.length),fp⟩ m' ∧
      Agree fp 17 K m m' ∧
      m'.rd64 (slot fp 17) = some 7 ∧ m'.rd64 (slot fp 18) = some 11 ∧
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 19 tail ρ W 13 := by
  apply floatFiniteAddL_read_operands F 16
    (fun j => some ([ci 1 j 7 0],j+1))
    (fun j => some ([ci 1 j 11 0],j+1)) 7 11
    (top := ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at format
    rcases format with rfl | rfl <;> rfl
  · exact room
  · exact slots
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre

#print axioms floatFiniteAddL_read_operands_zeuge

/-- Lift a composed word proof through an environment reconstructed from the
    actual retained read. The fixed-slot load is never assumed universally sound
    under the caller's environment. -/
theorem retainedWordCode_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K dst input top reserved : Nat}
    {code : List II} (w result : Runner.W)
    (body : (Nat → Option (List II × Nat)) → Nat → Option (List II × Nat))
    (sound : ∀ {Δ : Ctx} (η : Env D Δ),
      WordCode (L := L) η (fun _ => True)
        (fun j => some ([ci 2 j input 0],j+1)) w →
      WordCode (L := L) η (fun _ => True)
        (body (fun j => some ([ci 2 j input 0],j+1))) result)
    (compiled : body (fun j => some ([ci 2 j input 0],j+1)) dst = some (code,top))
    (room : top ≤ K) (dstRoom : dst ≤ K) (lower : FB ≤ input) (retained : input < dst)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some w)
    (pre : Pre L m pc fp K dst code ρ W reserved) :
    Ok m pc fp K dst code (· = result) := by
  obtain ⟨η, env⟩ := frameWordEnv (L := L) (n := dst-FB) pre.frame (by omega)
  let x := frameWordVar (dst-FB) (input-FB) (by omega)
  have hx : vslot x = input := by
    dsimp only [x]
    rw [frameWordVar_slot]
    omega
  obtain ⟨v, rv, ev⟩ := ValueAt.word frameWordTy _ trivial (env _ x)
  rw [hx, read] at rv
  cases rv
  change w = BitVec.ofInt 64 (η.get x).n at ev
  have load' : WordCode (L := L) η (fun _ => True)
      (fun j => some ([ci 2 j input 0],j+1)) w := by
    intro fp' K' d c t hc ht mm pp hp
    have hc' : (fun (j : Nat) => some ([ci 2 j (FB+(input-FB)) 0],j+1)) d =
        some (c,t) := by
      have eq : (FB : Int) + ((input : Int) - FB) = input := by omega
      simpa only [eq] using hc
    have run := frameWordLoad (L := L) (dst-FB) (input-FB) (by omega) η
      (by simpa only [Nat.cast_add, Nat.cast_sub lower] using hc') ht mm pp hp
    simpa only [x, ← ev] using run
  have hp : Pre L m pc fp K dst code η (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx]; omega, pre.small, pre.frame,
      pre.code, pre.far, env, trivial, wstab_true _ _⟩
  exact sound η load' compiled room m pc hp

#print axioms retainedWordCode_ok

/-- Execute the existing decoder on a retained word. The proof context is
    reconstructed from the actual frame; no decoded field or load contract is
    supplied. Arbitrary original reserved prefixes and outside-frame facts are
    recovered by the caller's continuation precondition. -/
theorem floatFieldL_retained {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K dst input top reserved : Nat}
    {code : List II} (offset width : Nat) (ho : offset < 64)
    (hm : 2^width - 1 < 2^64) (w : Runner.W)
    (compiled : floatFieldL offset width dst
      (fun j => some ([ci 2 j input 0],j+1)) = some (code,top))
    (room : top ≤ K) (lower : FB ≤ input) (retained : input < dst)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some w)
    (pre : Pre L m pc fp K dst code ρ W reserved) :
    Ok m pc fp K dst code (· = floatFieldWord w offset width) := by
  have dstRoom : dst ≤ K := by
    obtain ⟨output, shape, _⟩ := floatFieldL_shape offset width dst ho
      (fun j => some ([ci 2 j input 0],j+1)) _ _ rfl
    rw [compiled] at shape
    cases shape
    omega
  exact retainedWordCode_ok w (floatFieldWord w offset width)
    (fun load j => floatFieldL offset width j load)
    (fun η load => floatFieldL_ok offset width ho hm load)
    compiled room dstRoom lower retained read pre

#print axioms floatFieldL_retained

/-- Identify the first field decoder in the actual compiled continuation,
    including its ceiling. Neither the rest code nor a decoded field is assumed. -/
theorem floatFiniteAddL_first_field_code (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code,top)) :
    ∃ ca ta cb tb cf tf tail,
      a (dst+1) = some (ca,ta) ∧ b (dst+2) = some (cb,tb) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+3)
        (fun j => some ([ci 2 j (dst+1) 0],j+1)) = some (cf,tf) ∧
      code = (ca ++ cb) ++ (cf ++ tail) ∧ ta ≤ top ∧ tb ≤ top ∧ tf ≤ top := by
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
  rcases inputs with ⟨inputCode,inputTop⟩
  rcases afterA with ⟨aCode,aTop⟩
  rcases afterB with ⟨bCode,bTop⟩
  rcases afterF with ⟨fCode,fTop⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at inputEq afterEq fieldEq result
  refine ⟨av.1,av.2,bv.1,bv.2,fv.1,fv.2,
    fCode ++ code.drop inputCode.length,hav,?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using hbv
  · simpa [Nat.add_assoc] using hfv
  · calc
      code = inputCode ++ code.drop inputCode.length := by
        rw [← result.1]
        simp [List.drop_append, List.append_assoc]
      _ = _ := by
        rw [← inputEq.1, ← afterEq.1, ← fieldEq.1]
        simp only [List.append_assoc]
  all_goals omega

#print axioms floatFiniteAddL_first_field_code

/-- Extend the actual two-producer execution through its first field decoder.
    Both packed operands survive decoder temporaries; the remaining emitted code
    is fetchable under the original environment, world and reserved prefix. -/
theorem floatFiniteAddL_read_first_field {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (room : top ≤ K) (slots : dst+4 ≤ K)
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
      Pre L m' (pc+BitVec.ofNat 64 (16*executed.length)) fp K (dst+4) tail ρ W reserved := by
  obtain ⟨ca,ta,cb,tb,cf,tf,tail,ha,hb,hf,hcode,hta,htb,htf⟩ :=
    floatFiniteAddL_first_field_code F dst a b compiled
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
  refine ⟨(ca++cb)++cf,tail,m3,by simpa [List.append_assoc] using hcode,
    ?_,agreeAB.trans (agreeF.mono (by omega)),
    slotRead_agree preF.frame agreeF (by omega) (by omega) readA2,
    slotRead_agree preF.frame agreeF (by omega) (by omega) readB,readF,?_⟩
  · simpa only [List.length_append, pc_add] using (runA.trans runB).trans (by simpa only [List.length_append, pc_add] using runF)
  · simpa only [List.length_append, pc_add] using
      preF.next agreeF (show dst+3 ≤ dst+4 by omega) (by omega)

#print axioms floatFiniteAddL_read_first_field

/-- Joint format witness with distinct operands and reserved prefix thirteen. -/
theorem floatFiniteAddL_read_first_field_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (slots : 20 ≤ K)
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
      Pre L m' (pc + BitVec.ofNat 64 (16*operandCode.length)) fp K 20 tail ρ W 13 := by
  apply floatFiniteAddL_read_first_field F 16
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


#print axioms floatFiniteAddL_read_first_field_zeuge

/-- Recover both consecutive sign decoders from the actual emitted candidate. -/
theorem floatFiniteAddL_sign_fields_code (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) {code : List II} {top : Nat}
    (compiled : floatFiniteAddL F dst a b = some (code,top)) :
    ∃ ca ta cb tb cf tf cg tg tail,
      a (dst+1) = some (ca,ta) ∧ b (dst+2) = some (cb,tb) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+3)
        (fun j => some ([ci 2 j (dst+1) 0],j+1)) = some (cf,tf) ∧
      floatFieldL (F.fracBits+F.ebits) 1 (dst+4)
        (fun j => some ([ci 2 j (dst+2) 0],j+1)) = some (cg,tg) ∧
      code = (ca ++ cb) ++ (cf ++ (cg ++ tail)) ∧ ta ≤ top ∧ tb ≤ top ∧ tf ≤ top ∧ tg ≤ top := by
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
    gCode ++ code.drop inputCode.length,hav,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using hbv
  · simpa [Nat.add_assoc] using hfv
  · simpa [Nat.add_assoc] using hgv
  · calc
      code = inputCode ++ code.drop inputCode.length := by
        rw [← result.1]
        simp [List.drop_append, List.append_assoc]
      _ = _ := by
        rw [← inputEq.1, ← afterEq.1, ← fieldEq.1, ← signEq.1]
        simp only [List.append_assoc]
  all_goals omega

end Gabbro.Stage0.Senke
