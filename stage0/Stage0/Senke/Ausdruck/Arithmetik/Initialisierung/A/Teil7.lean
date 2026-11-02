module
public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil7a

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil6

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
theorem floatFiniteAddL_read_fields_sort {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : Nat)
    (a b : Nat → Option (List II × Nat)) (wa wb : Runner.W)
    {code : List II} {top K reserved : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (compiled : floatFiniteAddL F dst a b = some (code,top))
    (width : F.fracBits+F.ebits < 64) (lower : FB ≤ dst+1)
    (frac : F.fracBits < 64) (mask : 2^F.ebits-1 < 2^64)
    (fracMask : 2^F.fracBits-1 < 2^64) (hiddenBound : 2^F.fracBits < 2^64)
    (room : top ≤ K) (sortRoom : dst+11 < K)
    (producerA : ∀ c t, a (dst+1) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+1) c ρ W reserved →
      Ok m pc fp K (dst+1) c (· = wa))
    (producerB : ∀ c t, b (dst+2) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (dst+2) c ρ W reserved →
      Ok m pc fp K (dst+2) c (· = wb))
    (pre : Pre L m pc fp K (dst+1) code ρ W reserved) :
    ∃ executed tail, ∃ values : Nat → Runner.W, ∃ out,
      code = executed ++
        ([ci 13 (dst+9) (dst+5) (dst+6),
          ci 14 (dst+10) (dst+5) (dst+6),
          ci 13 (dst+11) (dst+7) (dst+8),
          ci 5 (dst+10) (dst+10) (dst+11),
          ci 9 (dst+9) (dst+9) (dst+10),
          ci 19 (dst+9) 176 0,
          ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
          ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
          ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0,
          ci 18 16 0 0] ++ tail) ∧
      Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*executed.length)+256,fp⟩ out ∧
      Agree fp (dst+1) K m out ∧
      (∀ i, i < 8 → values (dst+1+i) =
        match i with
        | 0 => wa
        | 1 => wb
        | 2 => floatFieldWord wa (F.fracBits+F.ebits) 1
        | 3 => floatFieldWord wb (F.fracBits+F.ebits) 1
        | _ => finiteAddRemainingValue F wa wb (i-4)) ∧
      (∀ i, i < dst+9 → out.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if (values (dst+5)).slt (values (dst+6)) ||
            ((values (dst+5) == values (dst+6)) && (values (dst+7)).slt (values (dst+8))) then
          if i = dst+3 then values (dst+4) else
          if i = dst+4 then values (dst+3) else
          if i = dst+5 then values (dst+6) else
          if i = dst+6 then values (dst+5) else
          if i = dst+7 then values (dst+8) else
          if i = dst+8 then values (dst+7) else values i
         else values i)) ∧
      (∃ ex ey q r : Runner.W,
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r ∧
        ey.toInt ≤ ex.toInt ∧ (ey = ex → r.toInt ≤ q.toInt)) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*executed.length)+256)
        fp K (dst+3) tail ρ W reserved := by
  obtain ⟨executed,fieldTail,before,hcode,run,ag,ra,rb,rsx,rsy,fields,rest,it,hi⟩ :=
    floatFiniteAddL_read_fields F dst a b wa wb compiled width lower frac mask
      fracMask hiddenBound room (by omega) producerA producerB pre
  obtain ⟨inputs,inputTop,tail,hinputs,hfull,_⟩ :=
    floatFiniteAddL_sort_continuation F dst a b compiled
  have heq : inputs = executed := by
    rw [hi] at hinputs
    exact (Prod.mk.inj (Option.some.inj hinputs)).1.symm
  subst inputs
  have ht := List.append_cancel_left (hcode.symm.trans hfull)
  rw [ht] at rest
  let values : Nat → Runner.W := fun i =>
    (before.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0
  have reads : ∀ i, i < K → before.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i) := by
    intro i hi
    have hr := rest.frame.rd i hi
    simp only [values, Runner.Mem.rd64, hr, ↓reduceIte, Option.getD_some]
  obtain ⟨out,sortRun,sortAgree,sorted,done⟩ := floatFiniteAddL_order_execute
    (dst := dst) values tail sortRoom reads
    {rest with ctx := Nat.le_trans pre.ctx (by omega : dst+1 ≤ dst+3)}
  refine ⟨executed,tail,values,out,hfull,run.trans sortRun,
    ag.trans (sortAgree.mono (by omega)),?_,sorted,finiteAdd_ordered_memory values sorted,done⟩
  have h0 : values (dst+1) = wa := by simp [values,ra]
  have h1 : values (dst+2) = wb := by simp [values,rb]
  have h2 : values (dst+3) = floatFieldWord wa (F.fracBits+F.ebits) 1 := by simp [values,rsx]
  have h3 : values (dst+4) = floatFieldWord wb (F.fracBits+F.ebits) 1 := by simp [values,rsy]
  have hf : ∀ i, i < 4 → values (dst+5+i) = finiteAddRemainingValue F wa wb i := by
    intro i hi
    simp [values,fields i hi]
  intro i hi
  interval_cases i
  · simpa using h0
  · simpa [Nat.add_assoc] using h1
  · simpa [Nat.add_assoc] using h2
  · simpa [Nat.add_assoc] using h3
  · simpa [Nat.add_assoc] using hf 0 (by omega)
  · simpa [Nat.add_assoc] using hf 1 (by omega)
  · simpa [Nat.add_assoc] using hf 2 (by omega)
  · simpa [Nat.add_assoc] using hf 3 (by omega)

#print axioms floatFiniteAddL_read_fields_sort

theorem floatFiniteAddL_read_fields_sort_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format)
    (format : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {K : Nat} {fp pc : Runner.W} {m : Runner.Mem}
    (room : ((floatFiniteAddL F 16
      (fun j => some ([ci 1 j 7 0],j+1))
      (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).2 ≤ K)
    (sortRoom : 27 < K)
    (pre : Pre L m pc fp K 17
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1))
        (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 ρ W 13) :
    ∃ executed tail, ∃ values : Nat → Runner.W, ∃ out,
      ((floatFiniteAddL F 16 (fun j => some ([ci 1 j 7 0],j+1)) (fun j => some ([ci 1 j 11 0],j+1))).getD ([],0)).1 = executed ++
        ([ci 13 (16+9) (16+5) (16+6),
          ci 14 (16+10) (16+5) (16+6),
          ci 13 (16+11) (16+7) (16+8),
          ci 5 (16+10) (16+10) (16+11),
          ci 9 (16+9) (16+9) (16+10),
          ci 19 (16+9) 176 0,
          ci 2 (16+9) (16+3) 0, ci 2 (16+3) (16+4) 0, ci 2 (16+4) (16+9) 0,
          ci 2 (16+9) (16+5) 0, ci 2 (16+5) (16+6) 0, ci 2 (16+6) (16+9) 0,
          ci 2 (16+9) (16+7) 0, ci 2 (16+7) (16+8) 0, ci 2 (16+8) (16+9) 0,
          ci 18 16 0 0] ++ tail) ∧
      Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*executed.length)+256,fp⟩ out ∧
      Agree fp (16+1) K m out ∧
      (∀ i, i < 8 → values (16+1+i) =
        match i with
        | 0 => 7
        | 1 => 11
        | 2 => floatFieldWord 7 (F.fracBits+F.ebits) 1
        | 3 => floatFieldWord 11 (F.fracBits+F.ebits) 1
        | _ => finiteAddRemainingValue F 7 11 (i-4)) ∧
      (∀ i, i < 16+9 → out.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if (values (16+5)).slt (values (16+6)) ||
            ((values (16+5) == values (16+6)) && (values (16+7)).slt (values (16+8))) then
          if i = 16+3 then values (16+4) else
          if i = 16+4 then values (16+3) else
          if i = 16+5 then values (16+6) else
          if i = 16+6 then values (16+5) else
          if i = 16+7 then values (16+8) else
          if i = 16+8 then values (16+7) else values i
         else values i)) ∧
      (∃ ex ey q r : Runner.W,
        out.rd64 (slot fp (BitVec.ofNat 64 (16+5))) = some ex ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+6))) = some ey ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+7))) = some q ∧
        out.rd64 (slot fp (BitVec.ofNat 64 (16+8))) = some r ∧
        ey.toInt ≤ ex.toInt ∧ (ey = ex → r.toInt ≤ q.toInt)) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*executed.length)+256)
        fp K (16+3) tail ρ W 13 := by
  apply floatFiniteAddL_read_fields_sort F 16
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
  · exact sortRoom
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · intro c t hc ht m pc hp
    cases hc
    exact const_ok hp (by decide) (by omega)
  · exact pre



#print axioms floatFiniteAddL_read_fields_sort_zeuge

/-- Execute the actual alignment producer from retained ordered-state reads.
    Reification ties repeated loads to memory while scratch writes remain above
    every operand. The returned continuation keeps the original environment and
    arbitrary reserved prefix; no fixed-read WordCode is assumed. -/
theorem floatFiniteAddL_align_execute {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst top reserved : Nat} {code tail : List II} {ex ey r : Runner.W}
    (lower : FB ≤ dst+5) (room : top ≤ K) (slots : dst+17 ≤ K)
    (rx : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (ry : m.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r)
    (compiled : floatShiftJamL (dst+16)
      (fun j => some ([ci 2 j (dst+8) 0],j+1))
      (fun j => wordL 4 j (some ([ci 2 j (dst+5) 0],j+1))
        (some ([ci 2 (j+1) (dst+6) 0],j+2))) = some (code,top))
    (pre : Pre L m pc fp K (dst+16) (code++tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*code.length),fp⟩ out ∧
      Agree fp (dst+16) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+16))) =
        some (floatShiftJamWord r (ex-ey)) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*code.length)) fp K (dst+17) tail ρ W reserved := by
  let producer := fun j => floatShiftJamL j
    (fun j => some ([ci 2 j (dst+8) 0],j+1))
    (fun j => wordL 4 j (some ([ci 2 j (dst+5) 0],j+1))
      (some ([ci 2 (j+1) (dst+6) 0],j+2)))
  have batch : floatStateSlotsL (dst+16) [producer] = some (code,max top (dst+17)) := by
    simp [floatStateSlotsL, producer, compiled, Nat.add_assoc]
  obtain ⟨out,run,agree,reads,rest⟩ := retainedWordCodes_ok (L := L)
    [producer] (fun _ => floatShiftJamWord r (ex-ey)) (by
      intro Δ η loads i hi
      have iz : i = 0 := by have : i < 1 := hi; omega
      subst i
      change WordCode (L := L) η (fun _ => True) producer (floatShiftJamWord r (ex-ey))
      have a : WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j (dst+8) 0],j+1)) r := loads (dst+8) r (by omega) (by omega) rr
      have x : WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j (dst+5) 0],j+1)) ex := loads (dst+5) ex lower (by omega) rx
      have y : WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j (dst+6) 0],j+1)) ey := loads (dst+6) ey (by omega) (by omega) ry
      have diff : WordCode (L := L) η (fun _ => True)
          (fun j => wordL 4 j (some ([ci 2 j (dst+5) 0],j+1))
            (some ([ci 2 (j+1) (dst+6) 0],j+2))) (ex-ey) :=
        WordCode.bin x y (g := fun x y => some (x-y)) rfl rfl (by decide : 4 < 256)
      intro fp K d c top hc ht mm pp hp
      exact floatShiftJamL_ok a diff hc ht mm pp hp)
    batch (by omega) (by omega) (by simpa using slots) pre
  exact ⟨out,run,agree,by simpa using reads 0 (by simp),rest⟩

#print axioms floatFiniteAddL_align_execute

theorem floatFiniteAddL_align_execute_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K top : Nat} {code tail : List II}
    (room : top ≤ K) (slots : 16+17 ≤ K)
    (rx : m.rd64 (slot fp (BitVec.ofNat 64 (16+5))) = some 5)
    (ry : m.rd64 (slot fp (BitVec.ofNat 64 (16+6))) = some 2)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (16+8))) = some 97)
    (compiled : floatShiftJamL (16+16)
      (fun j => some ([ci 2 j (16+8) 0],j+1))
      (fun j => wordL 4 j (some ([ci 2 j (16+5) 0],j+1))
        (some ([ci 2 (j+1) (16+6) 0],j+2))) = some (code,top))
    (pre : Pre L m pc fp K (16+16) (code++tail) ρ W 13) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*code.length),fp⟩ out ∧
      Agree fp (16+16) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (16+16))) =
        some (13) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*code.length)) fp K (16+17) tail ρ W 13 := by
  have run := floatFiniteAddL_align_execute (L := L) (dst := 16)
    (ex := 5) (ey := 2) (r := 97) (by decide) room slots rx ry rr compiled pre
  simpa only [show floatShiftJamWord 97 (5-2) = 13 from by decide +kernel] using run

#print axioms floatFiniteAddL_align_execute_zeuge

end Gabbro.Stage0.Senke
