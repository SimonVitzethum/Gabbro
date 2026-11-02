module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil5

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatFiniteAddL_read_fields_to_order {Γ : Ctx} {ρ : Env D Γ}
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
      ∃ orderingTail, tail =
        [ci 13 (dst+9) (dst+5) (dst+6),
         ci 14 (dst+10) (dst+5) (dst+6),
         ci 13 (dst+11) (dst+7) (dst+8),
         ci 5 (dst+10) (dst+10) (dst+11),
         ci 9 (dst+9) (dst+9) (dst+10)] ++ orderingTail := by
  obtain ⟨executed,tail,m',hc,run,agree,ra,rb,rsx,rsy,reads,rest,it,hi⟩ :=
    floatFiniteAddL_read_fields F dst a b wa wb compiled width lower frac mask
      fracMask hiddenBound room slots producerA producerB pre
  obtain ⟨inputs,inputTop,orderingTail,hinputs,hcode,_⟩ :=
    floatFiniteAddL_order_continuation F dst a b compiled
  have heq : inputs = executed := by
    rw [hi] at hinputs
    exact (Prod.mk.inj (Option.some.inj hinputs)).1.symm
  subst inputs
  have ht := List.append_cancel_left (hc.symm.trans hcode)
  exact ⟨executed,tail,m',hc,run,agree,ra,rb,rsx,rsy,reads,rest,orderingTail,ht⟩

#print axioms floatFiniteAddL_read_fields_to_order

theorem floatFiniteAddL_read_fields_to_order_zeuge {Γ : Ctx} {ρ : Env D Γ}
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
      ∃ orderingTail, tail =
        [ci 13 25 21 22, ci 14 26 21 22, ci 13 27 23 24,
         ci 5 26 26 27, ci 9 25 25 26] ++ orderingTail := by
  apply floatFiniteAddL_read_fields_to_order F 16
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


#print axioms floatFiniteAddL_read_fields_to_order_zeuge

/-- Exact read effect of a real frame write, including slots above the target. -/
theorem finiteAdd_write_reads {m : Runner.Mem} {fp : Runner.W} {K d : Nat}
    (frame : FrameOK m fp K) (hd : d < K) (v : Runner.W)
    (values : Nat → Runner.W)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i)) :
    ∀ i, i < K →
      (write m (slot fp (BitVec.ofNat 64 d)) 8 v.toNat).rd64
        (slot fp (BitVec.ofNat 64 i)) = some (Function.update values d v i) := by
  intro i hi
  by_cases eq : i = d
  · subst i
    simpa using (wr_slot frame hd v).2.1
  · rw [Function.update_of_ne eq]
    rw [rd64_write_far]
    · exact reads i hi
    · unfold Far
      rw [slot_toNat frame.room hd, slot_toNat frame.room hi]
      constructor
      · have := frame.lt; omega
      constructor
      · have := frame.lt; omega
      · omega

/-- Execute real copies while retaining a simultaneous account of every frame
    word. The fold records writes; it is not an alternative runner semantics. -/
theorem finiteAdd_moves {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K base reserved : Nat}
    (moves : List (Nat × Nat)) (values : Nat → Runner.W) (tail : List II)
    (bounds : ∀ p ∈ moves, base ≤ p.1 ∧ p.1 < K ∧ p.2 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (pre : Pre L m pc fp K base
      (moves.map (fun p => ci 2 p.1 p.2 0) ++ tail) ρ W reserved)
    (room : base ≤ K) :
    ∃ m', Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*moves.length),fp⟩ m' ∧
      Agree fp base K m m' ∧
      (∀ i, i < K → m'.rd64 (slot fp (BitVec.ofNat 64 i)) =
        some (moves.foldl (fun vs p => Function.update vs p.1 (vs p.2)) values i)) ∧
      Pre L m' (pc+BitVec.ofNat 64 (16*moves.length)) fp K base tail ρ W reserved := by
  induction moves generalizing m pc values with
  | nil => exact ⟨m, by simpa using (Star.refl ⟨pc,fp⟩ m), Agree.refl _ _ _ _, reads, by simpa using pre⟩
  | cons p ps ih =>
    obtain ⟨lower,hd,hs⟩ := bounds p (by simp)
    have hp : Pre L m pc fp K base
        ([ci 2 p.1 p.2 0] ++ (ps.map (fun p => ci 2 p.1 p.2 0) ++ tail)) ρ W reserved := by
      simpa using pre
    let next := write m (slot fp (BitVec.ofNat 64 p.1)) 8 (values p.2).toNat
    have wr := (wr_slot hp.frame hd (values p.2)).1
    have ag : Agree fp base K m next :=
      ((wr_slot hp.frame hd (values p.2)).2.2).mono lower
    have run : Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ next := by
      apply star_ins hp.left.code (by simp [ci])
      have ins := hp.left.code 0 (by simp)
      simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
      simp only [ci, op]
      apply f2_run (t := ⟨pc,fp⟩) ins
      rw [sx_nat (by have := hp.small; omega)]
      apply run_rd64 (reads p.2 hs)
      simp only [ret1]
      apply f1_run (t := ⟨pc,fp⟩) ins
      rw [sx_nat (by have := hp.small; omega)]
      exact run_wr64 wr
    have rest := hp.next ag (Nat.le_refl _) room
    obtain ⟨out,run2,ag2,reads2,rest2⟩ := ih
      (Function.update values p.1 (values p.2))
      (fun q hq => bounds q (by simp [hq]))
      (finiteAdd_write_reads hp.frame hd (values p.2) values reads)
      (by simpa using rest)
    have pcEq : pc+16+BitVec.ofNat 64 (16*ps.length) =
        pc+BitVec.ofNat 64 (16*(ps.length+1)) := by
      rw [BitVec.add_assoc, BitVec.add_comm (16 : Runner.W), ← BitVec.add_assoc]
      exact pc_add16 pc ps.length
    refine ⟨out, ?_, ag.trans ag2, reads2, ?_⟩
    · rw [List.length_cons, ← pcEq]
      exact run.trans run2
    · rw [List.length_cons, ← pcEq]
      exact rest2

#print axioms finiteAdd_moves

/-- The actual nine-copy SWAP path exchanges all three operand fields jointly.
    Every other frame slot is retained, except the actual scratch slot whose
    final value is the original left significand. -/
theorem finiteAdd_moves_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (values : Nat → Runner.W) (tail : List II)
    (room : dst+9 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (pre : Pre L m pc fp K (dst+3)
      ([ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
        ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
        ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0] ++ tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+144,fp⟩ m' ∧ Agree fp (dst+3) K m m' ∧
      (∀ i, i < K → m'.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if i = dst+3 then values (dst+4) else
         if i = dst+4 then values (dst+3) else
         if i = dst+5 then values (dst+6) else
         if i = dst+6 then values (dst+5) else
         if i = dst+7 then values (dst+8) else
         if i = dst+8 then values (dst+7) else
         if i = dst+9 then values (dst+7) else values i)) ∧
      Pre L m' (pc+144) fp K (dst+3) tail ρ W reserved := by
  have moves := finiteAdd_moves
    [(dst+9,dst+3),(dst+3,dst+4),(dst+4,dst+9),
     (dst+9,dst+5),(dst+5,dst+6),(dst+6,dst+9),
     (dst+9,dst+7),(dst+7,dst+8),(dst+8,dst+9)] values tail
    (L := L) (ρ := ρ) (W := W) (reserved := reserved)
    (m := m) (pc := pc) (fp := fp) (K := K) (base := dst+3)
  obtain ⟨out,run,ag,rd,rest⟩ := moves
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    reads (by simpa using pre) (by omega)
  refine ⟨out,by simpa using run,ag,?_,by simpa using rest⟩
  intro i hi
  have h := rd i hi
  simp [List.foldl, Function.update_apply] at h
  by_cases h3 : i = dst+3
  · subst i; simpa using h
  by_cases h4 : i = dst+4
  · subst i; simpa using h
  by_cases h5 : i = dst+5
  · subst i; simpa using h
  by_cases h6 : i = dst+6
  · subst i; simpa using h
  by_cases h7 : i = dst+7
  · subst i; simpa using h
  by_cases h8 : i = dst+8
  · subst i; simpa using h
  by_cases h9 : i = dst+9
  · subst i; simpa using h
  simpa [h3,h4,h5,h6,h7,h8,h9] using h

#print axioms finiteAdd_moves_zeuge

set_option maxHeartbeats 1200000 in
/-- Both emitted branch paths execute to their common continuation. The flag
    is read from real memory; the taken path executes all nine copies and the
    end jump, and the other path executes the conditional jump itself. -/
theorem floatFiniteAddL_swap_dispatch {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (values : Nat → Runner.W) (tail : List II) (swap : Bool)
    (room : dst+9 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (flag : values (dst+9) = Runner.IR.bool swap)
    (pre : Pre L m pc fp K (dst+3)
      ([ci 19 (dst+9) 176 0,
        ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
        ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
        ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0,
        ci 18 16 0 0] ++ tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+176,fp⟩ m' ∧ Agree fp (dst+3) K m m' ∧
      (∀ i, i < K → m'.rd64 (slot fp (BitVec.ofNat 64 i)) = some
        (if swap then
          if i = dst+3 then values (dst+4) else
          if i = dst+4 then values (dst+3) else
          if i = dst+5 then values (dst+6) else
          if i = dst+6 then values (dst+5) else
          if i = dst+7 then values (dst+8) else
          if i = dst+8 then values (dst+7) else
          if i = dst+9 then values (dst+7) else values i
         else values i)) ∧
      Pre L m' (pc+176) fp K (dst+3) tail ρ W reserved := by
  have ins : Runner.IR.InsAt m pc 19 (II.f ((dst+9 : Nat) : Int)) (II.f 176) (II.f 0) := by
    simpa [ci] using pre.code 0 (by simp)
  have test := reads (dst+9) room
  rw [flag] at test
  have sxslot : sx (II.f ((dst+9 : Nat) : Int)) = BitVec.ofNat 64 (dst+9) :=
    sx_nat (by have := pre.small; omega)
  cases swap with
  | false =>
    have readZero : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) = some (0 : Runner.W) := by
      rw [sxslot]
      exact test
    have run := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_zero (t := ⟨pc,fp⟩) ins readZero)
    have endPre := pre.next (Agree.refl fp (dst+3) K m) (Nat.le_refl _) (by omega)
    refine ⟨m,?_,Agree.refl _ _ _ _,?_,?_⟩
    · apply Star.one
      have off : sx (II.f 176) = (176 : Runner.W) := by
        rw [sx_lit (by decide : lit32 176 = true)]; rfl
      rw [off] at run
      exact run
    · simpa using reads
    · simpa using endPre
  | true =>
    have readOne : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) = some (1 : Runner.W) := by
      rw [sxslot]
      exact test
    have run := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_ne (t := ⟨pc,fp⟩) (v := 1) ins readOne (by decide))
    have hp : Pre L m (pc+16) fp K (dst+3)
        ([ci 2 (dst+9) (dst+3) 0, ci 2 (dst+3) (dst+4) 0, ci 2 (dst+4) (dst+9) 0,
          ci 2 (dst+9) (dst+5) 0, ci 2 (dst+5) (dst+6) 0, ci 2 (dst+6) (dst+9) 0,
          ci 2 (dst+9) (dst+7) 0, ci 2 (dst+7) (dst+8) 0, ci 2 (dst+8) (dst+9) 0] ++
          ([ci 18 16 0 0] ++ tail)) ρ W reserved := by
      have h : Pre L m pc fp K (dst+3)
        ([ci 19 (dst+9) 176 0] ++ _) ρ W reserved := pre
      simpa using h.next (Agree.refl fp (dst+3) K m) (Nat.le_refl _) (by omega)
    obtain ⟨out,copies,ag,rd,rest⟩ := finiteAdd_moves_zeuge values
      ([ci 18 16 0 0] ++ tail) room reads hp
    have jumpIns : Runner.IR.InsAt out (pc+16+144) 18 (II.f 16) (II.f 0) (II.f 0) := by
      simpa [ci] using rest.code 0 (by simp)
    have jump := run_step (t := ⟨pc+16+144,fp⟩) jumpIns (by decide) (run_jmp (t := ⟨pc+16+144,fp⟩) jumpIns)
    have done := rest.next (Agree.refl fp (dst+3) K out) (Nat.le_refl _) (by omega)
    refine ⟨out,?_,ag,by simpa using rd,?_⟩
    · have entry : Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ m := Star.one (by simpa only [nxt] using run)
      have finish : Star ⟨pc+16+144,fp⟩ out ⟨pc+176,fp⟩ out := Star.one (by
        have off : sx (II.f 16) = (16 : Runner.W) := by
          rw [sx_lit (by decide : lit32 16 = true)]; rfl
        rw [off] at jump
        simpa [BitVec.add_assoc] using jump)
      exact entry.trans (copies.trans finish)
    · simpa [BitVec.add_assoc] using done

#print axioms floatFiniteAddL_swap_dispatch

/-- Execute all five actual ordering instructions. The exponent comparison
    takes priority; the significand comparison breaks equal-exponent ties. -/
theorem floatFiniteAddL_order_compare {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {tail : List II} {ex ey q r : Runner.W}
    (room : dst+11 < K)
    (rx : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (ry : m.rd64 (slot fp (BitVec.ofNat 64 (dst+6))) = some ey)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r)
    (pre : Pre L m pc fp K (dst+9)
      ([ci 13 (dst+9) (dst+5) (dst+6), ci 14 (dst+10) (dst+5) (dst+6),
        ci 13 (dst+11) (dst+7) (dst+8), ci 5 (dst+10) (dst+10) (dst+11),
        ci 9 (dst+9) (dst+9) (dst+10)] ++ tail) ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc+80,fp⟩ m' ∧ Agree fp (dst+9) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (Runner.IR.bool (ex.slt ey || ((ex == ey) && q.slt r))) ∧
      Pre L m' (pc+80) fp K (dst+9) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+9)
    ([ci 13 (dst+9) (dst+5) (dst+6)] ++
     ([ci 14 (dst+10) (dst+5) (dst+6)] ++
      ([ci 13 (dst+11) (dst+7) (dst+8)] ++
       ([ci 5 (dst+10) (dst+10) (dst+11)] ++
        ([ci 9 (dst+9) (dst+9) (dst+10)] ++ tail))))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,w1,r1,e1⟩ := eng_bin_ok (a := dst+5) (b := dst+6) (d := dst+9) hp.left (by omega) (by omega) (by omega)
    rx ry (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  subst w1
  have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
  obtain ⟨m2,s2,a2,w2,r2,e2⟩ := eng_bin_ok (a := dst+5) (b := dst+6) (d := dst+10)
    {hp1.left with ctx := Nat.le_trans hp1.ctx (by omega : dst+9 ≤ dst+10)}
    (by omega) (by omega) (by omega)
    (slotRead_agree (input := dst+5) hp.frame a1 (by omega) (by omega) rx)
    (slotRead_agree (input := dst+6) hp.frame a1 (by omega) (by omega) ry)
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  subst w2
  have hp2 := hp1.next (a2.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have ag2 := a1.trans (a2.mono (by omega : dst+9 ≤ dst+10))
  obtain ⟨m3,s3,a3,w3,r3,e3⟩ := eng_bin_ok (a := dst+7) (b := dst+8) (d := dst+11)
    {hp2.left with ctx := Nat.le_trans hp2.ctx (by omega : dst+9 ≤ dst+11)}
    (by omega) (by omega) (by omega)
    (slotRead_agree (input := dst+7) hp.frame ag2 (by omega) (by omega) rq)
    (slotRead_agree (input := dst+8) hp.frame ag2 (by omega) (by omega) rr)
    (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  subst w3
  have hp3 := hp2.next (a3.mono (by omega : dst+9 ≤ dst+11)) (Nat.le_refl _) (by omega)
  obtain ⟨m4,s4,a4,w4,r4,e4⟩ := eng_bin_ok (a := dst+10) (b := dst+11) (d := dst+10)
    {hp3.left with ctx := Nat.le_trans hp3.ctx (by omega : dst+9 ≤ dst+10)}
    (by omega) (by omega) (by omega)
    (slotRead_agree (input := dst+10) hp2.frame a3 (by omega) (by omega) r2) r3
    (g := fun x y => some (x*y)) rfl (by decide) rfl
  subst w4
  have hp4 := hp3.next (a4.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have ag14 := (a2.trans (a3.mono (by omega : dst+10 ≤ dst+11))).trans a4
  obtain ⟨m5,s5,a5,w5,r5,e5⟩ := eng_bin_ok (a := dst+9) (b := dst+10) (d := dst+9) hp4.left (by omega) (by omega) (by omega)
    (slotRead_agree (input := dst+9) hp1.frame ag14 (by omega) (by omega) r1) r4
    (g := fun x y => some (x ||| y)) rfl (by decide) rfl
  subst w5
  have rest := hp4.next a5 (Nat.le_refl _) (by omega)
  refine ⟨m5,?_,(ag2.trans (a3.mono (by omega))).trans
    ((a4.mono (by omega)).trans a5),?_,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans (s3.trans (s4.trans s5)))
  · convert r5 using 2
    cases hx : ex.slt ey <;> cases he : ex == ey <;> cases hq : q.slt r <;>
      simp [Runner.IR.bool, hx, he, hq]
  · simpa [BitVec.add_assoc] using rest

#print axioms floatFiniteAddL_order_compare

end Gabbro.Stage0.Senke
