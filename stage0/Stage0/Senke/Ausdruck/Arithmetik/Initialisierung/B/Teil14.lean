module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.B.Teil14a

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.B.Teil13

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Execute all nine scalar instructions of the actual left test after its
    threshold constant. The retained significand and exponent share the run. -/
theorem floatFiniteAddL_left_condition_scalar {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q ex threshold : Runner.W} (tail : List II)
    (room : dst+11 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (rt : m.rd64 (slot fp (BitVec.ofNat 64 (dst+10))) = some threshold)
    (pre : Pre L m pc fp K (dst+9)
      ([ci 13 (dst+9) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0,
        ci 13 (dst+11) (dst+10) (dst+5),
        ci 5 (dst+9) (dst+9) (dst+11),
        ci 1 (dst+10) 0 0,
        ci 14 (dst+11) (dst+7) (dst+10),
        ci 1 (dst+10) 1 0,
        ci 4 (dst+11) (dst+10) (dst+11),
        ci 5 (dst+9) (dst+9) (dst+11)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+144,fp⟩ out ∧
      Agree fp (dst+9) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (Runner.IR.bool (q.slt threshold) * Runner.IR.bool ((1 : Runner.W).slt ex) *
          (1-Runner.IR.bool (q == 0))) ∧
      Pre L out (pc+144) fp K (dst+9) tail ρ W reserved := by
  have p0 : Pre L m pc fp K (dst+9) ([ci 13 (dst+9) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 13 (dst+11) (dst+10) (dst+5)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail))))))))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,w1,r1,rfl⟩ := eng_bin_ok (d := dst+9) (a := dst+7) (b := dst+10)
    {p0.left with ctx := by have := p0.ctx; omega} (by omega) (by omega) (by omega)
    rq rt (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have h1 := p0.next (a1.mono (by omega : dst+9 ≤ dst+9)) (Nat.le_refl _) (by omega)
  have rd1_7 := slotRead_agree p0.frame a1 (by omega) (by omega) rq
  have rd1_5 := slotRead_agree p0.frame a1 (by omega) (by omega) re
  have p1 : Pre L m1 (pc+16) fp K (dst+9) ([ci 1 (dst+10) 1 0] ++ ([ci 13 (dst+11) (dst+10) (dst+5)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)))))))) ρ W reserved := h1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (dst+10))) 8 (1 : Runner.W).toNat
  obtain ⟨wr2,r2,a2⟩ := wr_slot p1.frame (by omega : dst+10 < K) (1 : Runner.W)
  have s2 : Star ⟨pc+16,fp⟩ m1 ⟨pc+16+16,fp⟩ m2 := by
    apply star_ins p1.left.code (by simp [ci])
    have ins := p1.left.code 0 (by simp)
    simp only [ci,List.getElem_cons_zero,Nat.mul_zero,BitVec.add_zero] at ins
    simp only [ci,op]
    apply f2_run (t := ⟨pc+16,fp⟩) ins
    simp only [ret1]
    apply f1_run (t := ⟨pc+16,fp⟩) ins
    have sd : sx (II.f ((dst : Int)+10)) = BitVec.ofNat 64 (dst+10) := by
      exact_mod_cast (sx_nat (d := dst+10) (by have := p1.small; omega))
    rw [sd,sx_lit (by decide : lit32 1 = true)]
    exact run_wr64 wr2
  have h2 := p1.next (a2.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have rd2_7 := slotRead_agree p1.frame a2 (by omega) (by omega) rd1_7
  have rd2_5 := slotRead_agree p1.frame a2 (by omega) (by omega) rd1_5
  have rd2_9 := slotRead_agree p1.frame a2 (by omega) (by omega) r1
  have p2 : Pre L m2 (pc+16+16) fp K (dst+9) ([ci 13 (dst+11) (dst+10) (dst+5)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail))))))) ρ W reserved := h2
  obtain ⟨m3,s3,a3,w3,r3,rfl⟩ := eng_bin_ok (d := dst+11) (a := dst+10) (b := dst+5)
    {p2.left with ctx := by have := p2.ctx; omega} (by omega) (by omega) (by omega)
    r2 rd2_5 (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have h3 := p2.next (a3.mono (by omega : dst+9 ≤ dst+11)) (Nat.le_refl _) (by omega)
  have rd3_7 := slotRead_agree p2.frame a3 (by omega) (by omega) rd2_7
  have rd3_5 := slotRead_agree p2.frame a3 (by omega) (by omega) rd2_5
  have rd3_9 := slotRead_agree p2.frame a3 (by omega) (by omega) rd2_9
  have rd3_10 := slotRead_agree p2.frame a3 (by omega) (by omega) r2
  have p3 : Pre L m3 (pc+16+16+16) fp K (dst+9) ([ci 5 (dst+9) (dst+9) (dst+11)] ++ ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)))))) ρ W reserved := h3
  obtain ⟨m4,s4,a4,w4,r4,rfl⟩ := eng_bin_ok (d := dst+9) (a := dst+9) (b := dst+11)
    {p3.left with ctx := by have := p3.ctx; omega} (by omega) (by omega) (by omega)
    rd3_9 r3 (g := fun x y => some (x*y)) rfl (by decide) rfl
  have h4 := p3.next (a4.mono (by omega : dst+9 ≤ dst+9)) (Nat.le_refl _) (by omega)
  have rd4_7 := slotRead_agree p3.frame a4 (by omega) (by omega) rd3_7
  have rd4_5 := slotRead_agree p3.frame a4 (by omega) (by omega) rd3_5
  have p4 : Pre L m4 (pc+16+16+16+16) fp K (dst+9) ([ci 1 (dst+10) 0 0] ++ ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail))))) ρ W reserved := h4
  let m5 := write m4 (slot fp (BitVec.ofNat 64 (dst+10))) 8 (0 : Runner.W).toNat
  obtain ⟨wr5,r5,a5⟩ := wr_slot p4.frame (by omega : dst+10 < K) (0 : Runner.W)
  have s5 : Star ⟨pc+16+16+16+16,fp⟩ m4 ⟨pc+16+16+16+16+16,fp⟩ m5 := by
    apply star_ins p4.left.code (by simp [ci])
    have ins := p4.left.code 0 (by simp)
    simp only [ci,List.getElem_cons_zero,Nat.mul_zero,BitVec.add_zero] at ins
    simp only [ci,op]
    apply f2_run (t := ⟨pc+16+16+16+16,fp⟩) ins
    simp only [ret1]
    apply f1_run (t := ⟨pc+16+16+16+16,fp⟩) ins
    have sd : sx (II.f ((dst : Int)+10)) = BitVec.ofNat 64 (dst+10) := by
      exact_mod_cast (sx_nat (d := dst+10) (by have := p4.small; omega))
    rw [sd,sx_lit (by decide : lit32 0 = true)]
    exact run_wr64 wr5
  have h5 := p4.next (a5.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have rd5_7 := slotRead_agree p4.frame a5 (by omega) (by omega) rd4_7
  have rd5_5 := slotRead_agree p4.frame a5 (by omega) (by omega) rd4_5
  have rd5_9 := slotRead_agree p4.frame a5 (by omega) (by omega) r4
  have p5 : Pre L m5 (pc+16+16+16+16+16) fp K (dst+9) ([ci 14 (dst+11) (dst+7) (dst+10)] ++ ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)))) ρ W reserved := h5
  obtain ⟨m6,s6,a6,w6,r6,rfl⟩ := eng_bin_ok (d := dst+11) (a := dst+7) (b := dst+10)
    {p5.left with ctx := by have := p5.ctx; omega} (by omega) (by omega) (by omega)
    rd5_7 r5 (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  have h6 := p5.next (a6.mono (by omega : dst+9 ≤ dst+11)) (Nat.le_refl _) (by omega)
  have rd6_7 := slotRead_agree p5.frame a6 (by omega) (by omega) rd5_7
  have rd6_5 := slotRead_agree p5.frame a6 (by omega) (by omega) rd5_5
  have rd6_9 := slotRead_agree p5.frame a6 (by omega) (by omega) rd5_9
  have rd6_10 := slotRead_agree p5.frame a6 (by omega) (by omega) r5
  have p6 : Pre L m6 (pc+16+16+16+16+16+16) fp K (dst+9) ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail))) ρ W reserved := h6
  let m7 := write m6 (slot fp (BitVec.ofNat 64 (dst+10))) 8 (1 : Runner.W).toNat
  obtain ⟨wr7,r7,a7⟩ := wr_slot p6.frame (by omega : dst+10 < K) (1 : Runner.W)
  have s7 : Star ⟨pc+16+16+16+16+16+16,fp⟩ m6 ⟨pc+16+16+16+16+16+16+16,fp⟩ m7 := by
    apply star_ins p6.left.code (by simp [ci])
    have ins := p6.left.code 0 (by simp)
    simp only [ci,List.getElem_cons_zero,Nat.mul_zero,BitVec.add_zero] at ins
    simp only [ci,op]
    apply f2_run (t := ⟨pc+16+16+16+16+16+16,fp⟩) ins
    simp only [ret1]
    apply f1_run (t := ⟨pc+16+16+16+16+16+16,fp⟩) ins
    have sd : sx (II.f ((dst : Int)+10)) = BitVec.ofNat 64 (dst+10) := by
      exact_mod_cast (sx_nat (d := dst+10) (by have := p6.small; omega))
    rw [sd,sx_lit (by decide : lit32 1 = true)]
    exact run_wr64 wr7
  have h7 := p6.next (a7.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have rd7_7 := slotRead_agree p6.frame a7 (by omega) (by omega) rd6_7
  have rd7_5 := slotRead_agree p6.frame a7 (by omega) (by omega) rd6_5
  have rd7_9 := slotRead_agree p6.frame a7 (by omega) (by omega) rd6_9
  have rd7_11 : m7.rd64 (slot fp (BitVec.ofNat 64 (dst+11))) = some (Runner.IR.bool (q == 0)) := by
    change (write _ _ 8 _).rd64 _ = _
    rw [rd64_write_far]
    · exact r6
    · unfold Far
      rw [slot_toNat p6.frame.room (by omega : dst+10 < K),slot_toNat p6.frame.room (by omega : dst+11 < K)]
      have := p6.frame.lt
      omega
  have p7 : Pre L m7 (pc+16+16+16+16+16+16+16) fp K (dst+9) ([ci 4 (dst+11) (dst+10) (dst+11)] ++ ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)) ρ W reserved := h7
  obtain ⟨m8,s8,a8,w8,r8,rfl⟩ := eng_bin_ok (d := dst+11) (a := dst+10) (b := dst+11)
    {p7.left with ctx := by have := p7.ctx; omega} (by omega) (by omega) (by omega)
    r7 rd7_11 (g := fun x y => some (x-y)) rfl (by decide) rfl
  have h8 := p7.next (a8.mono (by omega : dst+9 ≤ dst+11)) (Nat.le_refl _) (by omega)
  have rd8_7 := slotRead_agree p7.frame a8 (by omega) (by omega) rd7_7
  have rd8_5 := slotRead_agree p7.frame a8 (by omega) (by omega) rd7_5
  have rd8_9 := slotRead_agree p7.frame a8 (by omega) (by omega) rd7_9
  have rd8_10 := slotRead_agree p7.frame a8 (by omega) (by omega) r7
  have p8 : Pre L m8 (pc+16+16+16+16+16+16+16+16) fp K (dst+9) ([ci 5 (dst+9) (dst+9) (dst+11)] ++ tail) ρ W reserved := h8
  obtain ⟨m9,s9,a9,w9,r9,rfl⟩ := eng_bin_ok (d := dst+9) (a := dst+9) (b := dst+11)
    {p8.left with ctx := by have := p8.ctx; omega} (by omega) (by omega) (by omega)
    rd8_9 r8 (g := fun x y => some (x*y)) rfl (by decide) rfl
  have h9 := p8.next (a9.mono (by omega : dst+9 ≤ dst+9)) (Nat.le_refl _) (by omega)
  have rd9_7 := slotRead_agree p8.frame a9 (by omega) (by omega) rd8_7
  have rd9_5 := slotRead_agree p8.frame a9 (by omega) (by omega) rd8_5
  refine ⟨m9,?_,?_,rd9_7,rd9_5,?_,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans (s9))))))))
  · exact (a1.mono (by omega)).trans ((a2.mono (by omega)).trans ((a3.mono (by omega)).trans ((a4.mono (by omega)).trans ((a5.mono (by omega)).trans ((a6.mono (by omega)).trans ((a7.mono (by omega)).trans ((a8.mono (by omega)).trans ((a9.mono (by omega))))))))))
  · simpa using r9
  · simpa [BitVec.add_assoc] using h9

#print axioms floatFiniteAddL_left_condition_scalar

/-- Run the actual threshold constant followed by the scalar left condition.
    The returned flag and retained words refer to the same final memory. -/
theorem floatFiniteAddL_left_condition {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q ex : Runner.W} (F : Gleitkomma.Format)
    (tail : List II) (thresholdRange : 2^(F.fracBits+3) < 65536^4)
    (room : dst+12 ≤ K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (pre : Pre L m pc fp K (dst+9)
      ((konstWL 4 (2^(F.fracBits+3)) (dst+10)).1 ++
        [ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
          ci 13 (dst+11) (dst+10) (dst+5), ci 5 (dst+9) (dst+9) (dst+11),
          ci 1 (dst+10) 0 0, ci 14 (dst+11) (dst+7) (dst+10),
          ci 1 (dst+10) 1 0, ci 4 (dst+11) (dst+10) (dst+11),
          ci 5 (dst+9) (dst+9) (dst+11)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+3)) (dst+10)).1.length)+144,fp⟩ out ∧
      Agree fp (dst+9) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (Runner.IR.bool (q.slt (BitVec.ofNat 64 (2^(F.fracBits+3)))) *
          Runner.IR.bool ((1 : Runner.W).slt ex) * (1-Runner.IR.bool (q == 0))) ∧
      Pre L out
        (pc+BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+3)) (dst+10)).1.length)+144)
        fp K (dst+9) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+9)
      ((konstWL 4 (2^(F.fracBits+3)) (dst+10)).1 ++
        ([ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
          ci 13 (dst+11) (dst+10) (dst+5), ci 5 (dst+9) (dst+9) (dst+11),
          ci 1 (dst+10) 0 0, ci 14 (dst+11) (dst+7) (dst+10),
          ci 1 (dst+10) 1 0, ci 4 (dst+11) (dst+10) (dst+11),
          ci 5 (dst+9) (dst+9) (dst+11)] ++ tail)) ρ W reserved := by
    simpa only [List.append_assoc] using pre
  obtain ⟨m1,run,agree,w,rd,rfl⟩ := konstWL_ok 4 (2^(F.fracBits+3)) thresholdRange
    (by omega) {hp.left with ctx := by have := hp.ctx; omega}
  have rest := hp.next (agree.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  obtain ⟨out,run2,agree2,rq2,re2,flag,done⟩ := floatFiniteAddL_left_condition_scalar tail
    (by omega) (slotRead_agree hp.frame agree (by omega) (by omega) rq)
    (slotRead_agree hp.frame agree (by omega) (by omega) re) rd rest
  exact ⟨out,run.trans run2,(agree.mono (by omega)).trans agree2,rq2,re2,flag,done⟩

#print axioms floatFiniteAddL_left_condition

end Gabbro.Stage0.Senke
