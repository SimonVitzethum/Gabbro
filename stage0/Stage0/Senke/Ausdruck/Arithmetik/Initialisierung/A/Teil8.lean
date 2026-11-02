module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil7

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Execute the emitted signed arithmetic branch, including its conditional
    and unconditional jumps. The result is read from the same reached frame. -/
theorem floatFiniteAddL_signed_dispatch {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q r : Runner.W} (same : Bool) (tail : List II)
    (room : dst+9 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (rr : m.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some r)
    (flag : m.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) = some (Runner.IR.bool same))
    (pre : Pre L m pc fp K (dst+7)
      ([ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
        ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+64,fp⟩ out ∧
      Agree fp (dst+7) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some (if same then q+r else q-r) ∧
      Pre L out (pc+64) fp K (dst+7) tail ρ W reserved := by
  have ins : Runner.IR.InsAt m pc 19 (II.f ((dst+9 : Nat) : Int)) (II.f 48) (II.f 0) := by
    simpa [ci] using pre.code 0 (by simp)
  have test : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) =
      some (Runner.IR.bool same) := by
    rw [sx_nat (by have := pre.small; omega)]
    exact flag
  cases same with
  | false =>
    have jump := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_zero (t := ⟨pc,fp⟩) ins test)
    have off : sx (II.f 48) = (48 : Runner.W) := by
      rw [sx_lit (by decide : lit32 48 = true)]; rfl
    rw [off] at jump
    have hp : Pre L m (pc+48) fp K (dst+7)
        ([ci 4 (dst+7) (dst+7) (dst+8)] ++ tail) ρ W reserved := by
      have h : Pre L m pc fp K (dst+7)
          ([ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8), ci 18 32 0 0] ++
            ([ci 4 (dst+7) (dst+7) (dst+8)] ++ tail)) ρ W reserved := pre
      exact h.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    obtain ⟨out,run,ag,w,rd,eq⟩ := eng_bin_ok (a := dst+7) (b := dst+8) (d := dst+7) hp.left (by omega) (by omega) (by omega)
      rq rr (g := fun x y => some (x-y)) rfl (by decide) rfl
    subst w
    have rest := hp.next ag (Nat.le_refl _) (by omega)
    refine ⟨out,?_,ag,rd,?_⟩
    · simpa [BitVec.add_assoc] using (Star.one jump).trans run
    · simpa [BitVec.add_assoc] using rest
  | true =>
    have step := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_ne (t := ⟨pc,fp⟩) (v := 1) ins test (by decide))
    have hp : Pre L m (pc+16) fp K (dst+7)
        ([ci 3 (dst+7) (dst+7) (dst+8)] ++
          ([ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail)) ρ W reserved := by
      have h : Pre L m pc fp K (dst+7) ([ci 19 (dst+9) 48 0] ++ _) ρ W reserved := pre
      exact h.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    obtain ⟨out,run,ag,w,rd,eq⟩ := eng_bin_ok (a := dst+7) (b := dst+8) (d := dst+7) hp.left (by omega) (by omega) (by omega)
      rq rr (g := fun x y => some (x+y)) rfl (by decide) rfl
    subst w
    have rest := hp.next ag (Nat.le_refl _) (by omega)
    have ji : Runner.IR.InsAt out (pc+16+16) 18 (II.f 32) (II.f 0) (II.f 0) := by
      simpa [ci] using rest.code 0 (by simp)
    have jump := run_step (t := ⟨pc+16+16,fp⟩) ji (by decide)
      (run_jmp (t := ⟨pc+16+16,fp⟩) ji)
    have off : sx (II.f 32) = (32 : Runner.W) := by
      rw [sx_lit (by decide : lit32 32 = true)]; rfl
    rw [off] at jump
    have done : Pre L out (pc+16+16+32) fp K (dst+7) tail ρ W reserved :=
      rest.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    refine ⟨out,?_,ag,rd,?_⟩
    · have first : Star ⟨pc,fp⟩ m ⟨pc+16,fp⟩ m := Star.one (by simpa [nxt] using step)
      simpa [BitVec.add_assoc] using first.trans (run.trans (Star.one jump))
    · simpa [BitVec.add_assoc] using done

#print axioms floatFiniteAddL_signed_dispatch

/-- Copy the actual jam result, compare the retained signs, and execute
    ADD/SUB in one Runner execution. No intermediate frame is supplied. -/
theorem floatFiniteAddL_signed_execute {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (values : Nat → Runner.W) (tail : List II)
    (room : dst+16 < K)
    (reads : ∀ i, i < K → m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i))
    (pre : Pre L m pc fp K (dst+7)
      ([ci 2 (dst+8) (dst+16) 0, ci 14 (dst+9) (dst+3) (dst+4),
        ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
        ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+96,fp⟩ out ∧
      Agree fp (dst+7) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) =
        some (if values (dst+3) == values (dst+4) then
          values (dst+7)+values (dst+16) else values (dst+7)-values (dst+16)) ∧
      Pre L out (pc+96) fp K (dst+7) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+7)
      ([ci 2 (dst+8) (dst+16) 0] ++
        ([ci 14 (dst+9) (dst+3) (dst+4)] ++
          ([ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
            ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,rd1,hp1⟩ := finiteAdd_moves (base := dst+7) [(dst+8,dst+16)] values _
    (by simp; omega) reads (by simpa using hp) (by omega)
  have hp1 : Pre L m1 (pc+16) fp K (dst+7)
      ([ci 14 (dst+9) (dst+3) (dst+4)] ++
        ([ci 19 (dst+9) 48 0, ci 3 (dst+7) (dst+7) (dst+8),
          ci 18 32 0 0, ci 4 (dst+7) (dst+7) (dst+8)] ++ tail)) ρ W reserved := by
    simpa using hp1
  have r1 (i : Nat) (hi : i < dst+8) :
      m1.rd64 (slot fp (BitVec.ofNat 64 i)) = some (values i) := by
    simpa [Function.update_of_ne (show i ≠ dst+8 by omega)] using rd1 i (by omega)
  obtain ⟨m2,s2,a2,w,rd2,eq⟩ := eng_bin_ok (a := dst+3) (b := dst+4) (d := dst+9) (o := 14)
    {hp1.left with ctx := Nat.le_trans hp1.ctx (by omega : dst+7 ≤ dst+9)}
    (by omega) (by omega) (by omega) (r1 (dst+3) (by omega)) (r1 (dst+4) (by omega))
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  subst w
  have hp2 := hp1.next (a2.mono (by omega : dst+7 ≤ dst+9)) (Nat.le_refl _) (by omega)
  have rq := slotRead_agree (input := dst+7) hp1.frame a2 (by omega) (by omega)
    (r1 (dst+7) (by omega))
  have rr : m2.rd64 (slot fp (BitVec.ofNat 64 (dst+8))) = some (values (dst+16)) := by
    apply slotRead_agree hp1.frame a2 (by omega) (by omega)
    simpa using rd1 (dst+8) (by omega)
  obtain ⟨out,s3,a3,rd3,hp3⟩ := floatFiniteAddL_signed_dispatch
    (values (dst+3) == values (dst+4)) tail (by omega) rq rr rd2 hp2
  refine ⟨out,?_,a1.trans ((a2.mono (by omega)).trans a3),rd3,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans s3)
  · simpa [BitVec.add_assoc] using hp3

#print axioms floatFiniteAddL_signed_execute

/-- The literal RIGHT comparison keeps the positive result and exponent in the
    same memory as its branch flag. No adaptive-loop code is substituted. -/
theorem floatFiniteAddL_right_condition_scalar {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q ex threshold : Runner.W} (tail : List II)
    (room : dst+10 < K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (rt : m.rd64 (slot fp (BitVec.ofNat 64 (dst+10))) = some threshold)
    (pre : Pre L m pc fp K (dst+9)
      ([ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
        ci 4 (dst+9) (dst+10) (dst+9)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+48,fp⟩ out ∧
      Agree fp (dst+9) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (1-Runner.IR.bool (q.slt threshold)) ∧
      Pre L out (pc+48) fp K (dst+9) tail ρ W reserved := by
  have p0 : Pre L m pc fp K (dst+9)
      ([ci 13 (dst+9) (dst+7) (dst+10)] ++
        ([ci 1 (dst+10) 1 0] ++ ([ci 4 (dst+9) (dst+10) (dst+9)] ++ tail))) ρ W reserved := pre
  obtain ⟨m1,s1,a1,w1,r1,rfl⟩ := eng_bin_ok (d := dst+9) (a := dst+7) (b := dst+10)
    {p0.left with ctx := by have := p0.ctx; omega} (by omega) (by omega) (by omega)
    rq rt (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have p1 := p0.next a1 (Nat.le_refl _) (by omega)
  obtain ⟨m2,s2,a2,w2,r2,rfl⟩ := const_ok (d := dst+10)
    {p1.left with ctx := by have := p1.ctx; omega} (by decide) (by omega)
  have p2 := p1.next (a2.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  have r12 := slotRead_agree p1.frame a2 (by omega) (by omega) r1
  obtain ⟨m3,s3,a3,w3,r3,rfl⟩ := eng_bin_ok (d := dst+9) (a := dst+10) (b := dst+9)
    {p2.left with ctx := by have := p2.ctx; omega} (by omega) (by omega) (by omega)
    r2 r12 (g := fun x y => some (x-y)) rfl (by decide) rfl
  have agree := a1.trans ((a2.mono (by omega : dst+9 ≤ dst+10)).trans a3)
  refine ⟨m3,?_,agree,slotRead_agree p0.frame agree (by omega) (by omega) rq,
    slotRead_agree p0.frame agree (by omega) (by omega) re,?_,?_⟩
  · simpa [BitVec.add_assoc] using s1.trans (s2.trans s3)
  · simpa using r3
  · simpa [BitVec.add_assoc] using p2.next a3 (Nat.le_refl _) (by omega)

/-- Execute the actual RIGHT threshold materialization and comparison. -/
theorem floatFiniteAddL_right_condition {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} {q ex : Runner.W} (F : Gleitkomma.Format)
    (tail : List II) (thresholdRange : 2^(F.fracBits+4) < 65536^4)
    (room : dst+12 ≤ K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (re : m.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex)
    (pre : Pre L m pc fp K (dst+9)
      ((konstWL 4 (2^(F.fracBits+4)) (dst+10)).1 ++
        [ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
          ci 4 (dst+9) (dst+10) (dst+9)] ++ tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m
        ⟨pc+BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48,fp⟩ out ∧
      Agree fp (dst+9) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+5))) = some ex ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
        some (1-Runner.IR.bool (q.slt (BitVec.ofNat 64 (2^(F.fracBits+4))))) ∧
      Pre L out
        (pc+BitVec.ofNat 64 (16*(konstWL 4 (2^(F.fracBits+4)) (dst+10)).1.length)+48)
        fp K (dst+9) tail ρ W reserved := by
  have hp : Pre L m pc fp K (dst+9)
      ((konstWL 4 (2^(F.fracBits+4)) (dst+10)).1 ++
        ([ci 13 (dst+9) (dst+7) (dst+10), ci 1 (dst+10) 1 0,
          ci 4 (dst+9) (dst+10) (dst+9)] ++ tail)) ρ W reserved := by
    simpa only [List.append_assoc] using pre
  obtain ⟨m1,run,agree,w,rd,rfl⟩ := konstWL_ok 4 (2^(F.fracBits+4)) thresholdRange
    (by omega) {hp.left with ctx := by have := hp.ctx; omega}
  have rest := hp.next (agree.mono (by omega : dst+9 ≤ dst+10)) (Nat.le_refl _) (by omega)
  obtain ⟨out,run2,agree2,rq2,re2,flag,done⟩ := floatFiniteAddL_right_condition_scalar tail
    (by omega) (slotRead_agree hp.frame agree (by omega) (by omega) rq)
    (slotRead_agree hp.frame agree (by omega) (by omega) re) rd rest
  exact ⟨out,run.trans run2,(agree.mono (by omega)).trans agree2,rq2,re2,flag,done⟩

#print axioms floatFiniteAddL_right_condition


/-- Execute the SHIFTJAM call emitted in the taken RIGHT arm, using its literal
    constant distance producer rather than the old magnitude pipeline. -/
theorem floatFiniteAddL_right_shift {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst top reserved : Nat} {code tail : List II} {q : Runner.W}
    (lower : FB ≤ dst+7) (room : top ≤ K) (slots : dst+17 ≤ K)
    (rq : m.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q)
    (compiled : floatShiftJamL (dst+16)
      (fun j => some ([ci 2 j (dst+7) 0],j+1))
      (fun j => some ([ci 1 j 1 0],j+1)) = some (code,top))
    (pre : Pre L m pc fp K (dst+16) (code++tail) ρ W reserved) :
    ∃ out, Star ⟨pc,fp⟩ m ⟨pc+BitVec.ofNat 64 (16*code.length),fp⟩ out ∧
      Agree fp (dst+16) K m out ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+7))) = some q ∧
      out.rd64 (slot fp (BitVec.ofNat 64 (dst+16))) =
        some (floatShiftJamWord q 1) ∧
      Pre L out (pc+BitVec.ofNat 64 (16*code.length)) fp K (dst+17) tail ρ W reserved := by
  let producer := fun j => floatShiftJamL j
    (fun j => some ([ci 2 j (dst+7) 0],j+1))
    (fun j => some ([ci 1 j 1 0],j+1))
  have batch : floatStateSlotsL (dst+16) [producer] = some (code,max top (dst+17)) := by
    simp [floatStateSlotsL, producer, compiled, Nat.add_assoc]
  obtain ⟨out,run,agree,reads,rest⟩ := retainedWordCodes_ok (L := L)
    [producer] (fun _ => floatShiftJamWord q 1) (by
      intro Δ η loads i hi
      have iz : i = 0 := by have : i < 1 := hi; omega
      subst i
      change WordCode (L := L) η (fun _ => True) producer (floatShiftJamWord q 1)
      have source : WordCode (L := L) η (fun _ => True)
          (fun j => some ([ci 2 j (dst+7) 0],j+1)) q :=
        loads (dst+7) q lower (by omega) rq
      intro fp K d c top hc ht mm pp hp
      exact floatShiftJamL_ok source (WordCode.const 1 (by decide)) hc ht mm pp hp)
    batch (by omega) (by omega) (by simpa using slots) pre
  exact ⟨out,run,agree,slotRead_agree pre.frame agree (by omega) (by omega) rq,
    by simpa using reads 0 (by simp),rest⟩

#print axioms floatFiniteAddL_right_shift


/-- Execute the actual RIGHT BRZ without changing the compared memory. -/
theorem floatFiniteAddL_right_branch {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {K dst reserved : Nat} (yes tail : List II) (test : Bool)
    (room : dst+9 < K) (range : 16*(yes.length+2) < 2^31)
    (flag : m.rd64 (slot fp (BitVec.ofNat 64 (dst+9))) =
      some (1-Runner.IR.bool test))
    (pre : Pre L m pc fp K (dst+9)
      ([ci 19 (dst+9) (16*(yes.length+2)) 0] ++ yes ++ [ci 18 16 0 0] ++ tail)
      ρ W reserved) :
    Star ⟨pc,fp⟩ m
      ⟨pc+BitVec.ofNat 64 (if test then 16*(yes.length+2) else 16),fp⟩ m ∧
    Pre L m (pc+BitVec.ofNat 64 (if test then 16*(yes.length+2) else 16))
      fp K (dst+9) (if test then tail else yes ++ [ci 18 16 0 0] ++ tail) ρ W reserved := by
  have ins : Runner.IR.InsAt m pc 19 (II.f ((dst+9 : Nat) : Int))
      (II.f ((16*(yes.length+2) : Nat) : Int)) (II.f 0) := by
    simpa [ci] using pre.code 0 (by simp)
  have rd : m.rd64 (slot fp (sx (II.f ((dst+9 : Nat) : Int)))) =
      some (1-Runner.IR.bool test) := by
    rw [sx_nat (by have := pre.small; omega)]
    exact flag
  cases test with
  | false =>
    have step := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_ne (t := ⟨pc,fp⟩) (v := 1) ins (by simpa [Runner.IR.bool] using rd) (by decide))
    have short : Pre L m pc fp K (dst+9)
        ([ci 19 (dst+9) (16*(yes.length+2)) 0] ++
          (yes ++ [ci 18 16 0 0] ++ tail)) ρ W reserved := by
      simpa only [List.append_assoc] using pre
    exact ⟨by simpa [nxt] using Star.one step,
      by simpa using short.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)⟩
  | true =>
    have step := run_step (t := ⟨pc,fp⟩) ins (by decide)
      (run_brz_zero (t := ⟨pc,fp⟩) ins (by simpa [Runner.IR.bool] using rd))
    rw [sx_nat range] at step
    have long : Pre L m pc fp K (dst+9)
        (([ci 19 (dst+9) (16*(yes.length+2)) 0] ++ yes ++ [ci 18 16 0 0]) ++ tail)
        ρ W reserved := by simpa only [List.append_assoc] using pre
    exact ⟨by simpa using Star.one step,
      by simpa [List.length_append, Nat.add_assoc] using
        long.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)⟩

set_option maxHeartbeats 6000000 in
theorem floatFiniteAddL_read_fields_align_fields  :
    ∀ (F : Gleitkomma.Format)
  (dst : ℕ) (a b : ℕ → Option (List II × ℕ)) (wa wb : Runner.W) {code : List II} {top K : ℕ} {fp : Runner.W},
  floatFiniteAddL F dst a b = some (code, top) →
    F.fracBits + F.ebits < 64 →
      FB ≤ dst + 1 →
        F.fracBits < 64 →
          2 ^ F.ebits - 1 < 2 ^ 64 →
            2 ^ F.fracBits - 1 < 2 ^ 64 →
              2 ^ F.fracBits < 2 ^ 64 →
                top ≤ K →
                  dst + 11 < K →
                    dst + 17 ≤ K →
                      ∀ (executed : List II) (before : Runner.Mem),
                        before.rd64 (slot fp (BitVec.ofNat 64 (dst + 1))) = some wa →
                          before.rd64 (slot fp (BitVec.ofNat 64 (dst + 2))) = some wb →
                            before.rd64 (slot fp (BitVec.ofNat 64 (dst + 3))) =
                                some (floatFieldWord wa (F.fracBits + F.ebits) 1) →
                              before.rd64 (slot fp (BitVec.ofNat 64 (dst + 4))) =
                                  some (floatFieldWord wb (F.fracBits + F.ebits) 1) →
                                (∀ i < 4,
                                    before.rd64 (slot fp (BitVec.ofNat 64 (dst + 5 + i))) =
                                      some (finiteAddRemainingValue F wa wb i)) →
                                  ∀ (it : ℕ),
                                    floatStateSlotsL (dst + 1)
                                          ([a, b, fun j =>
                                              floatFieldL (F.fracBits + F.ebits) 1 j fun k =>
                                                some ([ci 2 (↑k : ℤ) ((↑dst : ℤ) + 1) 0], k + 1),
                                              fun j =>
                                              floatFieldL (F.fracBits + F.ebits) 1 j fun k =>
                                                some ([ci 2 (↑k : ℤ) ((↑dst : ℤ) + 2) 0], k + 1)] ++
                                            finiteAddRemaining F dst) =
                                        some (executed, it) →
                                      let values := fun i => (before.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0;
                                      ∀ i < 8,
                                        values (dst + 1 + i) =
                                          match i with
                                          | 0 => wa
                                          | 1 => wb
                                          | 2 => floatFieldWord wa (F.fracBits + F.ebits) 1
                                          | 3 => floatFieldWord wb (F.fracBits + F.ebits) 1
                                          | x => finiteAddRemainingValue F wa wb (i - 4) := by
  intro F dst a b wa wb code top K fp compiled width lower frac mask fracMask hiddenBound room sortRoom alignRoom executed before ra rb rsx rsy fields it hi values
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

end Gabbro.Stage0.Senke
