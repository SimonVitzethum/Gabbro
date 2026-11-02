module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil6a

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
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
