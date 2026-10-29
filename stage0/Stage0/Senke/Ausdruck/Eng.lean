/-
  File:      stage0/Stage0/Senke/Ausdruck/Eng.lean
  Subject:   Signed interval narrowing: evaluate once, keep a fitting word or execute the fallback.
-/
import Stage0.Senke.Ausdruck.Top

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern] {D : Deklaration}

/-- A binary instruction may read any two frame slots, including its destination. -/
theorem eng_bin_ok {m : Runner.Mem} {pc fp : Runner.W} {K d a b o : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {va vb r : Runner.W}
    {g : Runner.W → Runner.W → Option Runner.W}
    (hp : Pre m pc fp K d [ci o d a b] ρ W) (hd : d < K) (ha : a < K) (hb : b < K)
    (ra : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some va)
    (rb : m.rd64 (slot fp (BitVec.ofNat 64 b)) = some vb)
    (hop : op o = bin g) (ho : o < 256) (hg : g va vb = some r) :
    Ok m pc fp K d [ci o d a b] (· = r) := by
  have := hp.small
  refine one_ok hp (by simpa [ci] using ho) hd rfl fun m' hw => ?_
  have hi := hp.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  simp only [ci]
  rw [hop]
  apply run_bin hi
  · simpa only [sx_nat (d := a) (by omega)] using ra
  · simpa only [sx_nat (d := b) (by omega)] using rb
  · exact hg
  · simpa only [sx_nat (d := d) (by omega)] using hw

/-- The five test instructions preserve the value in `d` and put the outside flag in `d+1`. -/
theorem eng_test_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {lo hi : Int}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {v : Runner.W}
    (hp : Pre m pc fp K (d + 1) (engTest d lo hi) ρ W) (hd : d + 2 < K)
    (hl : lit32 lo = true) (hh : lit32 hi = true)
    (rv : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some v) :
    Ok m pc fp K (d + 1) (engTest d lo hi)
      (· = Runner.IR.bool (v.slt (BitVec.ofInt 64 lo) || (BitVec.ofInt 64 hi).slt v)) := by
  change Pre _ _ _ _ _ ([ci 1 (d+1) lo 0] ++ ([ci 13 (d+1) d (d+1)] ++
    ([ci 1 (d+2) hi 0] ++ ([ci 13 (d+2) (d+2) d] ++ [ci 9 (d+1) (d+1) (d+2)])))) _ _ at hp
  obtain ⟨m1, s1, a1, w1, r1, rfl⟩ := const_ok hp.left hl (by omega)
  have h1 := hp.next a1 (Nat.le_refl _) (by omega)
  have rv1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some v := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]; exact rv
  obtain ⟨m2, s2, a2, w2, r2, rfl⟩ := eng_bin_ok (d := d+1) (a := d) (b := d+1) h1.left (by omega) (by omega) (by omega)
    rv1 r1 (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have h2 := h1.next a2 (Nat.le_refl _) (by omega)
  obtain ⟨m3, s3, a3, w3, r3, rfl⟩ := const_ok (d := d+2)
    { h2.left with ctx := by have := hp.ctx; omega } hh (by omega : d+2 < K)
  have h3 := h2.next (a3.mono (by omega : d+1 ≤ d+2)) (Nat.le_refl _) (by omega)
  have rv3 : m3.rd64 (slot fp (BitVec.ofNat 64 d)) = some v := by
    rw [agree_rd_low (a1.trans a2 |>.trans (a3.mono (by omega))) hp.frame.room (by omega) (by omega)]; exact rv
  obtain ⟨m4, s4, a4, w4, r4, rfl⟩ := eng_bin_ok (d := d+2) (a := d+2) (b := d)
    { h3.left with ctx := by have := hp.ctx; omega }
    (by omega : d+2 < K) (by omega) (by omega) r3 rv3
    (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  have h4 := h3.next (a4.mono (by omega : d+1 ≤ d+2)) (Nat.le_refl _) (by omega)
  have r24 : m4.rd64 (slot fp (BitVec.ofNat 64 (d+1))) = some (Runner.IR.bool (v.slt (BitVec.ofInt 64 lo))) := by
    rw [agree_rd_low (a3.trans a4) h2.frame.room (by omega) (by omega)]; exact r2
  obtain ⟨m5, s5, a5, w5, r5, rfl⟩ := eng_bin_ok (d := d+1) (a := d+1) (b := d+2) h4 (by omega) (by omega) (by omega) r24 r4
    (g := fun x y => some (x ||| y)) rfl (by decide) rfl
  refine ⟨m5, ?_, a1.trans (a2.trans ((a3.mono (by omega)).trans ((a4.mono (by omega)).trans a5))), _, r5, ?_⟩
  · simpa only [engTest, List.length_cons, List.length_nil, List.length_singleton, pc_add,
      Nat.reduceAdd] using s1.trans (s2.trans (s3.trans (s4.trans s5)))
  · simp only [bool_word]; exact or_word _ _

end Gabbro.Stage0.Senke
