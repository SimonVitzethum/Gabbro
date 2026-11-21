module

public import Stage0.Senke.Start
public import Stage0.Senke.Bild.Mehr.StartupOperands
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke

open Runner Runner.IR Runner.Mem Runner.Beweis Runner.Mach Gabbro.Stage0.Senke.BildMehr

/-- The two immediate instructions preceding a clone write the exact
    relocated entry and frame into the issuer's TSO view. The bytes of
    the clone site and the rest of the memory outside scratch agree
    with their original values. -/
theorem spawn_prepare_prefix [Kern] {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {pc fp : W} {K s a f : Nat}
    (running : before.ths[i]? = some (some (.next ⟨pc, fp⟩)))
    (code : CodeAt (before.ms.1.view i) pc (spawnOne s a f))
    (frame : FrameOK (before.ms.1.view i) fp K)
    (far : CodeFar pc 10 fp K)
    (room : s + 2 ≤ K) (slots : K < 2 ^ 31) (address : a < 2 ^ 31) (stack : f < 2 ^ 31) :
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] 10
        ⟨after, before.ths.set i (some (.next ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ j, j ≠ i → after.1.view j = before.ms.1.view j) ∧
      Agree fp s K (before.ms.1.view i) (after.1.view i) ∧
      InsAt (after.1.view i) (pc + BitVec.ofNat 64 (16 * 2)) 24 (II.f ((s + 2 : Nat) : Int))
        (II.f s) (II.f 0) ∧
      (after.1.view i).rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofNat 64 a) ∧
      (after.1.view i).rd64 (slot fp (BitVec.ofNat 64 s) + 8) = some (BitVec.ofNat 64 f) := by
  have first : InsAt (before.ms.1.view i) pc 1 (II.f s) (II.f a) (II.f 0) := by
    have h := code 0 (by rw [spawnOne_len]; decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at h
    exact h
  have sx0 : sx (II.f s) = BitVec.ofNat 64 s := sx_nat (by omega)
  have sx1 : sx (II.f ((s + 1 : Nat) : Int)) = BitVec.ofNat 64 (s + 1) := sx_nat (by omega)
  have writable0 : Mem.all before.ms.1.m.wr (slot fp (sx (II.f s))) 8 = true := by
    rw [sx0, ← foldl_wr (before.ms.1.buf i) before.ms.1.m]
    exact frame.wr s (by omega)
  obtain ⟨middle, prefix0, committed0, view0, other0⟩ := tso_const_prefix running first writable0
  rw [sx0, sx_nat address] at view0
  have same0 : Agree fp s K (before.ms.1.view i) (middle.1.view i) := by
    rw [view0]
    exact agree_write frame.room (Nat.le_refl _) (by omega) _
  have code0 := code.agree same0 (spawnOne_len s a f ▸ far)
  have second : InsAt (middle.1.view i) (pc + 16) 1 (II.f ((s + 1 : Nat) : Int))
      (II.f f) (II.f 0) := code0 1 (by rw [spawnOne_len]; decide)
  let middleCfg : Cfg (TSO layout) (Res T) :=
    ⟨middle, before.ths.set i (some (.next ⟨pc + 16, fp⟩))⟩
  have running1 : middleCfg.ths[i]? = some (some (.next ⟨pc + 16, fp⟩)) :=
    List.getElem?_set_self (List.getElem?_eq_some_iff.mp running).1
  have writable1 : Mem.all middle.1.m.wr (slot fp (sx (II.f ((s + 1 : Nat) : Int)))) 8 = true := by
    rw [sx1, ← foldl_wr (middle.1.buf i) middle.1.m]
    exact (frame.agree same0).wr (s + 1) (by omega)
  obtain ⟨after, prefix1, committed1, view1, other1⟩ := tso_const_prefix running1 second writable1
  rw [sx1, sx_nat stack] at view1
  have same1 : Agree fp s K (middle.1.view i) (after.1.view i) := by
    rw [view1]
    exact agree_write frame.room (Nat.le_succ _) (by omega) _
  have same := same0.trans same1
  have decoded := (code.agree same (spawnOne_len s a f ▸ far)) 2 (by rw [spawnOne_len]; decide)
  have advanced : (pc + 16 + 16) = pc + BitVec.ofNat 64 (16 * 2) := pcN pc 1 1 2 rfl
  refine ⟨after, ?_, committed1.trans committed0, fun j different => (other1 j different).trans (other0 j different),
    same, decoded, ?_, ?_⟩
  · simpa only [middleCfg, nxt, List.set_set, List.nil_append, advanced, Nat.reduceAdd] using prefix0.trans prefix1
  · rw [view1, rd64_write_far (slot_far frame.room (by omega) (by omega) (by omega)), view0]
    exact rd64_wr64 (wr64_some (frame.wr _ (by omega))) (frame.rd _ (by omega))
  · rw [show (8 : W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus, view1]
    have next := frame.agree same0
    exact rd64_wr64 (wr64_some (next.wr _ (by omega))) (next.rd _ (by omega))

end Gabbro.Stage0.Senke
