/- Capturing an entry cell in the immutable frame header. -/
import Stage0.Senke.Ausdruck.Old.Sound

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable [Kern]
variable {D : Deklaration} {L : Lay D}

theorem SnapAt.lese {cs : List (Zelle D)} {σ : World D} {m : Runner.Mem} {fp : Runner.W}
    (h : SnapAt L cs σ m fp) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    SnapAt L cs (σ.lese Λ os) m fp := by
  intro c hc
  obtain ⟨w, hw, he⟩ := h c hc
  refine ⟨w, hw, ?_⟩
  cases c <;> exact he

/-- Loading a world word into a reserved slot needs no variable environment at that slot. -/
theorem capture_load {m : Runner.Mem} {pc fp : Runner.W} {K : Nat} {a w : Runner.W}
    (hf : FrameOK m fp K) (hk : K < 2 ^ 31) (hd : 3 < K)
    (hc : CodeAt m pc [ci 15 3 3 0])
    (ha : m.rd64 (slot fp (BitVec.ofNat 64 3)) = some a) (hw : m.rd64 a = some w) :
    Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ (write m (slot fp (BitVec.ofNat 64 3)) 8 w.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply Star.one
  apply run_step (t := ⟨pc, fp⟩) hi (by decide)
  simp only [op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [show sx (II.f (3 : Int)) = (3 : Runner.W) by decide +kernel]
  refine run_rd64 ha ?_
  refine run_rd64 hw ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [show sx (II.f (3 : Int)) = (3 : Runner.W) by decide +kernel]
  exact run_wr64 (wr64_some (hf.wr 3 hd))

/-- Capture either no entry value or one cell. All parameters and return addresses survive. -/
theorem snapC_ok {cs : List (Zelle D)} {c : List II} {m : Runner.Mem} {pc fp : Runner.W}
    {K : Nat} {σ : World D} (hc : snapC L cs = some c) (hf : FrameOK m fp K)
    (hk : K < 2 ^ 31) (hd : 3 < K) (hcode : CodeAt m pc c) (hfar : CodeFar pc c.length fp K)
    (hw : WeltAt m L σ) (hl : LayIn L) (hwl : fp.toNat + 8 * K ≤ L.lo) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
      Agree fp 3 K m m' ∧ SnapAt L cs σ m' fp ∧
      (∀ j, j < K → j ≠ 3 → m'.rd64 (slot fp (BitVec.ofNat 64 j)) = m.rd64 (slot fp (BitVec.ofNat 64 j))) := by
  cases cs with
  | nil =>
    simp only [snapC, Option.some.injEq] at hc
    subst c
    exact ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, (fun _ h => nomatch h), fun _ _ _ => rfl⟩
  | cons z zs =>
    cases zs with
    | cons _ _ => simp [snapC] at hc
    | nil =>
      simp only [snapC] at hc
      split at hc
      · next htest =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
        cases hc
        let m1 := write m (slot fp (BitVec.ofNat 64 3)) 8 (BitVec.ofInt 64 (z.adr L)).toNat
        have s1 := quant_lit (m := m) (pc := pc) (fp := fp) (K := K) (dst := 3) (v := (z.adr L : Int)) hf hk hd (codeAt_left (b := [ci 15 3 3 0]) hcode) htest.2
        have a1 : Agree fp 3 K m m1 := agree_write hf.room (Nat.le_refl _) hd _
        have hf1 := hf.agree a1
        have hfar1 := codeFar_right (n := 1) (k := 1) hfar
        have hc1 := (codeAt_right (a := [ci 1 3 (z.adr L) 0]) hcode).agree a1 hfar1
        have hw1 : WeltAt m1 L σ := weltAt_stab hl hwl m m1 hw (a1.mono (Nat.zero_le _))
        obtain ⟨w, hword, he⟩ : ∃ w, m1.rd64 (BitVec.ofNat 64 (z.adr L)) = some w ∧ Enc L z.ty (z.val σ) w := by
          cases z with
          | glob g => exact hw1.2.1 g
          | elem t f k => exact hw1.1 t f k htest.1
        have ha : m1.rd64 (slot fp (BitVec.ofNat 64 3)) = some (BitVec.ofNat 64 (z.adr L)) := by
          simpa only [m1, BitVec.ofInt_natCast] using rd_same (a := 3) hf hd (BitVec.ofInt 64 (z.adr L))
        have s2 := capture_load hf1 hk hd hc1 ha hword
        let m2 := write m1 (slot fp (BitVec.ofNat 64 3)) 8 w.toNat
        have a2 : Agree fp 3 K m1 m2 := agree_write hf1.room (Nat.le_refl _) hd _
        refine ⟨m2, ?_, a1.trans a2, ?_, ?_⟩
        · simpa [m1, m2, BitVec.add_assoc] using s1.trans s2
        · intro z' hz
          simp only [List.mem_singleton] at hz
          subst z'
          exact ⟨w, rd_same (a := 3) hf1 hd w, he⟩
        · intro j hj hne
          dsimp only [m2, m1]
          rw [rd_other (a := 3) (b := j) hf1.room hd hj (Ne.symm hne), rd_other (a := 3) (b := j) hf.room hd hj (Ne.symm hne)]
      · cases hc

end Gabbro.Stage0.Senke
