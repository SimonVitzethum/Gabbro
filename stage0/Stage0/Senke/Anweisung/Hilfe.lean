/-
  File:      stage0/Stage0/Senke/Anweisung/Hilfe.lean
  Subject:   Small steps for statements: `mov` into a slot, code addresses after concatenation.
-/
import Stage0.Senke.Stopp

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

/-- `mov j s`: slot `j` gets the word of slot `s`. -/
theorem mov_to {m : Runner.Mem} {pc fp : Runner.W} {K j s : Nat} {w : Runner.W}
    (hc : CodeAt m pc [ci 2 j s 0]) (hF : FrameOK m fp K) (hj : j < K) (hs : s < K) (hK : K < 2 ^ 31)
    (hv : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [ci 2 j s 0].length), fp⟩
      (write m (slot fp (BitVec.ofNat 64 j)) 8 w.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  refine star_ins hc (by simp [ci]) ?_
  simp only [ci, op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  refine run_rd64 hv ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  exact run_wr64 (wr64_some (hF.wr j hj))

theorem addr_norm (pc : Runner.W) (a b : Nat) :
    pc + BitVec.ofNat 64 a + BitVec.ofNat 64 b = pc + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem pc_add1 (pc : Runner.W) (a b : List II) :
    pc + BitVec.ofNat 64 (16 * (a ++ b).length) = pc + BitVec.ofNat 64 (16 * a.length) +
      BitVec.ofNat 64 (16 * b.length) := by
  rw [pc_add, List.length_append]

/-- The protected slots `pr` (a loop's counter) read the same. -/
def Keeps (fp : Runner.W) (pr : List Nat) (m m' : Runner.Mem) : Prop :=
  ∀ j ∈ pr, m'.rd64 (slot fp (BitVec.ofNat 64 j)) = m.rd64 (slot fp (BitVec.ofNat 64 j))

theorem Keeps.refl (fp : Runner.W) (pr : List Nat) (m : Runner.Mem) : Keeps fp pr m m := fun _ _ => rfl

theorem Keeps.trans {fp : Runner.W} {pr : List Nat} {m1 m2 m3 : Runner.Mem} (h1 : Keeps fp pr m1 m2)
    (h2 : Keeps fp pr m2 m3) : Keeps fp pr m1 m3 := fun j hj => (h2 j hj).trans (h1 j hj)

/-- Code that changes only slots from `d` on keeps the protected slots below `d`. -/
theorem keeps_of_agree {fp : Runner.W} {pr : List Nat} {d K : Nat} {m m' : Runner.Mem} (ha : Agree fp d K m m')
    (hr : fp.toNat + 8 * K ≤ 2 ^ 64) (hp : ∀ j ∈ pr, j < d) (hd : d ≤ K) : Keeps fp pr m m' :=
  fun j hj => agree_rd_low ha hr (hp j hj) hd

/-- Writing slot `x` keeps the protected slots when `x` is none of them. -/
theorem keeps_write {fp : Runner.W} {pr : List Nat} {K x : Nat} {m : Runner.Mem} (hr : fp.toNat + 8 * K ≤ 2 ^ 64)
    (hx : x < K) (hp : ∀ j ∈ pr, j < K) (hn : x ∉ pr) (v : Nat) :
    Keeps fp pr m (write m (slot fp (BitVec.ofNat 64 x)) 8 v) := fun j hj =>
  rd64_write_far (slot_far hr hx (hp j hj) (fun e => hn (e ▸ hj)))

/-! ## The guard over a slot -/

theorem guard_brz {m : Runner.Mem} {pc : Runner.W} {a c s : Nat} (hc : CodeAt m pc (guardC a c s)) :
    InsAt m pc 19 (II.f (a : Int)) (II.f 32) (II.f 0) := by
  have h := hc 0 (by simp [guardC])
  simpa [guardC, ci] using h

/-- The guard over slot `a`, which holds zero: `exit_group(c)`. -/
theorem guard_stop {m : Runner.Mem} {pc fp : Runner.W} {K a c s : Nat} (hc : CodeAt m pc (guardC a c s))
    (hf : CodeFar pc 5 fp K) (hF : FrameOK m fp K) (ha : a < K) (hs : s + 8 ≤ K) (hK : K < 2 ^ 31)
    (hcode : c < 2 ^ 31) (h0 : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some 0) : Stops ⟨pc, fp⟩ m c := by
  have hbrz := guard_brz hc
  have hd : sx (II.f (a : Int)) = BitVec.ofNat 64 a := sx_nat (by omega)
  have hl : sx (II.f 32) = BitVec.ofNat 64 32 := sx_nat (d := 32) (by omega)
  have sb := Star.one (run_step (t := ⟨pc, fp⟩) hbrz (by decide)
    (run_brz_zero (t := ⟨pc, fp⟩) hbrz (by rw [hd]; exact h0)))
  rw [hl] at sb
  exact Stops.prefix sb (stop_ok (codeAt_right (a := [ci 19 a 32 0, ci 18 64 0 0]) hc)
    (codeFar_right (n := 2) (k := 3) hf) hF hs hK hcode)

/-- The guard over slot `a`, which holds a nonzero word: on after the guard, nothing written. -/
theorem guard_pass {m : Runner.Mem} {pc fp : Runner.W} {a c s : Nat} {v : Runner.W}
    (hc : CodeAt m pc (guardC a c s)) (ha : a < 2 ^ 31) (hv : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some v)
    (hne : v ≠ 0) : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (guardC a c s).length), fp⟩ m := by
  have hbrz := guard_brz hc
  have hd : sx (II.f (a : Int)) = BitVec.ofNat 64 a := sx_nat (by omega)
  have rb := run_brz_ne (t := ⟨pc, fp⟩) hbrz (by rw [hd]; exact hv) hne
  have sb := star_ins (fp := fp) (m' := m) (codeAt_left (a := [ci 19 a 32 0]) hc) (by simp [ci])
    (by simp only [ci]; exact rb)
  have hj := codeAt_right (a := [ci 19 a 32 0]) hc
  have hjmp := hj 0 (by simp [guardC])
  simp only [guardC, ci, List.cons_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hjmp
  have sj := Star.one (run_step (t := ⟨_, fp⟩) hjmp (by decide) (run_jmp (t := ⟨_, fp⟩) hjmp))
  have hl : sx (II.f 64) = BitVec.ofNat 64 64 := sx_nat (d := 64) (by omega)
  rw [hl] at sj
  refine star_cast (sb.trans sj) rfl ?_
  simp only [T.mk.injEq, and_true, List.length_singleton, addr_norm]
  rfl

end Gabbro.Stage0.Senke
