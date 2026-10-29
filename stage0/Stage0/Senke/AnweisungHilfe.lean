/-
  File:      stage0/Stage0/Senke/AnweisungHilfe.lean
  Subject:   Small steps for statements: `mov` into a slot, code addresses after concatenation.
-/
import Stage0.Senke.Umgebung

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

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

theorem star_cast {t t' u u' : T} {m m' : Runner.Mem} (h : Star t m t' m') (h1 : t = u) (h2 : t' = u') :
    Star u m u' m' := by subst h1; subst h2; exact h

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

end Gabbro.Stage0.Senke
