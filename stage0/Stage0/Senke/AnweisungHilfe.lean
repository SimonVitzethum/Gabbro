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

end Gabbro.Stage0.Senke
