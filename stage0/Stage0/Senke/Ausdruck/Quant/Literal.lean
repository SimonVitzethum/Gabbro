/- The common immediate-write primitive depends only on frame and IR semantics. -/
module
public import Stage0.Senke.Ausdruck.Sim
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
/-- An immediate assignment, with the resulting memory explicit. -/
theorem quant_lit [Kern] {m : Runner.Mem} {pc fp : Runner.W} {K dst : Nat} {v : Int}
    (hf : FrameOK m fp K) (hk : K < 2 ^ 31) (hd : dst < K)
    (hc : CodeAt m pc [ci 1 dst v 0]) (hv : lit32 v = true) :
    Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ (write m (slot fp (BitVec.ofNat 64 dst)) 8 (BitVec.ofInt 64 v).toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply Star.one
  apply run_step (t := ⟨pc, fp⟩) hi (by decide)
  simp only [op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_lit hv, sx_nat (by omega)]
  exact run_wr64 (wr64_some (hf.wr dst hd))

end Gabbro.Stage0.Senke
