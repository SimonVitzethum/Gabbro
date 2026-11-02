/- Joint high-bit source/compiler/frame witness for mixed scalar ordering. -/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Scalar
public import Stage0.Senke.Ausdruck.Zeiger.FnptrAufrufProben
@[expose] public section


namespace Gabbro.Stage0.Senke.MixedProbe
open Gabbro.Grammatik Runner.IR Runner.Mem

abbrev maximum : Int := 18446744073709551615

def expression : Expr FnptrProben.D [] [] .bool :=
  .lt (.lit (-1)) (.lit maximum)

def compiled : List II × Nat := (lowE FnptrProben.callLayout expression 4).getD ([], 0)
def bytes : List Runner.B := compiled.1.flatMap encII

theorem lowered : lowE FnptrProben.callLayout expression 4 = some compiled := by decide +kernel
theorem code_length : compiled.1.length = 6 := by decide +kernel
theorem code_top : compiled.2 = 9 := by decide +kernel

def memory : Runner.Mem :=
  { FnptrProben.callMem with b := fun a =>
      if 2048 ≤ a.toNat ∧ a.toNat < 2048 + bytes.length then
        (bytes[a.toNat - 2048]?).getD 0 else FnptrProben.callMem.b a }

theorem memory_code : CodeAt memory 2048 compiled.1 := by
  apply codeAt_bytes compiled.1 2048 (by decide +kernel)
  intro i hi
  change i < bytes.length at hi
  have size : bytes.length = 96 := by simp only [bytes, flatMap_enc_len, code_length]
  have bound : 2048 + i < 2 ^ 64 := by omega
  have address : (BitVec.ofNat 64 (2048 + i)).toNat = 2048 + i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  refine ⟨rfl, rfl, ?_⟩
  have low : 2048 ≤ 2048 + i := by omega
  have upper : 2048 + i < 2048 + bytes.length := by omega
  change memory.b (BitVec.ofNat 64 (2048 + i)) = bytes[i]
  simp [memory, address, low, upper, Nat.add_sub_cancel_left, hi]

theorem memory_frame : FrameOK memory 4096 256 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem memory_world [Kern] : WeltAt memory FnptrProben.callLayout FnptrProben.world := by
  refine ⟨(fun t => nomatch t), (fun g => ?_), (fun _ _ _ => rfl)⟩
  cases g
  exact ValueAt.ofCellWord (w := 64) (by decide) (by decide +kernel) rfl

end Gabbro.Stage0.Senke.MixedProbe

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR MixedProbe

/-- The actual generated program has code, frame, world and environment jointly
    satisfied, and leaves the complete mixed comparison result in its result. -/
theorem scalarCompareL_ok_zeuge [Kern] :
    ValueOk FnptrProben.callLayout memory 2048 4096 256 4 compiled.1 .bool true := by
  let W := fun m => WeltAt m FnptrProben.callLayout FnptrProben.world
  have pre : Pre FnptrProben.callLayout memory 2048 4096 256 4 compiled.1
      (Env.nil : Env FnptrProben.D []) W := by
    refine ⟨by decide, by decide, memory_frame, memory_code, ?_, ?_, memory_world,
      weltAt_stab FnptrProben.call_win.lay FnptrProben.call_win.top⟩
    · rw [code_length]
      unfold CodeFar
      decide +kernel
    · intro _ x; nomatch x
  exact lowE_ok FnptrProben.world FnptrProben.world (fun _ h => h) FnptrProben.call_win.lay
    expression 4 compiled.1 compiled.2 lowered (by rw [code_top]; decide) memory 2048 Env.nil pre

end Gabbro.Stage0.Senke
