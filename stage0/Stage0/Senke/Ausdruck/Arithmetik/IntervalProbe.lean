/- Joint high-bit source/compiler/frame witness for scalar interval narrowing. -/
import Stage0.Senke.Ausdruck.Arithmetik.Scalar
import Stage0.Senke.Ausdruck.FnptrAufrufProben

namespace Gabbro.Stage0.Senke.IntervalProbe
open Gabbro.Grammatik Runner.IR Runner.Mem

abbrev high : Int := 9223372036854775808
abbrev maximum : Int := 18446744073709551615

def input : Expr FnptrProben.D [] [] (.int 0 maximum) :=
  .widen (by decide) (by decide) (.lit high)

def expression : Expr FnptrProben.D [] [] (.int 0 (maximum - 1)) :=
  .eng input 0 (maximum - 1) (.widen (by decide) (by decide) (.lit 0))

def compiled : List II × Nat := (lowE FnptrProben.callLayout expression 4).getD ([], 0)
def bytes : List Runner.B := compiled.1.flatMap encII

theorem lowered : lowE FnptrProben.callLayout expression 4 = some compiled := by decide +kernel
theorem code_length : compiled.1.length = 40 := by decide +kernel
theorem code_top : compiled.2 = 8 := by decide +kernel

def memory : Runner.Mem :=
  { FnptrProben.callMem with b := fun a =>
      if 2048 ≤ a.toNat ∧ a.toNat < 2048 + bytes.length then
        (bytes[a.toNat - 2048]?).getD 0 else FnptrProben.callMem.b a }

theorem memory_code : CodeAt memory 2048 compiled.1 := by
  apply codeAt_bytes compiled.1 2048 (by decide +kernel)
  intro i hi
  change i < bytes.length at hi
  have size : bytes.length = 640 := by simp only [bytes, flatMap_enc_len, code_length]
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

end Gabbro.Stage0.Senke.IntervalProbe

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR IntervalProbe

/-- The actual generated program has code, frame, world and environment jointly
    satisfied, and leaves the complete unsigned high-bit value in its result. -/
theorem eng_ok_zeuge [Kern] :
    ValueOk FnptrProben.callLayout memory 2048 4096 256 4 compiled.1
      (.int 0 (maximum - 1)) ⟨high, by decide, by decide⟩ := by
  let W := fun m => WeltAt m FnptrProben.callLayout FnptrProben.world
  have pre : Pre FnptrProben.callLayout memory 2048 4096 256 4 compiled.1
      (Env.nil : Env FnptrProben.D []) W := by
    refine ⟨by decide, by decide, memory_frame, memory_code, ?_, ?_, memory_world,
      weltAt_stab FnptrProben.call_win.lay FnptrProben.call_win.top⟩
    · rw [code_length]
      unfold CodeFar
      decide +kernel
    · intro _ x; nomatch x
  exact lowE_int_value_ok FnptrProben.world FnptrProben.world (fun _ h => h)
    FnptrProben.call_win.lay expression (by decide) lowered (by change compiled.2 ≤ 256; rw [code_top]; decide) memory Env.nil pre

end Gabbro.Stage0.Senke
