/- Joint actual-memory witness for the complete scalar result contract. -/
import Stage0.Senke.Ausdruck.Arithmetik.Scalar
import Stage0.Senke.Ausdruck.FnptrAufrufProben

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable [Kern]

/-- The existing caller's first instruction produces the full integer value,
    with its real memory, frame, code, world and environment jointly present. -/
theorem lowE_int_value_ok_zeuge :
    ValueOk FnptrProben.callLayout FnptrProben.callMem 2048 4096 256 4 [ci 1 4 8192 0]
      (.int 8192 8192) ⟨8192, by decide, by decide⟩ := by
  let W := fun m => WeltAt m FnptrProben.callLayout FnptrProben.world
  have caller : Pre FnptrProben.callLayout FnptrProben.callMem 2048 4096 256 4
      FnptrProben.caller (Env.nil : Env FnptrProben.D []) W :=
    { FnptrProben.call_pre with
      welt := FnptrProben.call_world
      wstab := weltAt_stab FnptrProben.call_win.lay FnptrProben.call_win.top }
  have pre := Pre.left (a := [ci 1 4 8192 0])
    (b := [ci 15 4 4 0] ++ callTailN 0 0 4 true ++ [ci 2 4 6 0]) caller
  exact lowE_int_value_ok (reserved := 0) (top := 5) (Λ := []) FnptrProben.world FnptrProben.world (fun _ h => h)
    (.lit 8192) (by decide) (by decide +kernel) (by decide) _ Env.nil pre

end Gabbro.Stage0.Senke
