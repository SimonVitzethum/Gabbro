/- One request-register model shared by register and result-area providers. -/
module
public import Stage0.Senke.Tor
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- The six argument registers of a request, by number. -/
def reqArg (q : Runner.Req) : Nat → Runner.W
  | 0 => q.a1
  | 1 => q.a2
  | 2 => q.a3
  | 3 => q.a4
  | 4 => q.a5
  | 5 => q.a6
  | _ => 0

theorem reqArg_mk (nr : Runner.W) (f : Nat → Runner.W) :
    ∀ i, i < 6 → reqArg ⟨nr, f 0, f 1, f 2, f 3, f 4, f 5⟩ i = f i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | _ + 6, h => absurd h (by omega)

/-- Request registers encode scalar arguments. Internal pointer markers are ignored here:
    the buffer premise of `TorOK.puf` separately constrains the physical buffer address. -/
def ArgsW (L : Lay D) (f : Nat → Runner.W) : {τs : List Ty} → Env D τs → Prop
  | [], .nil => True
  | τ :: _, .cons v ρ => (if isPtr τ then True else Enc L τ v (f 0)) ∧ ArgsW L (fun j => f (j + 1)) ρ

end Gabbro.Stage0.Senke
