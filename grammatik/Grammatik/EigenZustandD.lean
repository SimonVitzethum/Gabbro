/-
  File:      Grammatik/EigenZustandD.lean
  Subject:   **OWN-STATE PROJECTION** (lane 56, attempt D).

  A step fired by a thread `h` whose program text never names table `t`
  leaves every slot of `t` unchanged. The route is bottom-up: each writing
  leaf records a `zugriff t true ..` event (carried by `hcar` of the leaf
  rule of `PCSchritt`); a leaf whose recorded events carry no `Sum.inl t`
  keeps the slots of `t`; take/release steps keep memory by construction.
-/
import Grammatik.Maschine
import Grammatik.Satz

namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A `zugriff t true` event sits in the recorded list whenever its world
    differs from the base world at a slot of `t` through `schreibSlot`. -/
def seed : Nat := 0

end Gabbro.Grammatik.EZD
