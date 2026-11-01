module

public import Grammatik.Bausteine.Arena.Ownership.Body.Forms
public import Grammatik.Bausteine.Arena.Ownership.Body.Sound.Teil2

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Body
open Source
variable {D : Deklaration}
section Sound
variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}
  {O : Orakel D} {passes : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
  {fr : Frame} {s0 : State}

end Sound

#print axioms ob_sound
#print axioms oe_sound

end Gabbro.Grammatik.ArenaOwnership.Body
