module

public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Lemmas
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Sound.Teil2

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Body
open Source
variable {D : Deklaration}
section Sound
variable {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn} {V : Vertrag D} {out : Flow.Output A V.erg}
variable (hvoll : ∀ f, f ∈ fs)
include hvoll

end Sound

end Gabbro.Grammatik.ArenaOwnership.Body
