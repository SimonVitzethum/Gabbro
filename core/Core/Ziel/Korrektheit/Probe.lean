module

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

/-- Deliberately faulty statement: the guard must report it, then this module is removed. -/
def ProbeFalscheAussage (p : Nat) (f : Nat → Prop) : Prop := ∀ q : Nat, True

end Gabbro.Core.Ziel.Korrektheit
