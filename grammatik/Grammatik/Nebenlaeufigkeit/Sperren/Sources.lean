module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T1a

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

variable {D : Deklaration}

/-- Optional source evidence for a semantic lock predicate. This is part of
    the model value, not a proof submitted to or checked by the compiler.
    The concrete invariant checker refuses a used lock without reification. -/
structure ReifiedLock (S : SperrInv D) (lock : D.Lock) where
  resources : List (Res D)
  expression : Expr D [] resources .bool
  correct : ∀ world, eval world expression world .nil = S.inv lock world.speicher

abbrev LockSources (S : SperrInv D) := ∀ lock, Option (ReifiedLock S lock)

end Gabbro.Grammatik.Invarianten.Pruefer
