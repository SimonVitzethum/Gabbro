module

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership

structure Frame where
  thread : Nat
  activation : Nat
  deriving DecidableEq, Repr

end Gabbro.Grammatik.ArenaOwnership
