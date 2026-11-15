/- Execution-image bindings, independent of the compiler host. -/
module
@[expose] public section

namespace Gabbro.Stage0

/-- Waiting changes scheduling, never the FIFO ticket order. -/
inductive LockWait where
  | futex
  | spin
  deriving DecidableEq, Repr

namespace Profil

/-- The environment of the emitted image; this never describes the build host. -/
inductive ImageEnvironment where
  | linux
  | freestanding
  deriving DecidableEq, Repr

/-- The environment fixes the lock binding; unsupported combinations cannot be selected. -/
def ImageEnvironment.lockWait : ImageEnvironment → LockWait
  | .linux => .futex
  | .freestanding => .spin

end Profil
end Gabbro.Stage0
