import Grammatik.Berechenbarkeit.Storage.TM2Run
import Grammatik.Bausteine.Arena.Unbounded.Observe

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap

open ArenaOwnership (Frame)

variable {K : Type} {Γ : K → Type}

/-- Decode the linked stack with fuel from its own finite backing extent. -/
def Store.observe (S : Store Γ) (frame : Frame) (k : K) : Option (List (Γ k)) :=
  let stack := S.regions k
  ArenaStorage.Linked.readAll stack.memory frame stack.memory.extent stack.head

theorem Store.observe_correct {S : Store Γ} {frame : Frame} {values : ∀ k, List (Γ k)}
    (hr : S.Represents frame values) (k : K) : S.observe frame k = some (values k) :=
  ArenaStorage.Linked.readAll_extent (hr k).1 (hr k).2

end Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap
