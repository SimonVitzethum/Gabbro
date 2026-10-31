/- Shared contiguous frame-word transport. Width is explicit and never inferred from a value. -/
import Runner.IR.Rahmen

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Copy an already materialized value into fresh frame storage, in increasing word order.
    Callers must separate the source from the destination (the execution theorem states this precisely). -/
def copyWords : Nat → Nat → Nat → List II
  | 0, _, _ => []
  | n + 1, dst, src => ⟨2, dst, src, 0⟩ :: copyWords n (dst + 1) (src + 1)

@[simp] theorem copyWords_length (n dst src : Nat) : (copyWords n dst src).length = n := by
  induction n generalizing dst src with
  | zero => rfl
  | succ n ih => simp [copyWords, ih]

/-- A frame value occupies consecutive words; byte addressing stays in the runner's `slot`. -/
def WordsAt (m : Runner.Mem) (fp : Runner.W) (base : Nat) (words : List Runner.W) : Prop :=
  ∀ i (hi : i < words.length),
    m.rd64 (slot fp (BitVec.ofNat 64 (base + i))) = some words[i]

end Gabbro.Stage0.Senke
