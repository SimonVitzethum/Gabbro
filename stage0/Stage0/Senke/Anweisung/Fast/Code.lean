module
public import Runner.IR.Rahmen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- Code and its scratch ceiling, with a length computed while composing chunks.
    No scope step needs to count the already emitted suffix again. -/
structure CodeCache where
  value : List II × Nat
  size : Nat
  correct : size = value.1.length

namespace CodeCache

def ofPair (value : List II × Nat) : CodeCache :=
  { value := value
    size := value.1.length
    correct := rfl }

def append (head tail : CodeCache) : CodeCache :=
  { value := (head.value.1 ++ tail.value.1, max head.value.2 tail.value.2)
    size := head.size + tail.size
    correct := (by rw [head.correct, tail.correct, List.length_append]) }

/-- Faithful caches are determined by the original result alone. -/
theorem ofPair_value (cached : CodeCache) : ofPair cached.value = cached := by
  cases cached with
  | mk value size correct => cases correct; rfl

theorem append_ofPair (head tail : List II × Nat) :
    append (ofPair head) (ofPair tail) =
      ofPair (head.1 ++ tail.1, max head.2 tail.2) := by
  unfold append ofPair
  simp only [List.length_append]

/-- A branch can use the cached size while its equality proof uses the specification length. -/
theorem size_ofPair (value : List II × Nat) : (ofPair value).size = value.1.length := rfl

theorem value_ofPair (value : List II × Nat) : (ofPair value).value = value := rfl

theorem map_value (value : Option (List II × Nat)) :
    (value.map ofPair).map CodeCache.value = value := by
  cases value <;> rfl

end CodeCache
end Gabbro.Stage0.Senke
