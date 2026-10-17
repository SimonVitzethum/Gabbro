/-
  Physical page reclamation beneath ArenaDyn's existing free-slot semantics.
  Links are metadata, not bytes in freed payloads: discarding an empty chunk
  must preserve the logical LIFO list, including for one-byte elements.
  This proves the storage rule, not the operating system or Rust producer.
-/
import Grammatik.Bausteine.Arena.ArenaDyn
import Grammatik.Bausteine.Schablonen.SchablonenArena

namespace Gabbro.Grammatik.ArenaDyn

structure SeitenZustand where
  slots : FreiZustand
  payload : Nat → Nat

def Live (F : FreiZustand) (i : Nat) : Prop := i < F.belegt ∧ i ∉ F.frei

def EmptyChunk (F : FreiZustand) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → i < F.belegt → i ∈ F.frei

/-- Page discard changes only payload; the free-list links live separately. -/
def discard (S : SeitenZustand) (lo hi : Nat) : SeitenZustand :=
  { S with payload := fun i => if lo ≤ i ∧ i < hi then 0 else S.payload i }

theorem discard_live (S : SeitenZustand) (lo hi i : Nat)
    (empty : EmptyChunk S.slots lo hi) (live : Live S.slots i) :
    (discard S lo hi).payload i = S.payload i := by
  have h : ¬ (lo ≤ i ∧ i < hi) := fun h => live.2 (empty i h.1 h.2 live.1)
  simp [discard, h]

theorem discard_preserves_reuse (S : SeitenZustand) (lo hi : Nat) :
    freiAlloc (discard S lo hi).slots = freiAlloc S.slots := rfl

theorem discard_live_zeuge :
    let S : SeitenZustand := ⟨⟨3, [0, 1], by intro i h; simp at h; omega⟩, fun i => i + 7⟩
    EmptyChunk S.slots 0 2 ∧ Live S.slots 2 ∧
    (discard S 0 2).payload 2 = 9 ∧ (freiAlloc (discard S 0 2).slots).1 = 0 := by
  refine ⟨?_, by simp [Live], by decide, by decide⟩
  intro i _ hi _
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl <;> simp

end Gabbro.Grammatik.ArenaDyn
