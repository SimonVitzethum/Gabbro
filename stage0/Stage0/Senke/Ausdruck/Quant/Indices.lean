/- Shared finite table-index enumeration for expression and statement loops. -/
import Stage0.Senke.Ausdruck
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
/-- The indices from `k` on, `n` of them. -/
def idxAb (c : Int) (k n : Nat) : List (Zahl 0 (c - 1)) :=
  (List.range' k n).filterMap fun (j : Nat) =>
    if h : ((j : Nat) : Int) ≤ c - 1 then some ⟨((j : Nat) : Int), by omega, h⟩ else none

theorem alleIndizes_ab (c : Int) : alleIndizes c = idxAb c 0 c.toNat := by
  unfold alleIndizes idxAb
  rw [List.range_eq_range']

theorem idxAb_zero (c : Int) (k : Nat) : idxAb c k 0 = [] := by simp [idxAb]

theorem idxAb_succ (c : Int) (k n : Nat) (hk : (k : Int) < c) :
    ∃ x : Zahl 0 (c - 1), x.n = k ∧ idxAb c k (n + 1) = x :: idxAb c (k + 1) n := by
  refine ⟨⟨k, by omega, by omega⟩, rfl, ?_⟩
  simp only [idxAb, List.range'_succ, List.filterMap_cons]
  rw [dif_pos (by omega)]


end Gabbro.Stage0.Senke
