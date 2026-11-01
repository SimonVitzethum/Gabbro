import Stage0.Senke.Anweisung.Satz
import Stage0.Senke.Sperre.ContendedProbe
import Stage0.Senke.Sperre.WaitProbe
import Stage0.Senke.Sperre.Interference

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Two distinct reason arms jointly satisfy the lock gate and actual emission.
    The generic `lowS_ok` lock case continues to use `locks_ok` and
    `retFreiB_istZ`, including release on normal, leave and next outcomes. -/
theorem locks_reason_zeuge {D : Deklaration} (passes : Nat) (A : D.Fn → Nat)
    (L : Lay D) (f : D.Fn) (lk : D.Lock) :
    let body : Block D (vertragVon D f) false [.why 2] [.held lk] [.held lk] :=
      .cons (.onWhy (.var .here) (.cons .nil (.cons .nil .nil))) .nil
    retFreiB body = true ∧
      ∃ code top, lowS passes A L 0 ([], 0) [] (0, 0)
        (Stmt.locks lk (fun _ h => (List.not_mem_nil h).elim) body) = some (code, top) ∧
        code.length > 0 := by
  refine ⟨rfl, ?_⟩
  exact ⟨_, _, rfl, by simp only [locksCode, List.length_append, List.length_cons, List.length_nil, nimmC_len, gibC_len]; omega⟩

end Gabbro.Stage0.Senke
