module
public import Stage0.Senke.Anweisung.Satz
public import Stage0.Senke.Sperre.Interference
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Two distinct reason arms under a lock at or above the function's floor (`ueberBodenB`) are lowered (the body
    under the enclosing scope `lk`). The generic `lowS_ok` lock case uses `locks_okT` for the give on normal, leave
    and next outcomes and `locks_okT_zurueck`/`locks_okT_why` for returns. -/
theorem locks_reason_zeuge {D : Deklaration} (passes : Nat) (A : D.Fn → Nat)
    (L : Lay D) (f : D.Fn) (lk : D.Lock) (hb : ueberBodenB (vertragVon D f).boden (D.rang lk) = true) :
    let body : Block D (vertragVon D f) false [.why 2] [.held lk] [.held lk] :=
      .cons (.onWhy (.var .here) (.cons .nil (.cons .nil .nil))) .nil
    ∃ code top, lowS passes A L
        ⟨D.params f, D.erg f, D.gruende f, 0, 0⟩ ([], 0) [] (0, 0)
        (Stmt.locks lk (fun _ h => (List.not_mem_nil h).elim) body) = some (code, top) ∧
        code.length > 0 := by
  simp only [lowS]
  split
  · exact ⟨_, _, rfl, by simp only [locksCodeT_len]; omega⟩
  · next hc => exact absurd ⟨hb, rfl, rfl⟩ hc

end Gabbro.Stage0.Senke
