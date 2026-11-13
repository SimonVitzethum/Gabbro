/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Lage.lean
  Subject:   Where the parts of the ticket form of the lock code lie (`locksCodeT`, `Ticket/Code.lean`): the take
              at 0, the body at 35, the gives at `35 + cb`, `52 + cb` and `69 + cb`, the jumps after them at
              `51 + cb`, `68 + cb` and `85 + cb`; the whole is `cb + 86` long.
-/
module
public import Stage0.Senke.Sperre.Ticket.Code
public import Stage0.Senke.Sperre.Paar
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem locksT_at (L : Lay D) (a s : Nat) (cb : List II) (x y : Int) :
    At (locksCodeT L a s cb x y) 0 (nimmT L a s) ∧
    At (locksCodeT L a s cb x y) 35 cb ∧
    At (locksCodeT L a s cb x y) (35 + cb.length) (gibT L a s) ∧
    (locksCodeT L a s cb x y)[51 + cb.length]? = some (ci 18 (16 * (1 + 2 * ((gibT L a s).length + 1))) 0 0) ∧
    At (locksCodeT L a s cb x y) (52 + cb.length) (gibT L a s) ∧
    (locksCodeT L a s cb x y)[68 + cb.length]? = some (ci 18 (16 + x + 16 * ((gibT L a s).length + 1)) 0 0) ∧
    At (locksCodeT L a s cb x y) (69 + cb.length) (gibT L a s) ∧
    (locksCodeT L a s cb x y)[85 + cb.length]? = some (ci 18 (16 + y) 0 0) := by
  have hn := nimmT_len L a s
  have hg := gibT_len L a s
  refine ⟨At.of_eq (xs := []) (by simp only [locksCodeT, List.append_assoc, List.nil_append]; rfl) rfl,
    At.of_eq (xs := nimmT L a s) (by simp only [locksCodeT, List.append_assoc, List.nil_append]; rfl) (by omega),
    At.of_eq (xs := nimmT L a s ++ cb) (by simp only [locksCodeT, List.append_assoc, List.nil_append]; rfl)
      (by simp; omega),
    At.one (At.of_eq (xs := nimmT L a s ++ cb ++ gibT L a s)
      (by simp only [locksCodeT, List.append_assoc, List.nil_append]; rfl) (by simp; omega)),
    At.of_eq (xs := nimmT L a s ++ cb ++ gibT L a s ++ [_])
      (by simp only [locksCodeT, List.append_assoc, List.nil_append]; rfl) (by simp; omega),
    At.one (At.of_eq (xs := nimmT L a s ++ cb ++ gibT L a s ++ [_] ++ gibT L a s)
      (by simp only [locksCodeT, List.append_assoc, List.nil_append]; rfl) (by simp; omega)),
    At.of_eq (xs := nimmT L a s ++ cb ++ gibT L a s ++ [_] ++ gibT L a s ++ [_])
      (by simp only [locksCodeT, List.append_assoc, List.nil_append]; rfl) (by simp; omega),
    At.one (At.of_eq (xs := nimmT L a s ++ cb ++ gibT L a s ++ [_] ++ gibT L a s ++ [_] ++ gibT L a s)
      (by simp only [locksCodeT, List.append_assoc, List.nil_append]; rfl) (by simp; omega))⟩

end Gabbro.Stage0.Senke
