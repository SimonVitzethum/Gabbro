module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.BleibtImBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Every instruction emitted by the left-projection block is relocatable,
    and its single backward jump stays behind its own position. -/
theorem verschiebbarLeft (ein aus frei : Nat) :
    VerschiebbaresProgramm (leftBlk ein aus frei) := by
  unfold VerschiebbaresProgramm
  intro j hj
  rw [leftBlkLaenge] at hj
  interval_cases j <;>
    simp only [leftBlk, sqrtPrefix, sqrtInit, sqrtLoop, kopie, leftSel,
      List.append_assoc, List.nil_append, List.append_nil, List.cons_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      List.length_cons, List.length_nil] at hj ⊢
  all_goals
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [Verschiebbar]
    · intro d hd
      cases hd <;> omega

/-- Every instruction emitted by the right-projection block is relocatable,
    and its single backward jump stays behind its own position. -/
theorem verschiebbarRight (ein aus frei : Nat) :
    VerschiebbaresProgramm (rightBlk ein aus frei) := by
  unfold VerschiebbaresProgramm
  intro j hj
  rw [rightBlkLaenge] at hj
  interval_cases j <;>
    simp only [rightBlk, sqrtPrefix, sqrtInit, sqrtLoop, kopie, rightSel,
      List.append_assoc, List.nil_append, List.append_nil, List.cons_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      List.length_cons, List.length_nil] at hj ⊢
  all_goals
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [Verschiebbar]
    · intro d hd
      cases hd <;> omega

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
