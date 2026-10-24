import Grammatik.Bausteine.Arena.Ownership.Body.Check.Program
import Grammatik.Zielsatz.Kern.Spec

/-! **The ownership leg beside the goal statement.** The checker reads, beside
the unit, its arenas with their ownership interfaces and decides
`ownershipAccepted`. Under the goal's own named hardware assumptions
(`HardwareAnnahmen`, of which only the oracle frame `GutO` is used) every
actual call of the program keeps its ownership interface, at every depth and
budget. Nothing is taken from the user's obligation (`NutzerPflichtA`) and
nothing new is assumed of RAM or hardware.

This is a statement BESIDE `GabbroZiel`: folding it into `Spec.lean` (the
acceptance target `AkzeptiertSpecX` and the conclusion `ZielX`) is a change of
the reviewed statement and waits for that review; the per-step lifting onto
the GA/GX machine is open (`PLAN-DYNAMIC` 12.8). -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source Zielsatz

variable {D : Deklaration}

/-- An arena of the unit with the ownership interfaces of its functions. -/
structure ArenaIface (D : Deklaration) where
  A : FreiForm D
  I : Interfaces A

/-- **The ownership acceptance**: every body passes the check for every declared arena. -/
def ownershipAccepted (E : Einheit D) (arenas : List (ArenaIface D)) (fs : List D.Fn) : Bool :=
  arenas.all fun a => checkProgram E.P a.A a.I fs

/-- **The ownership goal.** -/
theorem ownership_goal (E : Einheit D) (arenas : List (ArenaIface D)) (fs : Aufzaehlung D.Fn)
    (hacc : ownershipAccepted E arenas fs.1 = true) (O : Orakel D) (hH : HardwareAnnahmen O E.Q) :
    ∀ a ∈ arenas, ∀ (passes n : Nat), Respects a.A a.I.contracts (rufAt E.P O passes n) := by
  intro a ha passes
  exact checkProgram_calls fs.2 (List.all_eq_true.mp hacc a ha) hH.1 passes

/-- Non-vacuity: every unit whose program is the witness program is accepted with its arena. -/
theorem ownership_goal_witness (E : Einheit Witness.D) (hP : E.P = Witness.P) :
    ownershipAccepted E [⟨Witness.A, Witness.I⟩] [true, false] = true := by
  simp only [ownershipAccepted, hP, List.all_cons, List.all_nil, Bool.and_true]
  exact witness_passes

#print axioms ownership_goal

end Gabbro.Grammatik.ArenaOwnership.Body
