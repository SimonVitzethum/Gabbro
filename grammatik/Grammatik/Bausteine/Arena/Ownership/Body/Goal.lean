import Grammatik.Bausteine.Arena.Ownership.Body.Check.Program
import Grammatik.Bausteine.Arena.Ownership.Body.Witness
import Grammatik.Zielsatz.Kern.Spec

/-! **The ownership leg beside the goal statement.** The checker reads, beside
the unit, its arenas with their ownership interfaces and decides
`ownershipAccepted`. Under the goal's own named hardware assumptions
(`HardwareAnnahmen`, of which only the oracle frame `GutO` is used) every
actual call of the program keeps its ownership interface, at every depth and
budget. Nothing is taken from the user's obligation (`NutzerPflichtA`) and
nothing new is assumed of RAM or hardware.

This is the sequential statement over `rufAt`, per call; the per-machine leg
on every GA/GX run is `ZielFX.besitz` in `GabbroZiel` (`Spec.lean`). -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source Zielsatz

variable {D : Deklaration}

/-- The witness program passes the executable check, decided by the kernel. -/
theorem witness_passes : checkProgram Witness.P Witness.A Witness.I [true, false] = true := by decide

theorem witness_checked : Checked Witness.P Witness.A Witness.I :=
  checkProgram_sound (fun f => by cases f <;> simp only [List.mem_cons, Bool.false_eq_true, List.not_mem_nil, or_false, or_true, Bool.true_eq_false, or_self]) witness_passes

#print axioms witness_checked

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
