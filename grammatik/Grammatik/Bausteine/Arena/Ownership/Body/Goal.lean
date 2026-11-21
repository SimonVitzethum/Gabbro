module
public import Grammatik.Bausteine.Arena.Ownership.Body.Program
public import Grammatik.Bausteine.Arena.Struktur.ArenaBaumWelt
public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Program
public import Grammatik.Zielsatz.Kern.Spec
@[expose] public section


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

/-- **The ownership acceptance**: every body passes the check for every declared arena. -/
def ownershipAccepted (E : Einheit D) (arenas : List (ArenaIface D)) (fs : List D.Fn) : Bool :=
  arenas.all fun a => checkProgram E.P a.A a.I fs

/-- **The ownership goal.** -/
theorem ownership_goal (E : Einheit D) (arenas : List (ArenaIface D)) (fs : Aufzaehlung D.Fn)
    (hacc : ownershipAccepted E arenas fs.1 = true) (O : Orakel D) (hH : HardwareAnnahmen O E.Q) :
    ∀ a ∈ arenas, ∀ (passes n : Nat), Respects a.A a.I.contracts (rufAt E.P O passes n) := by
  intro a ha passes
  exact checkProgram_calls fs.2 (List.all_eq_true.mp hacc a ha) hH.1 passes

#print axioms ownership_goal

end Gabbro.Grammatik.ArenaOwnership.Body
