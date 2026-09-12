/-
  File:      Grammatik/CSLInvariante.lean
  Subject:   THE CSL RESOURCE INVARIANT -- THE MAIN THEOREM (lane 81).

  While lock L is free everywhere, the L-guarded table's invariant holds.
  Lane 54 proved the leaf lemma for non-oracle leaves
  (`blatt_slots_t_gleich` in CSLInvarianteC.lean) and cut the main theorem
  because `Stmt.axiomCall` could write guarded tables without the lock.
  Lane 74 repaired that: `axiomCall` carries `hd`/`hgd`, and
  `FremdSperre.lean` proves `axiomCall_haelt_waechter`. This file extends
  the leaf argument to `axiomCall` (oracle frame + `hd` + `HeldGenau`)
  and runs the induction over `PCReach`.
-/
import Grammatik.Maschine
import Grammatik.CSLInvarianteC
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Witness invariant on the reference fixture: the two slots of `konto`
    agree. True at the start (both `0`), local to `konto` slots, and not
    trivially true for every memory (see `badSp81`). -/
def refInv81 (σ : Speicher refD) : Prop :=
  σ.slots () 0 () = σ.slots () 1 ()

/-! ## CUTS
  - Green: `refInv81` (definition only so far).
  - Open: the leaf extension to `axiomCall`, the main induction
    `csl_ressourceninvariante`, and its witness
    `csl_ressourceninvariante_zeuge`.
-/

#print axioms Gabbro.Grammatik.refInv81

end Gabbro.Grammatik
