module

public import Grammatik.Logik.Invarianten.VC.ExtendedArithmetic
import all Batteries.Data.Except

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

namespace Gabbro.Grammatik.Invarianten.VC.ExtendedWitness

open Frag Elim Elim.Korrekt Modell
open Gabbro.Grammatik.Invarianten.VC.Witness

/-- The false decision has both an extracted arithmetic assignment and an
    actual typed G execution that destroys the invariant. -/
theorem overflow_assignment_zeuge :
    ∃ values : Assignment (Observation declaration),
      Extended.writerCounterexample overflowingCompiled entry .tru = some values :=
  Extended.writerCounterexample_complete overflowingCompiled entry .tru overflow_decided_zeuge

theorem overflow_execution_zeuge :
    (match execEnd oracle 0 calls overflowingWriter counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false := by decide +kernel

theorem temporary_execution_zeuge :
    (match execEnd oracle 0 calls temporaryWriter counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => false) = true := by decide +kernel

/-- An over-budget loop is a definite refusal, not an unchecked fallback. -/
theorem over_budget_refused_zeuge :
    (extendedEnd program noFacts noLockFacts 0 none 64 boundedWriter .nil post).toOption.isNone = true := by
  decide +kernel

theorem conditional_initializer_counterexample_zeuge :
    eval counterexampleWorld invariant counterexampleWorld .nil = true ∧
    (match execEnd oracle 0 calls (conditionalWriter false) counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false := by
  change wahr? (eval counterexampleWorld invariant counterexampleWorld .nil) = true ∧ _
  decide +kernel

theorem traversal_contract_accepted_zeuge :
    Vertraege.Pruefer.KontrakteGeprueftB (traversalProgram true)
      (SperrInv.leer declaration) [()] = true := by decide +kernel

theorem traversal_contract_refused_zeuge :
    Vertraege.Pruefer.KontrakteGeprueftB (traversalProgram false)
      (SperrInv.leer declaration) [()] = false := by decide +kernel

theorem traversal_logic_stop_zeuge :
    (match execEnd oracle 0 calls ((traversalProgram false).rumpf ()) counterexampleWorld .nil with
      | .logik .schleife => true
      | _ => false) = true := by decide +kernel

end Gabbro.Grammatik.Invarianten.VC.ExtendedWitness
