/- Axiom audit of the conditional-termination and unbounded-stack results.
   This file checks the existing goal theorem as well; it makes no universality claim. -/
import Grammatik.Berechenbarkeit.RunsUntilWitnesses
import Grammatik.Berechenbarkeit.RecursionBoundary

#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
#print axioms Gabbro.Grammatik.Terminierung.ExitTrace.run
#print axioms Gabbro.Grammatik.Terminierung.exitTrace_of_run
#print axioms Gabbro.Grammatik.Terminierung.run_iff_exitTrace
#print axioms Gabbro.Grammatik.Terminierung.run_mono
#print axioms Gabbro.Grammatik.Terminierung.exists_run_iff_exitTrace
#print axioms Gabbro.Grammatik.Terminierung.run_of_rank
#print axioms Gabbro.Grammatik.Terminierung.untilBody_exec
#print axioms Gabbro.Grammatik.Terminierung.runsUntil_iff
#print axioms Gabbro.Grammatik.Terminierung.untilBody_has_exit
#print axioms Gabbro.Grammatik.Terminierung.untilBody_exit_guard
#print axioms Gabbro.Grammatik.Terminierung.untilBody_continue_guard
#print axioms Gabbro.Grammatik.Terminierung.runsUntil_post
#print axioms Gabbro.Grammatik.Terminierung.runsUntil_of_rank
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.assignment_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.insufficient_budget_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.larger_budget_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.rank_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.false_guard_budget
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.false_guard_never_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.conditional_classes_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.memory_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RunsUntilWitnesses.memory_guard_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.push_step
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.head_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.step_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.reached_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.depth_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.unbounded_stack
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.rejected_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.accepted_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.claimed_measure_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.no_measure_duty
#print axioms Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary.no_wellFounded_ranking
