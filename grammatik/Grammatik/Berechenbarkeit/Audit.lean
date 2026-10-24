/- Axiom audit of the conditional-termination and unbounded-stack results.
   This file checks the existing goal theorem as well; it makes no universality claim. -/
import Grammatik.Berechenbarkeit.RunsUntilWitnesses
import Grammatik.Berechenbarkeit.RecursionBoundary
import Grammatik.Berechenbarkeit.AdmissionBoundary
import Grammatik.Berechenbarkeit.TerminationCompatibility
import Grammatik.Berechenbarkeit.Brainfuck.Witnesses
import Grammatik.Berechenbarkeit.Storage.CallReturn

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

-- Universality development: exact intermediate compiler and termination boundaries.
#print axioms Gabbro.Grammatik.Berechenbarkeit.AdmissionBoundary.unmeasured_non_tail_rejected
#print axioms Gabbro.Grammatik.Berechenbarkeit.AdmissionBoundary.admitted_cycle_has_measure_or_tail
#print axioms Gabbro.Grammatik.Berechenbarkeit.AdmissionBoundary.rejection_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.AdmissionBoundary.conditional_tail_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.TerminationCompatibility.no_complete_halting_test
#print axioms Gabbro.Grammatik.Berechenbarkeit.TerminationCompatibility.reference_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.runFor_sound
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.runFor_complete
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.runFor_iff
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.haltsWith_iff_fuel
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.runFor_mono
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.runFor_translation
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.halt_iff
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.increment_wrap
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.decrement_wrap
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.jump_exec
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.instruction_correct
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.step_correct
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.respects
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.evaluation_correct
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.termination_iff
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.reachable_preservation
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.reachable_reflection
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.steps_iff_reaches
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.haltsWith_iff_eval
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.compiler_correct
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.transfer_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.transfer_halts_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.transfer_tm2_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.insufficient_fuel_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.eof_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.nested_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.wrap_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.output_before_divergence_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.spin_step_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.self_loop_not_terminating
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.divergence_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.tm2_divergence_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.invalid_brackets_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.finite_initial_nonempty
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.finite_initial_reaches
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.finite_compiler_correct
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.growing_next
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.growing_reached
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.unbounded_tape_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.Witnesses.unbounded_tm2_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn.callFits
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn.call_step
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn.return_step
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn.reached_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn.retained_bit_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn.terminating_classes_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn.accepted_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Brainfuck.finiteMachine
