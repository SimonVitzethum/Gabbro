import Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses
import Grammatik.Berechenbarkeit.Storage.GStack.Multi
import Grammatik.Berechenbarkeit.Storage.HeapAudit

/-! Axiom audit of the actual, capacity-bounded G stack bridge.
The imported heap audit retains the separate unbounded component boundary. -/

#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Represents.list_ok
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Represents.unique
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.represents_empty
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Represents.nonempty
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Represents.frame
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Represents.reads
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.linkPush_prefix
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.linkPush_values
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.linkPush_grants
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.linkPop_prefix
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.linkPop_values
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.free_prefix
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.free_values
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.popAndRelease_values
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.fresh_allocated
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.reused_allocated
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.push_values
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.tryPush_refused
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.tryPush_values
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.linkPush_termination
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.free_termination
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.fresh_termination
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.reuse_termination
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.popAndRelease_termination
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.empty_contents
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.initial_free
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.refused_push_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.empty_pop_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.reused_contents
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.reused_push_values_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.roundTrip_correct
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.fresh_round_trip_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.reused_round_trip_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.program_exec_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.program_termination_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses.program_accepted_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.push_owned
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.pop_owned
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses.empty_agrees
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses.reused_valid
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses.reused_agrees
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses.reused_other_owns
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses.cycle
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses.fresh_owned_cycle_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses.reused_owned_cycle_zeuge
#print axioms Gabbro.Grammatik.Terminierung.ExitTrace.length_unique
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.emptyGuard_eval
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Represents.empty_head
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.drain_trace
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.drain_bound
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.drain_iff_budget
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses.exact_budget_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses.drain_values_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses.insufficient_budget_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses.empty_budget_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses.conditional_class_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses.core_accepted_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses.program_return_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.MultiRep.stapel
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.multiRep_leer
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.push_multi
#print axioms Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.pop_multi
