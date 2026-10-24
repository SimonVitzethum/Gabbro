import Grammatik.Berechenbarkeit.Storage.GStack.Witnesses
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
