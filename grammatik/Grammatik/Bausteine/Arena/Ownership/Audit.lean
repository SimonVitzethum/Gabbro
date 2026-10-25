import Grammatik.Bausteine.Arena.Ownership.FactoryWitness
import Grammatik.Bausteine.Arena.Ownership.Source.Witness
import Grammatik.Bausteine.Arena.Ownership.Source.ForwardWitness
import Grammatik.Bausteine.Arena.Ownership.Body.Goal
import Grammatik.Bausteine.Arena.Ownership.Machine.Reach
import Grammatik.Bausteine.Arena.Ownership.Ruhe.Witness

/-! Kernel-checked public audit of the ownership extension. The general body
judgment and its soundness are in `Body/`, ownership on every reachable
machine G, GA and GX in `Machine/`; whole-program integration is
recorded separately in PLAN-DYNAMIC §12. -/

namespace Gabbro.Grammatik.ArenaOwnership

#print axioms rufAt_ownership
#print axioms consume_call
#print axioms identity_result
#print axioms borrow_result
#print axioms factory_checked
#print axioms factory_oom_path
#print axioms factory_result
#print axioms FactoryWitness.factory_then_caller_free
#print axioms FactoryWitness.oom_keeps_empty_ledger
#print axioms Source.checkExpression_sound
#print axioms Source.checked_release
#print axioms Source.checked_binding
#print axioms Source.allocation_context
#print axioms Source.Witness.checked_release_witness
#print axioms Source.Witness.reuse_cannot_restore_alias
#print axioms Source.checked_bodies
#print axioms Source.checked_calls
#print axioms Source.checked_consuming_call
#print axioms Source.checked_owning_result
#print axioms Source.checked_factory_result
#print axioms Source.checked_factory_reason
#print axioms Source.forwardDestructor_checked
#print axioms Source.forwardIdentity_checked
#print axioms Source.ForwardWitness.nested_return_and_release
#print axioms Source.ForwardWitness.borrowed_call_restores_owner
#print axioms Source.consumed_argument_cannot_repeat
#print axioms Source.loan_reservation_blocks_consumption
#print axioms Body.handoff_requires
#print axioms Body.return_plain
#print axioms Body.return_owner
#print axioms Body.call_value
#print axioms Body.callInd_value
#print axioms Body.ob_sound
#print axioms Body.oe_sound
#print axioms Body.checked_bodies
#print axioms Body.checked_calls
#print axioms Body.Witness.checked
#print axioms Body.Witness.actual_run_closed
#print axioms Body.chkE_sound
#print axioms Body.checkProgram_sound
#print axioms Body.checkProgram_calls
#print axioms Body.witness_checked
#print axioms Body.ownership_goal
#print axioms Body.ownership_goal_witness
#print axioms Machine.ownInv_step
#print axioms Machine.ownInv_reach
#print axioms Machine.ownInv_reachGA
#print axioms Machine.ownInv_reachGX
#print axioms Ruhe.checked_mitRuhe
#print axioms Ruhe.threadFacts_of
#print axioms Ruhe.startOwn_arenen
#print axioms Ruhe.GoalWitness.besitz_zeuge
#print axioms Ruhe.GoalWitness.actual_run

end Gabbro.Grammatik.ArenaOwnership
