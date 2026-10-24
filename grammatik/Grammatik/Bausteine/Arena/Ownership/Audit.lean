import Grammatik.Bausteine.Arena.Ownership.FactoryWitness
import Grammatik.Bausteine.Arena.Ownership.Source.Witness
import Grammatik.Bausteine.Arena.Ownership.Source.ForwardWitness

/-! Kernel-checked public audit of the ownership extension. Source admission
and whole-program integration are recorded separately in PLAN-DYNAMIC §12. -/

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

end Gabbro.Grammatik.ArenaOwnership
