import Grammatik.Bausteine.Arena.Ownership.FactoryWitness
import Grammatik.Bausteine.Arena.Ownership.Source.Witness

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

end Gabbro.Grammatik.ArenaOwnership
