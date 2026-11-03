module

public import Grammatik.Zielsatz.Atomar.BeweisAtomar
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0
public import Stage0.Senke.Ausdruck.Tag
public import Stage0.Senke.Ausdruck.Quant.Proben
public import Stage0.Senke.Anweisung.Bytes.Proben
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.ControlProbes
public import Stage0.Bindung.Proben

@[expose] public section


#print axioms Gabbro.Grammatik.Parser.ExportWitnesses2.arrayTraversal_source_zeuge
#print axioms Gabbro.Grammatik.Parser.ExportPreservation.member_meaning
#print axioms Gabbro.Grammatik.Parser.ExportPreservation.member_footprint
#print axioms Gabbro.Grammatik.Parser.ExportPreservation.strings_gate
#print axioms Gabbro.Stage0.Compiled.initializer_exports
#print axioms Gabbro.Stage0.exported_batch2_ir_correct_zeuge
-- Contended locks: named OS return behavior and explicit interference premises.
#print axioms Runner.IR.futexOK_zeuge
#print axioms Gabbro.Stage0.Senke.add_waiters
#print axioms Gabbro.Stage0.Senke.LockInv.increment
#print axioms Gabbro.Stage0.Senke.LockInv.decrement
#print axioms Gabbro.Stage0.Senke.LockOK.invariant
#print axioms Gabbro.Stage0.Senke.futex_prepare
#print axioms Gabbro.Stage0.Senke.futex_entry
#print axioms Gabbro.Stage0.Senke.futex_return
#print axioms Gabbro.Stage0.Senke.nimm_wait_entry
#print axioms Gabbro.Stage0.Senke.nimm_wait_retry
#print axioms Gabbro.Stage0.Senke.nimm_retry
#print axioms Gabbro.Stage0.Senke.nimm_retry_acquired
#print axioms Gabbro.Stage0.Senke.gib_release
#print axioms Gabbro.Stage0.Senke.gib_waiters_entry
#print axioms Gabbro.Stage0.Senke.gib_waiters_return
#print axioms Gabbro.Stage0.Senke.WaitProbe.nimm_wait_acquired_zeuge
#print axioms Gabbro.Stage0.Senke.WaitProbe.gib_waiters_zeuge
#print axioms Gabbro.Stage0.Senke.WaitProbe.nimm_wait_spurious_zeuge
#print axioms Gabbro.Stage0.Senke.WaitProbe.sync_waiters_zeuge
#print axioms Gabbro.Stage0.Senke.ReservedByteProbe.putBytes_reserved_sentinel_zeuge
-- The first private-frame rely component for concurrent IR refinement.
#print axioms Gabbro.Stage0.Senke.AgreeK.foreign_word
#print axioms Gabbro.Stage0.Senke.AgreeK.foreign_frame
#print axioms Gabbro.Stage0.Senke.foreign_frame_zeuge
#print axioms Gabbro.Stage0.Senke.EntrySnapshots.capture_ok
#print axioms Gabbro.Stage0.Senke.EntrySnapshots.complete_at
#print axioms Gabbro.Stage0.Senke.EntrySnapshots.values_at
#print axioms Gabbro.Stage0.Senke.EntrySnapshots.At.agreeW
#print axioms Gabbro.Stage0.Senke.DistinctSnapshotProbe.capture_ok_zeuge
#print axioms Gabbro.Stage0.Senke.lowEnsAt_ok
#print axioms Gabbro.Stage0.Senke.publishResult_run
#print axioms Gabbro.Stage0.Senke.entryFrame_run
#print axioms Gabbro.Stage0.Senke.OldProbe.multiple_occurrences_zeuge
#print axioms Gabbro.Stage0.Senke.OldProbe.distinct_occurrences_zeuge
#print axioms Gabbro.Stage0.Senke.OldProbe.computed_snapshot_zeuge
#print axioms Gabbro.Stage0.Senke.CompleteSnapshotEnvProbe.complete_at_zeuge
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
#print axioms Gabbro.Stage0.Senke.ReturnProtocolProbe.publishResult_run_zeuge
#print axioms Gabbro.Stage0.Senke.EntryProtocolProbe.entryFrame_run_zeuge

-- Total binary64 addition, from decoded source operands through the Block hook.
#print axioms Gabbro.Stage0.Senke.softRound_exaktAdd_aligned
#print axioms Gabbro.Stage0.Senke.softAlignedMagnitude_bounds
#print axioms Gabbro.Stage0.Senke.routineDirectionalWord_canonical
#print axioms Gabbro.Stage0.Senke.routineSource_sum
#print axioms Gabbro.Stage0.Senke.routineSource_sum_zeuge
#print axioms Gabbro.Stage0.Senke.routineFiniteDirectionalWord_model
#print axioms Gabbro.Stage0.Senke.softAddRoutine_ok
#print axioms Gabbro.Stage0.Senke.softAddRoutineL_ok
#print axioms Gabbro.Stage0.Senke.softAddRoutine_ok_zeuge
#print axioms Gabbro.Stage0.Senke.softFloatContinuationL_ok
#print axioms Gabbro.Stage0.Senke.softFloatWordsL_ok
#print axioms Gabbro.Stage0.Senke.softFloatReject_none
#print axioms Gabbro.Stage0.Senke.softFloatRangeL_ok
#print axioms Gabbro.Stage0.Senke.blockFloatArithmetic_case
#print axioms Gabbro.Stage0.Senke.FloatArithmeticProbe.float_add_accepted_zeuge

-- Binary64 subtraction reuses the total adder after exactly one sign-bit xor.
#print axioms Gabbro.Stage0.Senke.floatSub_eq_add_neg
#print axioms Gabbro.Stage0.Senke.softNegWord_model
#print axioms Gabbro.Stage0.Senke.softNeg_model
#print axioms Gabbro.Stage0.Senke.softSub_model
#print axioms Gabbro.Stage0.Senke.softSubRoutine_ok
#print axioms Gabbro.Stage0.Senke.softAddOperandL_ok
#print axioms Gabbro.Stage0.Senke.softSub_model_zeuge
#print axioms Gabbro.Stage0.Senke.softSubRoutine_ok_zeuge
#print axioms Gabbro.Stage0.Senke.floatArithmeticBlockL_supported
#print axioms Gabbro.Stage0.Senke.FloatArithmeticProbe.float_sub_accepted_zeuge
