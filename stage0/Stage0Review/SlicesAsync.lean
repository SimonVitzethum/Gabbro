module

import Stage0
import Grammatik.Parser.Async.Elaboration
import Grammatik.Parser.Elab.UebersetzeAllg.StringSliceObservations
import Grammatik.Nebenlaeufigkeit.Async.Representation.Reachability
import Grammatik.Nebenlaeufigkeit.Async.Representation.Completion
import Grammatik.Nebenlaeufigkeit.Async.Representation.Construction
import Grammatik.Nebenlaeufigkeit.Async.Representation.BindLowering
import Grammatik.Nebenlaeufigkeit.Async.Representation.WaitingLowering
import Grammatik.Nebenlaeufigkeit.Async.Representation.TaskLowering
import Grammatik.Nebenlaeufigkeit.Async.Representation.JoinLowering
import Grammatik.Nebenlaeufigkeit.Async.Representation.AwaitLowering
import Grammatik.Nebenlaeufigkeit.Async.Representation.Dispatch
import Grammatik.Nebenlaeufigkeit.Async.Representation.ArgumentLowering
import Grammatik.Nebenlaeufigkeit.Async.Representation.ConstructLowering
import Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedAwait
import Grammatik.Nebenlaeufigkeit.Async.Representation.CheckedPoll
import Grammatik.Nebenlaeufigkeit.Async.Representation.Poll
import Grammatik.Parser.Elab.UebersetzeAllg.RuntimeSlices
import Grammatik.Niedrig.Konstrukte.SliceCheck
import Grammatik.Niedrig.Konstrukte.GuardedSliceCarrier
import Stage0.Senke.Ausdruck.Aggregat.Stored.Carriers
import Grammatik.Nebenlaeufigkeit.Async.Creation
import Grammatik.Parser.Elab.UebersetzeAllg.ArithmeticSlices
import Grammatik.Parser.Elab.UebersetzeAllg.RecordLaws

#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specLiteralNestedRecord_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specArrayLiteral_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specLiteralTyped_low
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specArrayLocal_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specCompositeArgument_lower
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specTypedArray_low

#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertE_slice
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowerSlice_array
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowerSlice_string
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowerIndexedSlice_array
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.arraySpan_refines
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.arraySpan_reads
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_indexedArraySlice
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.indexedSlice_reads
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_stringSlice
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.arraySlice_erfuellbar
#print axioms Gabbro.Grammatik.Parser.Uebersetze.fullLocalSlice_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_fullLocalStringSlice
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_fullLocalArraySlice
#print axioms Gabbro.Grammatik.Parser.Uebersetze.fixedLocalArraySlice_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertE_localArraySpan
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_arraySpanFrom
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.arraySpanFrom_reads
#print axioms Gabbro.Grammatik.LowLevel.Construct.BoundedSlice.checkOfArray_exact
#print axioms Gabbro.Grammatik.LowLevel.Construct.ArraySliceView.check_exact
#print axioms Gabbro.Stage0.Senke.ValueAt.checked_slice_view
#print axioms Gabbro.Stage0.Senke.ValueAt.decode_slice_descriptor
#print axioms Gabbro.Stage0.Senke.lowE_slice_descriptor_ok
#print axioms Gabbro.Stage0.Senke.runtimeSliceDescriptor_ok
#print axioms Gabbro.Stage0.Senke.runtimeStringSliceDescriptor_ok
#print axioms Gabbro.Grammatik.LowLevel.Construct.ArraySliceView.value_ofEndpoints
#print axioms Gabbro.Grammatik.LowLevel.Construct.ArraySliceView.value_subslice
#print axioms Gabbro.Grammatik.LowLevel.Construct.ArraySliceView.relocated_value_eq_iff
#print axioms Gabbro.Grammatik.LowLevel.Construct.ArraySliceView.value_eq_iff
#print axioms Gabbro.Grammatik.LowLevel.Construct.ArraySliceView.value_arrSet_outside
#print axioms Gabbro.Grammatik.LowLevel.Construct.ArraySliceView.value_arrSet_inside_iff
#print axioms Gabbro.Grammatik.LowLevel.Construct.runtimeArraySlice_erfuellbar
#print axioms Gabbro.Grammatik.LowLevel.Construct.strBoundedSliceValue_exact
#print axioms Gabbro.Grammatik.LowLevel.Construct.checkStringSlice_exact
#print axioms Gabbro.Grammatik.LowLevel.Construct.checkStringSlice_result
#print axioms Gabbro.Grammatik.LowLevel.Construct.strBoundedSliceValue_byte
#print axioms Gabbro.Grammatik.LowLevel.Construct.strBoundedSliceValue_subslice
#print axioms Gabbro.Grammatik.LowLevel.Construct.guardSlice_exec
#print axioms Gabbro.Grammatik.LowLevel.Construct.stringSliceBounds_erfuellbar
#print axioms Gabbro.Stage0.Senke.ValueAt.string_slice_view
#print axioms Gabbro.Stage0.Senke.lowE_runtimeSliceLength_ok
#print axioms Gabbro.Grammatik.LowLevel.Construct.runtimeStringSlice_erfuellbar
#print axioms Gabbro.Grammatik.Parser.Uebersetze.localArraySliceLength_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertE_arraySliceLength
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.mixedArraySliceObservations_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_localArraySpanIndex
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.fixedSpanObservations_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.fixedSpanObservations_source
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.uSliceInteger_unknown
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.uSliceInteger_param
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_localArraySliceLength
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.localArraySliceIndex_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertE_localArraySliceIndex
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_localArraySliceIndex
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.runtimeSliceObservations_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.textSliceObservations_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertE_textSliceIndex
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_textSliceObservations
#print axioms Gabbro.Grammatik.LowLevel.Construct.rangeArrayCarrierExpr_exact
#print axioms Gabbro.Grammatik.LowLevel.Construct.rangeArrayCarrierExpr_erfuellbar
#print axioms Gabbro.Grammatik.LowLevel.Construct.rangeStringCarrierExpr_exact
#print axioms Gabbro.Grammatik.LowLevel.Construct.withGuardedSlice_exec
#print axioms Gabbro.Grammatik.LowLevel.Construct.withGuardedTextSlice_exec
#print axioms Gabbro.Stage0.Senke.Faeden.ImageTicketStates.draw
#print axioms Gabbro.Stage0.Senke.Faeden.ImageTicketStates.wait_reply
#print axioms Gabbro.Stage0.Senke.Faeden.ImageTicketStates.wake_reply
#print axioms Gabbro.Stage0.Senke.Faeden.image_ticket_draw_prefix
#print axioms Gabbro.Stage0.Senke.Faeden.image_ticket_wait_prefix
#print axioms Gabbro.Stage0.Senke.Faeden.image_ticket_wake_prefix
#print axioms Gabbro.Stage0.Senke.Faeden.image_ticket_waiter_CAS_prefix
#print axioms Gabbro.Stage0.Senke.Faeden.image_ticket_counter_load_prefix
#print axioms Gabbro.Stage0.Senke.Faeden.ImageTicketStates.readCounter
#print axioms Gabbro.Stage0.Senke.BildMehr.image_atomic_word_CAS
#print axioms Gabbro.Stage0.Senke.BildMehr.image_exchange_prefix
#print axioms Gabbro.Stage0.Senke.BildMehr.image_exchange_GX
#print axioms Gabbro.Stage0.Senke.BildMehr.image_awaits_prefix
#print axioms Gabbro.Stage0.Senke.BildMehr.image_awaits_GX
#print axioms Gabbro.Stage0.Senke.Faeden.ImageTicketStates.adjustWaiters
#print axioms Gabbro.Stage0.Senke.Faeden.ImageTicketStates.retryServing
#print axioms Gabbro.Stage0.Senke.Faeden.ImageTicketStates.flush
#print axioms Gabbro.Stage0.Senke.Faeden.image_release_scope
#print axioms Gabbro.Stage0.Senke.Faeden.image_admit_scope
#print axioms Gabbro.Stage0.MappedImage.single_thread_sc
#print axioms Gabbro.Stage0.Senke.BildMehr.SCMemoryPrefix.consume
#print axioms Gabbro.Stage0.Senke.BildMehr.SCMemoryPrefix.no_terminal
#print axioms Gabbro.Stage0.Senke.BildMehr.StarM.sc_reference
#print axioms Gabbro.Stage0.MappedImage.no_early_silent_terminal
#print axioms Gabbro.Grammatik.Zielsatz.EntryPrefix.activate_after_return
#print axioms Gabbro.Grammatik.Zielsatz.EntryPrefix.activate_declared_workers
#print axioms Gabbro.Stage0.ImageIRSimulation.toRunner
#print axioms Gabbro.Stage0.stage0_runner_correct_of_ir_simulation
#print axioms Gabbro.Stage0.stage0_correct_of_ir_refinement
#print axioms Gabbro.Stage0.LoadedIRImage.source_start
#print axioms Gabbro.Stage0.LoadedIRImage.workerStartup
#print axioms Gabbro.Stage0.LoadedIRImage.firstWorkerActivation
#print axioms Gabbro.Stage0.LoadedIRImage.function_semantics
#print axioms Gabbro.Stage0.irBild_function_semantics
#print axioms Gabbro.Stage0.image_body_memory_segment
#print axioms Gabbro.Grammatik.Parser.AsyncSource.segmentValue_names
#print axioms Gabbro.Grammatik.Parser.AsyncSource.tagFuture_names
#print axioms Gabbro.Grammatik.Async.inferredBoundary_erfuellbar
#print axioms Gabbro.Grammatik.Async.asyncOrder_sound
#print axioms Gabbro.Grammatik.Async.OrderedAsync.wellFounded
#print axioms Gabbro.Grammatik.Async.arrangeAsync_complete
#print axioms Gabbro.Grammatik.Async.requiredSaved_exact
#print axioms Gabbro.Grammatik.Async.ReificationDuty.cancel_releases
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.uSliceLocalType_unknown
#print axioms Gabbro.Grammatik.Parser.Uebersetze.specTextSliceArgument_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specTextSliceArgument_low
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specArraySliceArgument_low
#print axioms Gabbro.Grammatik.Parser.Uebersetze.specArraySliceArgument_erfuellbar
#print axioms Gabbro.Grammatik.Parser.Uebersetze.specArrayIndexArgument_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specArrayIndexArgument_low
#print axioms Gabbro.Stage0.Senke.ValueAt.slice_element
#print axioms Gabbro.Stage0.Senke.ValueAt.slice_view
#print axioms Gabbro.Stage0.Senke.SliceAt.agree_visible
#print axioms Gabbro.Stage0.Senke.SliceAt.subslice
#print axioms Gabbro.Stage0.Senke.SliceAt.write_slot
#print axioms Gabbro.Stage0.Senke.lowE_arrayUpdate_retainsSlices
#print axioms Gabbro.Stage0.Senke.ValueAt.string_slice_byte
#print axioms Gabbro.Stage0.Senke.lowE_runtimeSliceIndex_ok
#print axioms Gabbro.Grammatik.Parser.AsyncSource.elaborated_refines
#print axioms Gabbro.Stage0.Frontend.Async.sourceFunction
#print axioms Gabbro.Stage0.Frontend.Async.resolveLayout
#print axioms Gabbro.Stage0.Frontend.Async.LayoutResolution.frameField
#print axioms Gabbro.Grammatik.Async.Representation.initial_inv
#print axioms Gabbro.Grammatik.Async.Representation.reachable_encoded
#print axioms Gabbro.Grammatik.Async.Representation.completed_inv
#print axioms Gabbro.Grammatik.Async.Representation.cancelEpilogue_encoded
#print axioms Gabbro.Grammatik.Async.Representation.cancelCallBlock_simulates
#print axioms Gabbro.Grammatik.Async.Representation.cancelBody_simulates
#print axioms Gabbro.Grammatik.Async.Representation.pollTask_rep
#print axioms Gabbro.Grammatik.Async.Representation.await_poll_rep
#print axioms Gabbro.Grammatik.Async.Segment.waitingBlock_exec_outcome
#print axioms Gabbro.Grammatik.Async.Segment.runChildPoll_normal
#print axioms Gabbro.Grammatik.Async.Segment.childPollBlock_reports_failure
#print axioms Gabbro.Grammatik.Async.Segment.runTaskPoll_join_left_failure
#print axioms Gabbro.Grammatik.Async.Segment.runTaskPoll_join_right_failure
#print axioms Gabbro.Grammatik.Async.Segment.runWaitingPoll_error_iff
#print axioms Gabbro.Grammatik.Async.pollTaskWith_except_normal
#print axioms Gabbro.Grammatik.Async.Segment.runTaskPoll_agrees_with_inducedModel
#print axioms Gabbro.Grammatik.Async.Representation.runTaskPoll_leaf_rep
#print axioms Gabbro.Grammatik.Async.Representation.runTaskPoll_rep
#print axioms Gabbro.Grammatik.Async.Representation.await_runTaskPoll_rep
#print axioms Gabbro.Grammatik.Async.Representation.await_construction_rep
#print axioms Gabbro.Grammatik.Async.Representation.waiting_construction_inv
#print axioms Gabbro.Grammatik.Async.Representation.await_construction_preserves
#print axioms Gabbro.Grammatik.Async.Representation.await_pending_preserves
#print axioms Gabbro.Grammatik.Async.Representation.await_runTaskPoll_pending_preserves
#print axioms Gabbro.Grammatik.Async.Representation.await_resume_frame
#print axioms Gabbro.Grammatik.Async.Representation.bind_resume_frame
#print axioms Gabbro.Grammatik.Async.Representation.trimFrameExpr_rep
#print axioms Gabbro.Grammatik.Async.Representation.bindingFrameExpr_rep
#print axioms Gabbro.Grammatik.Async.Representation.resumeBlock_exec
#print axioms Gabbro.Grammatik.Async.Representation.runningValue_inv
#print axioms Gabbro.Grammatik.Async.Representation.waitingExpr_eval
#print axioms Gabbro.Grammatik.Async.Representation.waitingValue_inv
#print axioms Gabbro.Grammatik.Async.Representation.lowerAwaitConstruction_rep
#print axioms Gabbro.Grammatik.Async.Representation.activeChildExpr_rep
#print axioms Gabbro.Grammatik.Async.Representation.joinChildrenExpr_rep
#print axioms Gabbro.Grammatik.Async.Representation.lowerAwaitLeaf_rep
#print axioms Gabbro.Grammatik.Async.Representation.lowerLeafPoll_pending
#print axioms Gabbro.Grammatik.Async.Representation.lowerLeafPoll_ready
#print axioms Gabbro.Grammatik.Async.Representation.lowerLeafPoll_simulates
#print axioms Gabbro.Grammatik.Async.Representation.leafTaskStmt_simulates
#print axioms Gabbro.Grammatik.Async.Representation.joinActiveBlock_exec
#print axioms Gabbro.Grammatik.Async.Representation.collectJoin_exec
#print axioms Gabbro.Grammatik.Async.Representation.joinTaskStmt_simulates
#print axioms Gabbro.Grammatik.Async.Representation.PollPlan.lower_simulates
#print axioms Gabbro.Grammatik.Async.Representation.lowerAwaitPoll_simulates
#print axioms Gabbro.Grammatik.Async.Representation.waitingPhaseBlock_simulates
#print axioms Gabbro.Grammatik.Async.Representation.phaseDispatch_selects
#print axioms Gabbro.Grammatik.Async.Representation.CheckedArgument.lower_exec
#print axioms Gabbro.Grammatik.Async.Representation.CheckedArguments.lower_assign
#print axioms Gabbro.Grammatik.Async.Representation.constructLeafBlock_assign
#print axioms Gabbro.Grammatik.Async.Representation.ConstructPlan.lower_assign
#print axioms Gabbro.Grammatik.Async.Representation.beginAwaitBlock_simulates
#print axioms Gabbro.Grammatik.Async.Representation.CheckedAwait.start_simulates
#print axioms Gabbro.Grammatik.Async.Representation.CheckedAwait.poll_simulates
#print axioms Gabbro.Grammatik.Async.Segment.runActivation_agrees_with_inducedModel
#print axioms Gabbro.Grammatik.Async.Representation.CheckedFinal.block_simulates
#print axioms Gabbro.Grammatik.Async.Representation.fixedActivationInventory_erfuellbar
#print axioms Gabbro.Grammatik.Async.Representation.checkedDispatch_refines
#print axioms Gabbro.Grammatik.Async.Representation.resolvedPoll_machinePoll
#print axioms Gabbro.Grammatik.Async.Representation.checkedPoll_refines
#print axioms Gabbro.Grammatik.Async.Representation.lowerRunningBinding_rep
#print axioms Gabbro.Grammatik.Async.Representation.resolvedBindingBlock_rep
#print axioms Gabbro.Grammatik.Async.Representation.restoreFrameBlock_rep
#print axioms Gabbro.Grammatik.Async.Representation.restoredBindingBlock_rep
#print axioms Gabbro.Grammatik.Async.Representation.CheckedBinding.block_rep
#print axioms Gabbro.Grammatik.Async.Representation.frameSlot
#print axioms Gabbro.Grammatik.Async.Representation.evaluateBind_preserves
#print axioms Gabbro.Grammatik.Async.Representation.await_runTaskPoll_ready_frame
#print axioms Gabbro.Grammatik.Async.Representation.await_ready_resumes
#print axioms Gabbro.Grammatik.Async.Representation.await_runTaskPoll_ready_preserves
#print axioms Gabbro.Grammatik.Async.Representation.await_ready_preserves
#print axioms Gabbro.Grammatik.Async.Representation.runWaitingPoll_preserves
#print axioms Gabbro.Grammatik.Async.Representation.checkAwaitLocalOrigins_sound
#print axioms Gabbro.Grammatik.Async.Representation.checkAwaitInventory_sound
#print axioms Gabbro.Grammatik.Async.Representation.final_segment_encoded
#print axioms Gabbro.Grammatik.Async.Representation.finalBlock_exec
#print axioms Gabbro.Grammatik.Async.Representation.finalBlock_simulates
#print axioms Gabbro.Grammatik.Async.Representation.finalBlock_duty
#print axioms Gabbro.Grammatik.Async.Representation.Constructor.encoded
#print axioms Gabbro.Grammatik.Async.Representation.checkedDispatch_reachable_encoded
#print axioms Gabbro.Stage0.Frontend.Async.resolveExpression_literal_erfuellbar
#print axioms Gabbro.Stage0.Frontend.Async.resolveChild
#print axioms Gabbro.Grammatik.Async.Segment.checkElaboration
#print axioms Gabbro.Stage0.Frontend.Async.resolveFunction
#print axioms Gabbro.Grammatik.Async.Representation.pollFunction_refines
#print axioms Gabbro.Stage0.Frontend.Async.lowerNamedPoll
#print axioms Gabbro.Stage0.Frontend.Async.NamedPoll.call_refines
#print axioms Gabbro.Stage0.Frontend.Async.NamedPoll.linkedCall_refines
#print axioms Gabbro.Stage0.Frontend.Async.LinkedPolls.body
#print axioms Gabbro.Stage0.Frontend.Async.LinkedPolls.other
#print axioms Gabbro.Stage0.Senke.runtimeArraySliceCarrier_ok
#print axioms Gabbro.Stage0.Senke.runtimeStringSliceCarrier_ok
#print axioms Gabbro.Grammatik.Parser.Uebersetze.specRecordArgument_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specRecordArgument_lower
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.specLiteralRecord_source_erfuellbar
#print axioms Gabbro.Stage0.Frontend.Async.generatedRecordName_exact
#print axioms Gabbro.Stage0.Frontend.Async.generatedRecordName_fresh
#print axioms Gabbro.Grammatik.Async.Representation.checkedRetryStmt_cost
#print axioms Gabbro.Grammatik.Async.Representation.checkedRetryStmt_calls
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.nestedLocalArraySlice_erfuellbar
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertE_nestedLocalArraySliceIndex
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.eval_nestedLocalArraySliceIndex
