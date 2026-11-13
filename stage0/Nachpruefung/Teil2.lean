module

public import Grammatik.Zielsatz.Atomar.BeweisAtomar
public import Stage0
public import Stage0.Senke.Ausdruck.Tag
public import Stage0.Senke.Ausdruck.Quant.Proben
public import Stage0.Senke.Anweisung.Bytes.Proben
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.ControlProbes
public import Stage0.Bindung.Proben

@[expose] public section


#print axioms Gabbro.Grammatik.Parser.ExportPreservation.member_meaning
#print axioms Gabbro.Grammatik.Parser.ExportPreservation.member_footprint
#print axioms Gabbro.Grammatik.Parser.ExportPreservation.strings_gate
#print axioms Gabbro.Stage0.Compiled.initializer_exports
#print axioms Gabbro.Stage0.exported_batch2_ir_correct_zeuge
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
#print axioms Gabbro.Stage0.Senke.blockFloatArithmetic_case

-- All ending float binders use the same generic lowering and exact-outcome witnesses.
#print axioms Gabbro.Stage0.Senke.endFloatLit_case
#print axioms Gabbro.Stage0.Senke.endFloatOfLit_case
#print axioms Gabbro.Stage0.Senke.endFloatOfComputed_case
#print axioms Gabbro.Stage0.Senke.endFloatArithmetic_case
#print axioms Gabbro.Stage0.Senke.endFloatNarrow_case

-- Binary64 arithmetic uses the native runner operations and the shared binder.
#print axioms Gabbro.Stage0.Senke.floatArithmeticBlockL_eq

-- Binary64 division: native arithmetic and connected source witnesses.

-- C14 Stage-0 image placement and profile certificate transport.
#print axioms Gabbro.Stage0.Senke.layU_ga_lcm_dvd
#print axioms Gabbro.Stage0.Emitted.placed
#print axioms Gabbro.Stage0.Compiled.profile_binding
#print axioms Gabbro.Stage0.AlignedStaticWitness.addr_aligned
#print axioms Gabbro.Stage0.ProfileMismatchWitness.candidate_refused
#print axioms Gabbro.Stage0.SectionWitness.candidate_refused

-- C01 products: actual emitters, generic simulation and jointly inhabited value flow.
#print axioms Gabbro.Stage0.Senke.prodArgs_ok
#print axioms Gabbro.Stage0.Senke.prod_ok
#print axioms Gabbro.Stage0.Senke.prodGet_ok
#print axioms Gabbro.Stage0.Senke.prodSet_ok
#print axioms Gabbro.Stage0.Senke.wordsAt_prodSet
#print axioms Gabbro.Stage0.Senke.AggregateProbe.Product.prod_ok_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.Product.prodGet_ok_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.Product.prodSet_ok_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.Product.prod_empty_zeuge
#print axioms Gabbro.Stage0.Pipeline.ProductValueWitness.semantics_zeuge
#print axioms Gabbro.Stage0.Pipeline.ProductValueWitness.encoding_zeuge
#print axioms Gabbro.Stage0.Pipeline.ProductValueWitness.wide_encoding_zeuge
#print axioms Gabbro.Stage0.Pipeline.ProductValueWitness.wide_lowering_zeuge
#print axioms Gabbro.Stage0.Pipeline.ProductValueWitness.simulation_zeuge
#print axioms Gabbro.Stage0.Pipeline.ProductValueWitness.block_lowering_zeuge
#print axioms Gabbro.Stage0.Pipeline.ProductValueWitness.image_zeuge
#print axioms Gabbro.Stage0.exported_records_ir_correct
#print axioms Gabbro.Stage0.Pipeline.ProductRecordWitness.exported_records_ir_correct_zeuge
#print axioms Gabbro.Stage0.Senke.bytesLt_keys
#print axioms Gabbro.Stage0.Senke.keyScan_lex
#print axioms Gabbro.Stage0.Senke.stringScan_value
#print axioms Gabbro.Stage0.Senke.stringAppend_ok
#print axioms Gabbro.Stage0.Senke.stringCatC_ok
#print axioms Gabbro.Stage0.Senke.strCatExpr_ok
#print axioms Gabbro.Stage0.Senke.strLtExpr_ok
#print axioms Gabbro.Stage0.Senke.StringSpanProbe.concatenation_correct
#print axioms Gabbro.Stage0.Senke.StringSpanProbe.order_correct

-- Native CPU arithmetic and complete-word storage, without a software FP fallback.
#print axioms Gabbro.Stage0.Senke.nativeFloat_read_word
#print axioms Gabbro.Stage0.Senke.nativeFloat_word_eq
#print axioms Gabbro.Stage0.Senke.nativeFloat_word_eq_nonNaN
#print axioms Gabbro.Stage0.Senke.nativeFP_bin_ok
#print axioms Gabbro.Stage0.Senke.nativeFPWordL_ok
#print axioms Gabbro.Stage0.Senke.nativeArithmetic_eval
#print axioms Gabbro.Stage0.Senke.floatWordsL_ok
#print axioms Gabbro.Stage0.Senke.nativeFloatRangeL_at_ok
#print axioms Gabbro.Stage0.Senke.nativeFloatRangeL_ok
#print axioms Gabbro.Stage0.Senke.floatRetainedRangeL_ok
#print axioms Gabbro.Stage0.Senke.nativeFloatBind_ok
#print axioms Gabbro.Stage0.Senke.nativeIntegerFloatL_ok
#print axioms Gabbro.Stage0.Senke.nativeIntegerFloatL_source_ok
#print axioms Gabbro.Stage0.Senke.nativeFloatMulL_ok
#print axioms Gabbro.Stage0.Senke.nativeFloatScaleL_ok
#print axioms Gabbro.Stage0.Senke.computedFloatOfE_ok
#print axioms RootNativeFloat.bits_roundtrip
#print axioms RootNativeFloat.finite_word_mask
#print axioms RootNativeFloat.ofInt_jam56
#print axioms RootNativeFloat.neg_bits64
#print axioms RootNativeFloat.neg_bits32
#print axioms RootNativeFloat.canonLiteral_integer
#print axioms Gabbro.Grammatik.bruch_integer
