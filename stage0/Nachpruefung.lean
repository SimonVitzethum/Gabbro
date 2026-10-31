import Stage0.Senke.Ausdruck.Gleit.Exponent
/-
  File:      stage0/Nachpruefung.lean
  Subject:   The axioms of the lowering's theorems (`Stage0/Senke/`), read by stage 7 of the Lean guardian: each must
             depend on exactly `propext`, `Classical.choice`, `Quot.sound`.
-/
import Stage0
import Stage0.Senke.Ausdruck.Tag
import Stage0.Senke.Ausdruck.Quant.Proben
import Stage0.Senke.Anweisung.Bytes.Proben
import Stage0.Senke.Anweisung.Faelle.Kontrolle.ControlProbes

#print axioms Gabbro.Stage0.Senke.bild_ok_u
#print axioms Gabbro.Stage0.Senke.bild_ok
#print axioms Gabbro.Stage0.Senke.lowFun_spec
#print axioms Gabbro.Stage0.Senke.lowS_ok
#print axioms Gabbro.Stage0.Senke.lowB_ok
#print axioms Gabbro.Stage0.Senke.lowEnd_ok
#print axioms Gabbro.Stage0.Senke.lowE_ok
#print axioms Gabbro.Stage0.Senke.wenn_ok
#print axioms Gabbro.Stage0.Senke.eng_ok
#print axioms Gabbro.Stage0.Senke.store_ok
#print axioms Gabbro.Stage0.Senke.trav_ok
#print axioms Gabbro.Stage0.Senke.weltAt_glob
#print axioms Gabbro.Stage0.Senke.weltAt_slot
#print axioms Gabbro.Stage0.Senke.layU_in
#print axioms Gabbro.Stage0.Senke.layU_dis
#print axioms Gabbro.Stage0.Senke.torC_ok
#print axioms Gabbro.Stage0.Senke.torBind_ok
#print axioms Gabbro.Stage0.Senke.chkC_ok
#print axioms Gabbro.Stage0.Senke.torOK_zeuge
#print axioms Gabbro.Stage0.Senke.torElse_ok
#print axioms Gabbro.Stage0.Senke.fehlC_ok
#print axioms Gabbro.Stage0.Senke.sonst_dec
#print axioms Gabbro.Stage0.Senke.torPuf_ok
#print axioms Gabbro.Stage0.Senke.byte_packV
#print axioms Gabbro.Stage0.Senke.bild_wurzel_ok_u
#print axioms Gabbro.Stage0.Senke.start_ok
#print axioms Gabbro.Stage0.Senke.spawnC_ok
#print axioms Gabbro.Stage0.Senke.locks_ok
#print axioms Gabbro.Stage0.Senke.nimm_paar
#print axioms Gabbro.Stage0.Senke.gib_paar
#print axioms Gabbro.Stage0.Senke.retFreiB_istZ
#print axioms Gabbro.Stage0.Senke.SyncOK.call
#print axioms Gabbro.Stage0.Senke.BildLage.sync
#print axioms Gabbro.Stage0.Senke.lk_bytes
#print axioms Gabbro.Stage0.Senke.exch_ok
#print axioms Gabbro.Stage0.Senke.awaits_ok
#print axioms Gabbro.Stage0.Senke.ex_tail
#print axioms Gabbro.Stage0.Senke.sichtOK_zeuge

#print axioms Gabbro.Stage0.Senke.onOption_ok
#print axioms Gabbro.Stage0.Senke.fnref_ok
#print axioms Gabbro.Stage0.Senke.call_ok
#print axioms Gabbro.Stage0.Senke.lowInd_ok
#print axioms Gabbro.Stage0.Senke.indStmt_ok
#print axioms Gabbro.Stage0.Senke.indBind_ok
#print axioms Gabbro.Stage0.Senke.FnptrProben.global_call_zeuge
#print axioms Gabbro.Stage0.Senke.FnptrProben.image_zeuge
#print axioms Gabbro.Stage0.Senke.FnptrProben.fnref_encoding_zeuge
#print axioms Gabbro.Stage0.Senke.FnptrProben.fnref_ok_zeuge
#print axioms Gabbro.Stage0.Senke.FnptrProben.lowInd_ok_zeuge
#print axioms Gabbro.Stage0.Senke.FnptrProben.indStmt_ok_zeuge
#print axioms Gabbro.Stage0.Senke.FnptrProben.indBind_ok_zeuge
#print axioms Gabbro.Stage0.Senke.FnptrProben.fnref_address_refused_zeuge
#print axioms Gabbro.Stage0.Senke.encSum_inj
#print axioms Gabbro.Stage0.Senke.encSum_inj_zeuge
#print axioms Gabbro.Stage0.Senke.sumWord_tag
#print axioms Gabbro.Stage0.Senke.sumWord_off
#print axioms Gabbro.Stage0.Senke.choice_ok
#print axioms Gabbro.Stage0.Senke.onTag_ok
#print axioms Gabbro.Stage0.Senke.lowTags_ok
#print axioms Gabbro.Stage0.Senke.retFreiArms_istZ
#print axioms Gabbro.Stage0.Senke.onTag_ok_zeuge
#print axioms Gabbro.Stage0.Senke.sumFits_zeuge
#print axioms Gabbro.Stage0.Senke.lowN_ok
#print axioms Gabbro.Stage0.Senke.packSum_ok

#print axioms Gabbro.Stage0.Senke.shift_ok
#print axioms Gabbro.Stage0.Senke.readBytesL_ok
#print axioms Gabbro.Stage0.Senke.putBytesL_ok
#print axioms Gabbro.Stage0.Senke.putBytes_ok
#print axioms Gabbro.Stage0.Senke.bytePartC_ok
#print axioms Gabbro.Stage0.Senke.byte_word
#print axioms Gabbro.Stage0.Senke.ByteProbe.byte_roundtrip_zeuge
#print axioms Gabbro.Stage0.Senke.ByteProbe.putBytes_ok_zeuge
#print axioms Gabbro.Stage0.Senke.ByteProbe.byte_roundtrip8_zeuge
#print axioms Gabbro.Stage0.Senke.ByteProbe.putBytes8_ok_zeuge
#print axioms Gabbro.Stage0.Senke.ByteProbe.shift_ok_zeuge
#print axioms Gabbro.Stage0.Senke.ByteProbe.putBytes_overlap_zeuge
#print axioms Gabbro.Stage0.Senke.ByteProbe.putBytes_empty_zeuge
#print axioms Gabbro.Stage0.Senke.ByteProbe.open_refs_lowered_zeuge

#print axioms Gabbro.Stage0.Senke.blockCheck_case
#print axioms Gabbro.Stage0.Senke.Ret.toSim
#print axioms Gabbro.Stage0.Senke.Ret.ofSim
#print axioms Gabbro.Stage0.Senke.narrow_ok
#print axioms Gabbro.Stage0.Senke.blockNarrow_case
#print axioms Gabbro.Stage0.Senke.endNarrow_case
#print axioms Gabbro.Stage0.Senke.blockAxiomElse_case
#print axioms Gabbro.Stage0.Senke.ControlProbe.blockCheck_case_zeuge
#print axioms Gabbro.Stage0.Senke.ControlProbe.blockNarrow_case_zeuge
#print axioms Gabbro.Stage0.Senke.ControlProbe.endNarrow_case_zeuge
#print axioms Gabbro.Stage0.Senke.ControlProbe.narrow_refused_zeuge
#print axioms Gabbro.Stage0.Senke.ControlProbe.blockAxiomElse_case_zeuge
#print axioms Gabbro.Stage0.Senke.quant_restore
#print axioms Gabbro.Stage0.Senke.quantBind_ok
#print axioms Gabbro.Stage0.Senke.quantC_ok
#print axioms Gabbro.Stage0.Senke.quantL_ok
#print axioms Gabbro.Stage0.Senke.reachEqL_ok
#print axioms Gabbro.Stage0.Senke.reachL_ok
#print axioms Gabbro.Stage0.Senke.reachesL_ok
#print axioms Gabbro.Stage0.Senke.QuantProbe.quantifiers_zeuge
#print axioms Gabbro.Stage0.Senke.QuantProbe.reaches_zeuge
#print axioms Gabbro.Stage0.Senke.QuantProbe.quant_image_zeuge
#print axioms Gabbro.Stage0.Senke.QuantProbe.quant_refused_zeuge
#print axioms Gabbro.Stage0.Senke.QuantProbe.reaches_refused_zeuge

#print axioms Gabbro.Stage0.Senke.retryTest_ok
#print axioms Gabbro.Stage0.Senke.retryC_ok
#print axioms Gabbro.Stage0.Senke.retry_case
#print axioms Gabbro.Stage0.Senke.forever_zero
#print axioms Gabbro.Stage0.Senke.forever_one_false
#print axioms Gabbro.Stage0.Senke.forever_refused
#print axioms Gabbro.Stage0.Senke.RetryProbe.retry_case_zeuge
#print axioms Gabbro.Stage0.Senke.LoopProbe.retry_overflow_zeuge
#print axioms Gabbro.Stage0.Senke.LoopProbe.forever_fuel_zeuge
#print axioms Gabbro.Stage0.Senke.LoopProbe.forever_body_zeuge
#print axioms Gabbro.Stage0.Senke.LoopProbe.forever_refused_zeuge
#print axioms Gabbro.Stage0.Senke.boolC_ok
#print axioms Gabbro.Stage0.Senke.einpassen_bool
#print axioms Gabbro.Stage0.Senke.einpassen_never
#print axioms Gabbro.Stage0.Senke.GateProbe.boolean_images_zeuge
#print axioms Gabbro.Stage0.Senke.GateProbe.never_images_zeuge
#print axioms Gabbro.Stage0.Senke.GateProbe.never_outcome_zeuge
#print axioms Gabbro.Stage0.Senke.GateProbe.boolean_decode_zeuge
#print axioms Gabbro.Stage0.Senke.GateProbe.start_frontend_zeuge
#print axioms Gabbro.Stage0.Senke.GateProbe.start_image_zeuge
#print axioms Gabbro.Stage0.Senke.GateProbe.unsupported_answers_zeuge
#print axioms Gabbro.Stage0.Senke.whyTest_ok
#print axioms Gabbro.Stage0.Senke.lowGrund_ok
#print axioms Gabbro.Stage0.Senke.onWhy_ok
#print axioms Gabbro.Stage0.Senke.onWhy_ok_zeuge
#print axioms Gabbro.Stage0.Senke.retWhy_ok
#print axioms Gabbro.Stage0.Senke.RetWhy.prefix
#print axioms Gabbro.Stage0.Senke.callBranch_ok
#print axioms Gabbro.Stage0.Senke.callElse_ok
#print axioms Gabbro.Stage0.Senke.callElse_jump
#print axioms Gabbro.Stage0.Senke.blockCallElse_case
#print axioms Gabbro.Stage0.Senke.endCallElse_case
#print axioms Gabbro.Stage0.Senke.endLeave_case
#print axioms Gabbro.Stage0.Senke.endNext_case
#print axioms Gabbro.Stage0.Senke.WhyProbe.outcomes_zeuge
#print axioms Gabbro.Stage0.Senke.WhyProbe.callElse_ok_zeuge
#print axioms Gabbro.Stage0.Senke.arrNil_ok
#print axioms Gabbro.Stage0.Senke.arrCons_ok
#print axioms Gabbro.Stage0.Senke.arrGet_ok
#print axioms Gabbro.Stage0.Senke.arrSet_ok
#print axioms Gabbro.Stage0.Senke.strLit_ok
#print axioms Gabbro.Stage0.Senke.strLen_ok
#print axioms Gabbro.Stage0.Senke.strCat_ok
#print axioms Gabbro.Stage0.Senke.strGet_ok
#print axioms Gabbro.Stage0.Senke.strCompare_ok
#print axioms Gabbro.Stage0.Senke.strWeit_ok
#print axioms Gabbro.Stage0.Senke.AggregateProbe.semantics_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.lowering_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.simulation_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.refused_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.representation_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.image_zeuge
#print axioms Gabbro.Stage0.Senke.AggregateProbe.read_refused_zeuge

#print axioms Gabbro.Stage0.Senke.enc_ref_cell
#print axioms Gabbro.Stage0.Senke.slotRefA_ok
#print axioms Gabbro.Stage0.Senke.slotRefC_ok
#print axioms Gabbro.Stage0.Senke.refEq_ok
#print axioms Gabbro.Stage0.Senke.assignSlotRef_case
#print axioms Gabbro.Stage0.Senke.ReferenceProbe.region_zeuge
#print axioms Gabbro.Stage0.Senke.ReferenceProbe.encoded_zeuge
#print axioms Gabbro.Stage0.Senke.ReferenceProbe.lowering_zeuge
#print axioms Gabbro.Stage0.Senke.ReferenceProbe.read_simulation_zeuge
#print axioms Gabbro.Stage0.Senke.ReferenceProbe.write_simulation_zeuge
#print axioms Gabbro.Stage0.Senke.ReferenceProbe.refused_zeuge
#print axioms Gabbro.Stage0.Senke.wordL_ok
#print axioms Gabbro.Stage0.Senke.float_word_injective
#print axioms Gabbro.Stage0.Senke.float_lt_key
#print axioms Gabbro.Stage0.Senke.float_lt_key_not_nan
#print axioms Gabbro.Stage0.Senke.float_key_word
#print axioms Gabbro.Stage0.Senke.floatKeyL_ok
#print axioms Gabbro.Stage0.Senke.floatExprE_ok
#print axioms Gabbro.Stage0.Senke.floatRangeL_ok
#print axioms Gabbro.Stage0.Senke.bindValue_ok
#print axioms Gabbro.Stage0.Senke.blockFloatLit_case
#print axioms Gabbro.Stage0.Senke.blockFloatNarrow_case
#print axioms Gabbro.Stage0.Senke.FloatProbe.float_lowering_zeuge
#print axioms Gabbro.Stage0.Senke.FloatProbe.float_signed_zero_zeuge
#print axioms Gabbro.Stage0.Senke.FloatProbe.float_refused_zeuge
#print axioms Gabbro.Stage0.Senke.floatRoundUp_model
#print axioms Gabbro.Stage0.Senke.floatRoundWord_model
#print axioms Gabbro.Stage0.Senke.floatRoundWord_model_zeuge
#print axioms Gabbro.Stage0.Senke.floatRoundL_ok
#print axioms Gabbro.Stage0.Senke.floatMagnitudeWord_model
#print axioms Gabbro.Stage0.Senke.floatMagnitudeL_ok
#print axioms Gabbro.Stage0.Senke.floatMagnitudeWord_model_zeuge
#print axioms Gabbro.Stage0.Senke.floatMagnitudeL_ok_zeuge
#print axioms Gabbro.Stage0.Senke.floatShiftQuotWord_model
#print axioms Gabbro.Stage0.Senke.floatShiftBackWord_model
#print axioms Gabbro.Stage0.Senke.floatShiftJamWord_model
#print axioms Gabbro.Stage0.Senke.floatShiftQuotL_ok
#print axioms Gabbro.Stage0.Senke.floatShiftJamL_ok
#print axioms Gabbro.Stage0.Senke.floatShiftJamWord_model_zeuge
#print axioms Gabbro.Stage0.Senke.floatShiftQuotL_ok_zeuge
#print axioms Gabbro.Stage0.Senke.floatShiftJamL_ok_zeuge
#print axioms Gabbro.Stage0.Senke.floatShiftBackWord_toNat
#print axioms Gabbro.Stage0.Senke.floatShiftRemainderWord_model
#print axioms Gabbro.Stage0.Senke.floatRoundShiftL_ok
#print axioms Gabbro.Stage0.Senke.floatNormQ_shift
#print axioms Gabbro.Stage0.Senke.floatRoundShiftL_normQ
#print axioms Gabbro.Stage0.Senke.floatRoundShiftL_ok_zeuge
#print axioms Gabbro.Stage0.Senke.floatRoundShiftL_normQ_zeuge
#print axioms Gabbro.Stage0.Senke.blockFloatOfLit_case
#print axioms Gabbro.Stage0.Senke.FloatArithmeticProbe.float_arithmetic_images_zeuge
#print axioms Gabbro.Stage0.Senke.FloatArithmeticProbe.float_add_sub_model_zeuge
#print axioms Gabbro.Stage0.Senke.FloatArithmeticProbe.float_operations_refused_zeuge

#print axioms Gabbro.Stage0.Senke.lowEns_ok
#print axioms Gabbro.Stage0.Senke.snapC_ok
#print axioms Gabbro.Stage0.Senke.OldProbe.lowEns_ok_zeuge
#print axioms Gabbro.Stage0.Senke.OldProbe.snapC_ok_zeuge
#print axioms Gabbro.Stage0.Senke.counter_init
#print axioms Gabbro.Stage0.Senke.counter_zero
#print axioms Gabbro.Stage0.Senke.counter_positive
#print axioms Gabbro.Stage0.Senke.counter_decrement
#print axioms Gabbro.Stage0.Senke.counter_protected
#print axioms Gabbro.Stage0.Senke.counter_decrement_zeuge

#print axioms Gabbro.Stage0.Senke.floatNormQ_left

#print axioms Gabbro.Stage0.Senke.findeExp_integer_nonzero
#print axioms Gabbro.Stage0.Senke.floatExponentWord_canonical
#print axioms Gabbro.Stage0.Senke.floatExponentL_canonical
#print axioms Gabbro.Stage0.Senke.floatExponentL_canonical_zeuge
#print axioms Gabbro.Stage0.Senke.normalize_integer_zero
#print axioms Gabbro.Stage0.Senke.normalize_integer_zero_zeuge

#print axioms Gabbro.Stage0.Senke.floatRangeReject_none
#print axioms Gabbro.Stage0.Senke.floatRangeReject_accept
#print axioms Gabbro.Stage0.Senke.floatRangeReject_zeuge
#print axioms Gabbro.Stage0.Senke.FloatArithmeticProbe.computedSamples_bits

#print axioms Gabbro.Stage0.Senke.canonicalFloatRangeL_nan
#print axioms Gabbro.Stage0.Senke.FloatArithmeticProbe.computed_range_decisions_zeuge
#print axioms Gabbro.Stage0.Senke.canonicalFloatRangeL_nan_ok
#print axioms Gabbro.Stage0.Senke.floatKeyL_ok
#print axioms Gabbro.Stage0.Senke.floatRangeL_raw_ok
#print axioms Gabbro.Stage0.Senke.canonicalFloatRangeL_ok
#print axioms Gabbro.Stage0.Senke.canonicalFloatRangeL_ok_zeuge

#print axioms Gabbro.Stage0.Senke.blockFloatOfComputed_case

#print axioms Gabbro.Stage0.Senke.floatNegL_model
#print axioms Gabbro.Stage0.Senke.floatFieldWord_canonical
#print axioms Gabbro.Stage0.Senke.floatFieldL_ok
#print axioms Gabbro.Stage0.Senke.AddSubProbe.floatFieldL_joint_zeuge

#print axioms Gabbro.Stage0.Senke.floatCoefficientWord_canonical
#print axioms Gabbro.Stage0.Senke.floatCoefficient_exact
#print axioms Gabbro.Stage0.Senke.floatCoefficientL_ok
#print axioms Gabbro.Stage0.Senke.floatCoefficientL_shape
#print axioms Gabbro.Stage0.Senke.AddSubProbe.floatCoefficientL_joint_zeuge
#print axioms Gabbro.Stage0.Senke.AddSubProbe.coefficientImages_zeuge

#print axioms Gabbro.Stage0.Senke.floatAlignSumWord_model

#print axioms Gabbro.Stage0.Senke.floatAlignSumWord_round

#print axioms Gabbro.Stage0.Senke.floatAlignSumL_ok

#print axioms Gabbro.Stage0.Senke.floatCoefficientAlignSumL_ok

#print axioms Gabbro.Stage0.Senke.floatAlignSumL_shape

#print axioms Gabbro.Stage0.Senke.AddSubProbe.floatAlignSumL_joint_zeuge

#print axioms Gabbro.Stage0.Senke.AddSubProbe.alignmentImages_zeuge

#print axioms Gabbro.Stage0.Senke.floatCoefficientAlignSumWord_add
#print axioms Gabbro.Stage0.Senke.floatCoefficientAlignSumWord_add_zeuge

#print axioms Gabbro.Stage0.Senke.floatGuardSticky_round
#print axioms Gabbro.Stage0.Senke.floatGuardSticky_round_zeuge
#print axioms Gabbro.Stage0.Senke.floatGuardRoundL_ok
#print axioms Gabbro.Stage0.Senke.AddSubProbe.floatGuardRoundL_joint_zeuge
#print axioms Gabbro.Stage0.Senke.AddSubProbe.guardImages_zeuge

#print axioms Gabbro.Stage0.Senke.floatGuardSticky_div
#print axioms Gabbro.Stage0.Senke.floatNegativeAlign_div
#print axioms Gabbro.Stage0.Senke.floatSignedAlign_reconstruct
#print axioms Gabbro.Stage0.Senke.floatNegativeQuotL_ok
#print axioms Gabbro.Stage0.Senke.AddSubProbe.floatNegativeQuotL_joint_zeuge
#print axioms Gabbro.Stage0.Senke.AddSubProbe.negativeQuotImages_zeuge

#print axioms Gabbro.Stage0.Senke.floatShiftTailL_ok
#print axioms Gabbro.Stage0.Senke.floatNegativeShiftL_ok
#print axioms Gabbro.Stage0.Senke.AddSubProbe.floatNegativeShiftL_joint_zeuge
#print axioms Gabbro.Stage0.Senke.AddSubProbe.negativeShiftImages_zeuge
