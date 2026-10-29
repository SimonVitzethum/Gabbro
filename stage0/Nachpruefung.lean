/-
  File:      stage0/Nachpruefung.lean
  Subject:   The axioms of the lowering's theorems (`Stage0/Senke/`), read by stage 7 of the Lean guardian: each must
             depend on exactly `propext`, `Classical.choice`, `Quot.sound`.
-/
import Stage0
import Stage0.Senke.Ausdruck.Tag
import Stage0.Senke.Ausdruck.Quant.Proben
import Stage0.Senke.Anweisung.Bytes.Proben
import Stage0.Senke.Anweisung.Faelle.ControlProbes

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
#print axioms Gabbro.Stage0.Senke.ByteProbe.open_refs_refused_zeuge

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
