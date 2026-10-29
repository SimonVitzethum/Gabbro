/-
  File:      stage0/Nachpruefung.lean
  Subject:   The axioms of the lowering's theorems (`Stage0/Senke/`), read by stage 7 of the Lean guardian: each must
             depend on exactly `propext`, `Classical.choice`, `Quot.sound`.
-/
import Stage0

#print axioms Gabbro.Stage0.Senke.bild_ok_u
#print axioms Gabbro.Stage0.Senke.bild_ok
#print axioms Gabbro.Stage0.Senke.lowFun_spec
#print axioms Gabbro.Stage0.Senke.lowS_ok
#print axioms Gabbro.Stage0.Senke.lowB_ok
#print axioms Gabbro.Stage0.Senke.lowEnd_ok
#print axioms Gabbro.Stage0.Senke.lowE_ok
#print axioms Gabbro.Stage0.Senke.wenn_ok
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
