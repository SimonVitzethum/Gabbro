/-
  The cheap check: the goal theorem alone, without the translation-validation chain files.
  Run:  lake build Grammatik.Zielsatz.BeweisAtomar && lake env lean NachpruefungZiel.lean
-/
import Grammatik.Zielsatz.Beweis
import Grammatik.Zielsatz.Proben
import Grammatik.Zielsatz.ProbenW1
import Grammatik.Zielsatz.BeweisAtomar

open Gabbro.Grammatik

#check @Gabbro.Grammatik.Zielsatz.GabbroZiel
#check @Gabbro.Grammatik.Zielsatz.gabbro_ziel
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_sc
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_sc_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund_sc_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_zeuge
#print axioms Gabbro.Grammatik.Zielsatz.probeA_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeD_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.w1_abgelehnt
