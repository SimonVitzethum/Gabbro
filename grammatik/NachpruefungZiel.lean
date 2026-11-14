/-
  The cheap check: the goal theorem alone.
  Run:  lake build Grammatik.Zielsatz.BeweisAtomar && lake env lean NachpruefungZiel.lean
-/
module
public import Grammatik.Zielsatz.Kern.Beweis
public import Grammatik.Zielsatz.Kern.Proben
public import Grammatik.Zielsatz.Kern.ProbenW1
public import Grammatik.Zielsatz.Atomar.BeweisAtomar
public import Grammatik.Zielsatz.Atomar.BeweisTerminierung
public import Grammatik.Zielsatz.Atomar.TerminierungZeuge
public import Grammatik.Zielsatz.Atomar.BeweisWarten
@[expose] public section


open Gabbro.Grammatik

#check @Gabbro.Grammatik.Zielsatz.GabbroZiel
#check @Gabbro.Grammatik.Zielsatz.gabbro_ziel
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
#check @Gabbro.Grammatik.Zielsatz.GabbroZielVoll
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_voll
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_sc
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_sc_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_leben
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_terminierung
#print axioms Gabbro.Grammatik.Zielsatz.terminierung_zeuge
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_warten
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund_sc_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_zeuge
#print axioms Gabbro.Grammatik.Zielsatz.probeA_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.probeD_widerlegt_gilt
#print axioms Gabbro.Grammatik.Zielsatz.w1_abgelehnt
