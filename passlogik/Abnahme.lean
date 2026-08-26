/-
  Datei:      Abnahme.lean
  Gegenstand: Die ABNAHME -- die Axiomliste des README, GEMESSEN statt gepflegt.

  `#print axioms X` nennt jedes Axiom, an dem `X` haengt. Erwartet wird ueberall
  entweder "does not depend on any axioms" oder die drei Standardaxiome von Lean
  (`propext`, `Classical.choice`, `Quot.sound`) -- **und niemals `sorryAx`.**

      lake build Abnahme 2>&1 | grep -c sorryAx      # muss 0 sein
      lake build Abnahme                             # die Ausgabe IST die Axiomliste

  *Taucht `sorryAx` auf, ist ein Beweis nicht gefuehrt. Das ist die Sprechprobe in die
  andere Richtung: dieser Befehl kann rot werden.*

  **Diese Datei ist ERZEUGT** aus den `theorem`-Koepfen unter `Passlogik/`. Sie zaehlt
  ALLE Saetze, nicht nur die Hauptsaetze -- die Hauptsaetze tragen ihr `#print axioms`
  ausserdem an Ort und Stelle, direkt unter dem Beweis.
-/
import Passlogik


/-! ## Bereich -- 46 Saetze -/

#print axioms Passlogik.Bereich.imin_le_left
#print axioms Passlogik.Bereich.imin_le_right
#print axioms Passlogik.Bereich.le_imax_left
#print axioms Passlogik.Bereich.le_imax_right
#print axioms Passlogik.Bereich.le_imin
#print axioms Passlogik.Bereich.imax_le
#print axioms Passlogik.Bereich.Iv.leer_haelt_nichts
#print axioms Passlogik.Bereich.Iv.kleiner_refl
#print axioms Passlogik.Bereich.Iv.kleiner_trans
#print axioms Passlogik.Bereich.Iv.kleiner_syntaktisch
#print axioms Passlogik.Bereich.add_korrekt
#print axioms Passlogik.Bereich.neg_korrekt
#print axioms Passlogik.Bereich.sub_korrekt
#print axioms Passlogik.Bereich.mul_korrekt
#print axioms Passlogik.Bereich.schnitt_genau
#print axioms Passlogik.Bereich.huelle_deckt_links
#print axioms Passlogik.Bereich.huelle_deckt_rechts
#print axioms Passlogik.Bereich.add_monoton
#print axioms Passlogik.Bereich.sub_monoton
#print axioms Passlogik.Bereich.schnitt_ist_infimum
#print axioms Passlogik.Bereich.schnitt_monoton
#print axioms Passlogik.Bereich.echt_enger_faellt
#print axioms Passlogik.Bereich.keine_unendliche_verengung
#print axioms Passlogik.Bereich.passt_dann_kein_ueberlauf
#print axioms Passlogik.Bereich.summe_passt_dann_kein_ueberlauf
#print axioms Passlogik.Bereich.produkt_passt_dann_kein_ueberlauf
#print axioms Passlogik.Bereich.nenner_ok_dann_nicht_null
#print axioms Passlogik.Bereich.v1_ja
#print axioms Passlogik.Bereich.v1_nein
#print axioms Passlogik.Bereich.v1_zweige_decken_ab
#print axioms Passlogik.Bereich.v1_verengt
#print axioms Passlogik.Bereich.v1_traegt_nur_stabil
#print axioms Passlogik.Bereich.trichotomie_ueber_int
#print axioms Passlogik.Bereich.trichotomie_bricht
#print axioms Passlogik.Bereich.vier_ausgaenge
#print axioms Passlogik.Bereich.v2_ge
#print axioms Passlogik.Bereich.v2_gt
#print axioms Passlogik.Bereich.v2_kauft_etwas
#print axioms Passlogik.Bereich.v2_woertlich_ist_nicht_immer_enger
#print axioms Passlogik.Bereich.sub_v2_korrekt
#print axioms Passlogik.Bereich.sub_v2_nie_schlechter
#print axioms Passlogik.Bereich.sub_v2_kauft_etwas
#print axioms Passlogik.Bereich.v3_verengt
#print axioms Passlogik.Bereich.v3_braucht_erschoepfung
#print axioms Passlogik.Bereich.fakten_ueberleben_schreiben
#print axioms Passlogik.Bereich.leere_fakten_immer_gueltig

/-! ## Kosten -- 22 Saetze -/

#print axioms Passlogik.Kosten.le_max_links
#print axioms Passlogik.Kosten.le_max_rechts
#print axioms Passlogik.Kosten.wdh_schritt
#print axioms Passlogik.Kosten.deckt_A
#print axioms Passlogik.Kosten.deckt_S
#print axioms Passlogik.Kosten.deckt_K
#print axioms Passlogik.Kosten.deckt_Z
#print axioms Passlogik.Kosten.deckt_W
#print axioms Passlogik.Kosten.L1_obere_schranke
#print axioms Passlogik.Kosten.rekursion_bricht_die_praemisse
#print axioms Passlogik.Kosten.gliederwert_null
#print axioms Passlogik.Kosten.gliederwert_nichtnegativ
#print axioms Passlogik.Kosten.L2_kleinste_belegung
#print axioms Passlogik.Kosten.ohne_K005_faellt_L2
#print axioms Passlogik.Kosten.alt_rechnet_zwei
#print axioms Passlogik.Kosten.neu_rechnet_sechs
#print axioms Passlogik.Kosten.durchlauf_kostet_sechs
#print axioms Passlogik.Kosten.alte_regel_zaehlt_zu_wenig
#print axioms Passlogik.Kosten.held_bindet_darunter
#print axioms Passlogik.Kosten.wartezeit_ist_summe
#print axioms Passlogik.Kosten.schleife_multipliziert
#print axioms Passlogik.Kosten.produkt_waechst_monoton

/-! ## Linear -- 10 Saetze -/

#print axioms Passlogik.Linear.pfad_zaehlt_genau
#print axioms Passlogik.Linear.genau_einmal
#print axioms Passlogik.Linear.linear_dann_affin
#print axioms Passlogik.Linear.affin_sieht_das_leck_nicht
#print axioms Passlogik.Linear.unabgeglichen_faellt
#print axioms Passlogik.Linear.ohne_abgleich_leck
#print axioms Passlogik.Linear.schleife_verbraucht_faellt
#print axioms Passlogik.Linear.zwei_durchgaenge_verbrauchen_zweimal
#print axioms Passlogik.Linear.basisname_verwischt
#print axioms Passlogik.Linear.leaves_ist_kein_verbrauch

/-! ## Phasen -- 11 Saetze -/

#print axioms Passlogik.Phasen.fluss_geht_vorwaerts
#print axioms Passlogik.Phasen.ein_schritt_kommt_voran
#print axioms Passlogik.Phasen.zusagen_komponieren
#print axioms Passlogik.Phasen.zweige_treffen_sich
#print axioms Passlogik.Phasen.ohne_o006_zwei_stufen
#print axioms Passlogik.Phasen.kette_ist_endlich
#print axioms Passlogik.Phasen.hoechstens_so_viele_schritte
#print axioms Passlogik.Phasen.schritt_stufen_verschieden
#print axioms Passlogik.Phasen.tut_nur_von_der_ausgangsstufe
#print axioms Passlogik.Phasen.kein_zweiter_durchgang
#print axioms Passlogik.Phasen.ordnung_ist_nicht_umsonst

/-! ## Rang -- 13 Saetze -/

#print axioms Passlogik.Rang.kette_wartet
#print axioms Passlogik.Rang.kette_endet_wartend
#print axioms Passlogik.Rang.rang_steigt
#print axioms Passlogik.Rang.keine_verklemmung
#print axioms Passlogik.Rang.kein_selbstwarten
#print axioms Passlogik.Rang.kreuz_erfuellt_lasch
#print axioms Passlogik.Rang.lasch_laesst_verklemmung_zu
#print axioms Passlogik.Rang.null_rueckfall_verwischt
#print axioms Passlogik.Rang.keine_verklemmung_partiell
#print axioms Passlogik.Rang.undeklarierte_sperren_bleiben_draussen
#print axioms Passlogik.Rang.rangregel_ist_nicht_notwendig
#print axioms Passlogik.Rang.kette_ohne_wiederholung
#print axioms Passlogik.Rang.rangSteigend_schwanz

/-! ## Terminierung -- 14 Saetze -/

#print axioms Passlogik.Terminierung.kein_unendlicher_abstieg
#print axioms Passlogik.Terminierung.schleife_endet
#print axioms Passlogik.Terminierung.zaehle_gleich
#print axioms Passlogik.Terminierung.zaehle_ein_mehr
#print axioms Passlogik.Terminierung.unvisited_endet
#print axioms Passlogik.Terminierung.decreasing_endet
#print axioms Passlogik.Terminierung.s005_ist_nicht_hinreichend
#print axioms Passlogik.Terminierung.consuming_endet
#print axioms Passlogik.Terminierung.s008_ist_nicht_hinreichend
#print axioms Passlogik.Terminierung.retry_endet
#print axioms Passlogik.Terminierung.retry_ohne_kosten_endet_nicht
#print axioms Passlogik.Terminierung.forever_laeuft_ewig
#print axioms Passlogik.Terminierung.programm_endet_unter_massen
#print axioms Passlogik.Terminierung.forever_traegt_kein_mass

/-! ## Wirkung -- 21 Saetze -/

#print axioms Passlogik.Wirkung.teilmenge_refl
#print axioms Passlogik.Wirkung.teilmenge_trans
#print axioms Passlogik.Wirkung.leere_ist_kleinste
#print axioms Passlogik.Wirkung.pure_ist_leer
#print axioms Passlogik.Wirkung.erreicht_trans
#print axioms Passlogik.Wirkung.dekl_monoton
#print axioms Passlogik.Wirkung.huelle_deckt
#print axioms Passlogik.Wirkung.wechselseitig_hat_zyklus
#print axioms Passlogik.Wirkung.wechselseitig_rahmen
#print axioms Passlogik.Wirkung.wechselseitig_kante
#print axioms Passlogik.Wirkung.zyklus_stoert_nicht
#print axioms Passlogik.Wirkung.erreicht_monoton
#print axioms Passlogik.Wirkung.sem_monoton
#print axioms Passlogik.Wirkung.absage_haelt_unter_unvollstaendigkeit
#print axioms Passlogik.Wirkung.vollstaendigkeit_geht_verloren
#print axioms Passlogik.Wirkung.alte_pruefung_laesst_durch
#print axioms Passlogik.Wirkung.huelle_deckt_mit_fremden
#print axioms Passlogik.Wirkung.fail_open_bricht_den_satz
#print axioms Passlogik.Wirkung.teilmenge_dann_grob
#print axioms Passlogik.Wirkung.grob_deckt_mehr
#print axioms Passlogik.Wirkung.huelle_deckt_grob
