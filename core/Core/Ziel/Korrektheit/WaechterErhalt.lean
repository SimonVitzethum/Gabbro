/-
  File:      core/Core/Ziel/Korrektheit/WaechterErhalt.lean
  Subject:   PRESERVATION of the joined environments across every instruction: the master
             transfer lemma over the whole instruction set.

  Every case is one application of a generic lemma of `WaechterSchritt.lean`: static writes
  use their value lemma, unknown writes use poison, frame-only steps rewrite, calls use the
  call lemma and returns restore a saved frame. Access and lifecycle instructions are
  excluded by hypothesis (the checker refuses them).
-/
module

public import Core.Ziel.Korrektheit.WaechterWert

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse

open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast


/-- Preservation of the joined environments across one instruction step. -/
theorem auswerten_erfuellt (code : List Befehl) (frame : Rahmen) (live : Nat → Bool)
    (b : Befehl) (hmem : b ∈ code) (hfre : code.all keinFremdzugriff = true)
    (h : RahmenErfuellt code frame) :
    RahmenErfuellt code (b.auswerten frame live) := by
  have hrein : ∀ x ∈ code, keinFremdzugriff x = true := List.all_eq_true.mp hfre
  cases b with
  | literal dst val =>
    have hpoisT : beitragText (Befehl.literal dst val) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hV : ∀ g : Ganzzahl,
        (((Befehl.literal dst val).auswerten frame live).temp dst).bind alsGanzzahl = some g →
        ∀ L H : Int, umgebungInt code dst = some (L, H) → L ≤ g.zahl.wert ∧ g.zahl.wert ≤ H := by
      intro g hg L H hlook
      have htemp : ((Befehl.literal dst val).auswerten frame live).temp dst =
          some ⟨.int (val : Int) (val : Int), Zahl.literal (val : Int)⟩ := by
        simp only [Befehl.auswerten, Rahmen.schreibe, Function.update_self]
      rw [htemp] at hg
      exact literal_wertSat code dst val hmem g hg L H hlook
    exact transfer_schreibe_statischInt code frame live _ _ hmem h _ rfl hV hpoisT
  | binaer op links =>
    have hpoisI : beitragInt (Befehl.binaer op links) links = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.binaer op links) links = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | binden name quelle =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | wahrheitswert dst val =>
    have hpoisI : beitragInt (Befehl.wahrheitswert dst val) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.wahrheitswert dst val) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | lesen dst index =>
    have hpoisI : beitragInt (Befehl.lesen dst index) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.lesen dst index) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | negativ dst betrag =>
    have hpoisT : beitragText (Befehl.negativ dst betrag) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hV : ∀ g : Ganzzahl,
        (((Befehl.negativ dst betrag).auswerten frame live).temp dst).bind alsGanzzahl = some g →
        ∀ L H : Int, umgebungInt code dst = some (L, H) → L ≤ g.zahl.wert ∧ g.zahl.wert ≤ H := by
      intro g hg L H hlook
      have htemp : ((Befehl.negativ dst betrag).auswerten frame live).temp dst =
          some ⟨.int (-(betrag : Int)) (-(betrag : Int)), Zahl.literal (-(betrag : Int))⟩ := by
        simp only [Befehl.auswerten, Rahmen.schreibe, Function.update_self]
      rw [htemp] at hg
      exact negativ_wertSat code dst betrag hmem g hg L H hlook
    exact transfer_schreibe_statischInt code frame live _ _ hmem h _ rfl hV hpoisT
  | negieren dst =>
    have hpoisI : beitragInt (Befehl.negieren dst) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.negieren dst) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | verneinen dst =>
    have hpoisI : beitragInt (Befehl.verneinen dst) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.verneinen dst) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | teilen links =>
    have hpoisI : beitragInt (Befehl.teilen links) links = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.teilen links) links = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | vergleichen op links =>
    have hpoisI : beitragInt (Befehl.vergleichen op links) links = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.vergleichen op links) links = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | springeWenn src bei abstand =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | zuweisen src index zieltyp =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | zurueck quelle zieltyp =>
    exact Rahmen.rueckkehr_erfuellt code frame _ h
  | springe abstand =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | blockEnde freigabe =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | bindeWert quelle ziel global =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | definiere name parameter result globale ueberspringe misstAbstieg ruft effects =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | rufe name args bind =>
    exact Rahmen.ruf_erfuellt code frame name args bind h
  | rueckVoid =>
    exact Rahmen.rueckkehr_erfuellt code frame _ h
  | pruefeMass quelle =>
    have htemp : ((Befehl.pruefeMass quelle).auswerten frame live).temp = frame.temp := by
      simp only [Befehl.auswerten, Rahmen.setzeMass]
      repeat' first | rfl | split
    have hfort : ((Befehl.pruefeMass quelle).auswerten frame live).fortsetzungen =
        frame.fortsetzungen := by
      simp only [Befehl.auswerten, Rahmen.setzeMass]
      repeat' first | rfl | split
    exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | setzePasszahl src distance =>
    have htemp : ((Befehl.setzePasszahl src distance).auswerten frame live).temp = frame.temp := by
      simp only [Befehl.auswerten]
      repeat' first | rfl | split
    have hfort : ((Befehl.setzePasszahl src distance).auswerten frame live).fortsetzungen =
        frame.fortsetzungen := by
      simp only [Befehl.auswerten]
      repeat' first | rfl | split
    exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | whileTest src exit handler =>
    have htemp : ((Befehl.whileTest src exit handler).auswerten frame live).temp = frame.temp := by
      simp only [Befehl.auswerten, Rahmen.pass]
      repeat' first | rfl | split
    have hfort : ((Befehl.whileTest src exit handler).auswerten frame live).fortsetzungen =
        frame.fortsetzungen := by
      simp only [Befehl.auswerten, Rahmen.pass]
      repeat' first | rfl | split
    exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | forAnfang unter ober index skipEmpty shadowed missingHandler =>
    have htemp : ((Befehl.forAnfang unter ober index skipEmpty shadowed missingHandler).auswerten
        frame live).temp = frame.temp := by
      simp only [Befehl.auswerten]
      repeat' first | rfl | split
    have hfort : ((Befehl.forAnfang unter ober index skipEmpty shadowed missingHandler).auswerten
        frame live).fortsetzungen = frame.fortsetzungen := by
      simp only [Befehl.auswerten]
      repeat' first | rfl | split
    exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | forTest ende handler =>
    have htemp : ((Befehl.forTest ende handler).auswerten frame live).temp = frame.temp := by
      simp only [Befehl.auswerten, Rahmen.pass]
      repeat' first | rfl | split
    have hfort : ((Befehl.forTest ende handler).auswerten frame live).fortsetzungen =
        frame.fortsetzungen := by
      simp only [Befehl.auswerten, Rahmen.pass]
      repeat' first | rfl | split
    exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | forNaechster zurueck index =>
    have htemp : ((Befehl.forNaechster zurueck index).auswerten frame live).temp = frame.temp := by
      simp only [Befehl.auswerten]
      repeat' first | rfl | split
    have hfort : ((Befehl.forNaechster zurueck index).auswerten frame live).fortsetzungen =
        frame.fortsetzungen := by
      simp only [Befehl.auswerten]
      repeat' first | rfl | split
    exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | zurueckSprung abstand =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | starte name =>
    by_cases hn : (frame.funktionen.map fun f => f.name.val).Nodup
    · cases h2 : frame.funktionen.find? (fun f =>
        !f.misstAbstieg && Funktion.rekursiv frame.funktionen f) with
      | some f =>
        have htemp : ((Befehl.starte name).auswerten frame live).temp = frame.temp := by
          simp only [Befehl.auswerten, hn, h2, Rahmen.halt, Id.run]
          rfl
        have hfort : ((Befehl.starte name).auswerten frame live).fortsetzungen =
            frame.fortsetzungen := by
          simp only [Befehl.auswerten, hn, h2, Rahmen.halt, Id.run]
          rfl
        exact transfer_unveraendert code frame live _ hmem h htemp hfort
      | none =>
        cases h3 : (frame.funktionen.flatMap Funktion.ruft).find? (fun call =>
            !(call.passt frame.funktionen)) with
        | some bad =>
          have htemp : ((Befehl.starte name).auswerten frame live).temp = frame.temp := by
            simp only [Befehl.auswerten, hn, h2, h3, Rahmen.halt, Id.run]
            rfl
          have hfort : ((Befehl.starte name).auswerten frame live).fortsetzungen =
              frame.fortsetzungen := by
            simp only [Befehl.auswerten, hn, h2, h3, Rahmen.halt, Id.run]
            rfl
          exact transfer_unveraendert code frame live _ hmem h htemp hfort
        | none =>
          cases h4 : Funktion.finde frame.funktionen name with
          | none =>
            have htemp : ((Befehl.starte name).auswerten frame live).temp = frame.temp := by
              simp only [Befehl.auswerten, hn, h2, h3, h4, Rahmen.halt, Id.run]
              rfl
            have hfort : ((Befehl.starte name).auswerten frame live).fortsetzungen =
                frame.fortsetzungen := by
              simp only [Befehl.auswerten, hn, h2, h3, h4, Rahmen.halt, Id.run]
              rfl
            exact transfer_unveraendert code frame live _ hmem h htemp hfort
          | some target =>
            cases h5 : frame.eintrittArgumente target.parameter with
            | none =>
              have htemp : ((Befehl.starte name).auswerten frame live).temp = frame.temp := by
                simp only [Befehl.auswerten, hn, h2, h3, h4, h5, Rahmen.halt, Id.run]
                rfl
              have hfort : ((Befehl.starte name).auswerten frame live).fortsetzungen =
                  frame.fortsetzungen := by
                simp only [Befehl.auswerten, hn, h2, h3, h4, h5, Rahmen.halt, Id.run]
                rfl
              exact transfer_unveraendert code frame live _ hmem h htemp hfort
            | some entry =>
              have hentry : RahmenErfuellt code entry := by
                have he := eintrittArgumente_erfuellt code frame target.parameter entry
                  h5 h.1 h.2.1
                have hfort : entry.fortsetzungen = frame.fortsetzungen := by
                  unfold Rahmen.eintrittArgumente at h5
                  split at h5
                  · cases h5
                    rfl
                  · split at h5
                    · cases h5
                      rfl
                    · cases h5
                refine ⟨?_, ?_, ?_⟩
                · intro slot lo hi hlook g hg
                  exact he.1 slot lo hi hlook g hg
                · intro slot l hh hlook d hd cap txt hdt
                  exact he.2 slot l hh hlook d hd cap txt hdt
                · intro k hk
                  rw [hfort] at hk
                  exact h.2.2 k hk
              have hausw : ((Befehl.starte name).auswerten frame live) =
                  entry.ruf name target.parameter target.result := by
                simp only [Befehl.auswerten, hn, h2, h3, h4, h5, Rahmen.halt, Id.run]
                rfl
              rw [hausw]
              exact Rahmen.ruf_erfuellt code entry name target.parameter target.result hentry
    · have htemp : ((Befehl.starte name).auswerten frame live).temp = frame.temp := by
        simp only [Befehl.auswerten, hn, Rahmen.halt, Id.run]
        rfl
      have hfort : ((Befehl.starte name).auswerten frame live).fortsetzungen =
          frame.fortsetzungen := by
        simp only [Befehl.auswerten, hn, Rahmen.halt, Id.run]
        rfl
      exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | ende =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | baueArray ziel element count =>
    have hpoisI : beitragInt (Befehl.baueArray ziel element count) ziel = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.baueArray ziel element count) ziel = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | liesArray basis element count =>
    cases element
    case int lo hi =>
      have hpoisT : beitragText (Befehl.liesArray basis (.int lo hi) count) basis =
          some .unbekannt := by
        simp only [beitragText, schreibtTemp, List.mem_cons_self, if_true]
      exact transfer_schreibe_statischInt code frame live _ _ hmem h _
        rfl (liesArray_hV code frame live basis count lo hi hmem h) hpoisT
    all_goals
      refine transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl ?_ ?_ <;>
        simp only [beitragInt, beitragText, schreibtTemp, List.mem_cons_self, if_true]
  | baueTupel dst types =>
    have hpoisI : beitragInt (Befehl.baueTupel dst types) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.baueTupel dst types) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | liesTupelfeld basis types index =>
    have hpoisI : beitragInt (Befehl.liesTupelfeld basis types index) basis = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.liesTupelfeld basis types index) basis = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | bindeTupel quelle types bind =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | definiereRecord name labels types =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | baueRecord dst name labels types sources =>
    have hpoisI : beitragInt (Befehl.baueRecord dst name labels types sources) dst =
        some .unbekannt := by
      simp only [beitragInt, schreibtTemp, List.mem_cons_self, if_true]
    have hpoisT : beitragText (Befehl.baueRecord dst name labels types sources) dst =
        some .unbekannt := by
      simp only [beitragText, schreibtTemp, List.mem_cons_self, if_true]
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | liesRecordFeld basis name labels types index =>
    have hpoisI : beitragInt (Befehl.liesRecordFeld basis name labels types index) basis =
        some .unbekannt := by
      simp only [beitragInt, schreibtTemp, List.mem_cons_self, if_true]
    have hpoisT : beitragText (Befehl.liesRecordFeld basis name labels types index) basis =
        some .unbekannt := by
      simp only [beitragText, schreibtTemp, List.mem_cons_self, if_true]
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | setzeRecordFeld source indexLocal name labels types index =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | definiereVariante name labels cases =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | baueVariante dst name labels cases index =>
    have hpoisI : beitragInt (Befehl.baueVariante dst name labels cases index) dst =
        some .unbekannt := by
      simp only [beitragInt, schreibtTemp, List.mem_cons_self, if_true]
    have hpoisT : beitragText (Befehl.baueVariante dst name labels cases index) dst =
        some .unbekannt := by
      simp only [beitragText, schreibtTemp, List.mem_cons_self, if_true]
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | waehleVariante source name labels cases branches =>
    cases h1 : (frame.temp source).bind (wertAls (variantValueType name labels cases)) with
    | none =>
      have htemp : (((Befehl.waehleVariante source name labels cases branches).auswerten
          frame live).temp) = frame.temp := by
        simp only [Befehl.auswerten, h1, Rahmen.halt, Id.run]
        repeat' first | rfl | split
      have hfort : (((Befehl.waehleVariante source name labels cases branches).auswerten
          frame live).fortsetzungen) = frame.fortsetzungen := by
        simp only [Befehl.auswerten, h1, Rahmen.halt, Id.run]
        repeat' first | rfl | split
      exact transfer_unveraendert code frame live _ hmem h htemp hfort
    | some v =>
      have htemp : (((Befehl.waehleVariante source name labels cases branches).auswerten
          frame live).temp) = frame.temp := by
        simp only [Befehl.auswerten, h1, Rahmen.halt, Id.run]
        repeat' first | rfl | split
      have hfort : (((Befehl.waehleVariante source name labels cases branches).auswerten
          frame live).fortsetzungen) = frame.fortsetzungen := by
        simp only [Befehl.auswerten, h1, Rahmen.halt, Id.run]
        repeat' first | rfl | split
      exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | textLiteral dst decoded =>
    have hpoisI : beitragInt (Befehl.textLiteral dst decoded) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hV : ∀ (d : Dynamisch),
        (((Befehl.textLiteral dst decoded).auswerten frame live).temp dst) = some d →
        ∀ (cap : Nat) (t : TextValue cap), d = ⟨.text cap, t⟩ → ∀ L H : Nat,
        umgebungText code dst = some (L, H) → L ≤ t.bytes.size ∧ t.bytes.size ≤ H := by
      intro d hd cap t hdt L H hlook
      have htemp : ((Befehl.textLiteral dst decoded).auswerten frame live).temp dst =
          some ⟨.text (sourceUtf8 decoded).size, TextValue.literal decoded⟩ := by
        simp only [Befehl.auswerten, Rahmen.schreibe, Function.update_self]
      rw [htemp] at hd
      cases hd
      cases hdt
      exact textLiteral_wertSat code dst decoded hmem L H hlook
    exact transfer_schreibe_statischText code frame live _ _ hmem h _ rfl hpoisI hV
  | textConcat base a b =>
    have hpoisI : beitragInt (Befehl.textConcat base a b) base = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_statischText code frame live _ _ hmem h _ rfl hpoisI
      (textConcat_hV code frame live base a b hmem h)
  | textIndex base capacity =>
    exact textIndex_transfer code frame live base capacity hmem h
  | substring base capacity =>
    exact substring_transfer code frame live base capacity hmem h
  | textLength base capacity =>
    have hpoisT : beitragText (Befehl.textLength base capacity) base = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_statischInt code frame live _ _ hmem h _
      rfl (textLength_hV code frame live base capacity hmem h) hpoisT
  | definiereTraeger count labels layout exported =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | optionIstBesetzt dst count =>
    have hpoisI : beitragInt (Befehl.optionIstBesetzt dst count) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    have hpoisT : beitragText (Befehl.optionIstBesetzt dst count) dst = some .unbekannt := by
      exact if_pos List.mem_cons_self
    exact transfer_schreibe_unbekannt code frame live _ _ hmem h _ rfl hpoisI hpoisT
  | definiereEffektgruppe effects =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | waehleUmgebung name abi row =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | bindeRegion receiver init =>
    cases h1 : (frame.lokale[receiver]?.join.bind (wertAls .ownedRegion)) with
    | none =>
      have htemp : (((Befehl.bindeRegion receiver init).auswerten frame live).temp) =
          frame.temp := by
        simp only [Befehl.auswerten, Rahmen.bindeRegion, h1, Rahmen.halt, Id.run]
        repeat' first | rfl | split
      have hfort : (((Befehl.bindeRegion receiver init).auswerten frame live).fortsetzungen) =
          frame.fortsetzungen := by
        simp only [Befehl.auswerten, Rahmen.bindeRegion, h1, Rahmen.halt, Id.run]
        repeat' first | rfl | split
      exact transfer_unveraendert code frame live _ hmem h htemp hfort
    | some slot =>
      have htemp : (((Befehl.bindeRegion receiver init).auswerten frame live).temp) =
          frame.temp := by
        simp only [Befehl.auswerten, Rahmen.bindeRegion, h1, Rahmen.halt, Id.run]
        repeat' first | rfl | split
      have hfort : (((Befehl.bindeRegion receiver init).auswerten frame live).fortsetzungen) =
          frame.fortsetzungen := by
        simp only [Befehl.auswerten, Rahmen.bindeRegion, h1, Rahmen.halt, Id.run]
        repeat' first | rfl | split
      exact transfer_unveraendert code frame live _ hmem h htemp hfort
  | zugriff form =>
    have hbf := hrein _ hmem
    simp only [keinFremdzugriff] at hbf
    cases hbf
  | faden form =>
    have hbf := hrein _ hmem
    simp only [keinFremdzugriff] at hbf
    cases hbf
  | maskiere vektor aus =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | prioritaet grenze =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | sendeUnterbrechung vektor kern =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl
  | leiteLeitung leitung kern prioritaet =>
    exact transfer_unveraendert code frame live _ hmem h rfl rfl

end Gabbro.Core.Ziel.Korrektheit.WaechterAnalyse
