/-
  Datei:      Grammatik/Komposition.lean
  Gegenstand: **Die Komposition der Ruempfe** -- die Gestalt, in der `UmgebungOK` und
              `SchleifenOK` aus den Laeufen entlassen werden. Nur Gestalt, kein Beweis:
              jede Aussage unten steht als `def` ueber `Prop`, nie als `theorem`.

  Was wo steht:

    §1  `Routine`, `Gefuege`      -- die Koerpertabelle UND die Abbildung in die
                                     Umgebung als Felder EINER Struktur
    §2  `ruftAn`, `Topologisch`, `AzyklischUnter`, `ZyklusGetragen`
                                  -- die Ordnung des Rufgraphen: azyklisch
                                     topologisch, zyklisch ueber das Mass
    §3  `Mitglied`, `UnterMass`, `VertragSchranke`, `RekursionZyklusGetragen`
                                  -- die Zyklusform von `Coverage.lean`
                                     (`recursion_cycle_carried`) als `def`
    §4  `UmgebungOk`, `SchleifenOk` -- die beiden Praemissen als `Prop`-wertige
                                     `def`s ueber dem Graphen
    §5  `Durchgang`, `DurchgangBesucht`, `SchleifeLaeuft`
                                  -- der Schleifendurchgang als Indexliste
    §6  `RufAusOrdnung`, `UmgebungOkAusLaeufen`, `ZyklusAusMass`,
        `SchleifenOkAusLaeufen`   -- die Kompositionssaetze als AussageFORMEN
  §7  `OhneMassTabelle`, `ZyklusOhneMass`, `ohne_mass_ist_none`,
        `ZyklusOhneMassWirdAbgewiesen`
                                   -- der Zyklus ohne `decreases` als DATUM, mit
                                      der Abweisung als pruefbarer Form
  §8  `DurchgangImBereich`, `SchleifeLaeuftImBereich`, `DurchgangGezaehlt`,
      `SchleifeLaeuftGezaehlt`, `SchleifenOkAusGezaehltenLaeufen`
                                   -- die gezaehlte Laufform (`RunsLoopN`) als
                                      `def`s nach dem Muster von `RunsLoop` /
                                      `RunsLoopIn` aus §5
  §9  `SchleifeInMitglied`, `MassAussenSchleifeInnen`, `SchleifeAussenMassInnen`,
      `UmgekehrteTabelle`, `Umgekehrt`, `UmgekehrteMitglieder`,
      `UmgekehrterDurchgang`, `schleife_sitzt_in_a`,
      `UmgekehrtWirdAbgewiesen`  -- die feste Schachtelung (Mass aussen,
                                      Schleife innen) und die Abweisung der
                                      umgekehrten als DATUM mit pruefbarer Form
  §10 `zyklus_aus_mass_genau`, `umgebung_ok_aus_pflichten`,
      `schleife_gibt_regel`, `bereich_gibt_regel`, `gezaehlt_gibt_regel`,
      `gezaehlt_ist_bereich`, `gezaehlt_laeuft_bereich`, `bereich_laeuft`,
      `gezaehlt_laeuft`, `gezaehlt_schranke_nichtnegativ`,
      `schleifen_ok_aus_allen_lauefen`,
      `schleifen_ok_aus_gezaehlten_allen`, `durchgang_falte_erhaelt`,
      `ZweiSchleifenTabelle`, `ZweiSchleifen`, `EinDurchgang`,
      `ein_durchgang_laeuft_gezaehlt`, `zwei_schleifen_nicht_ok`,
      `einzelner_lauf_schliesst_nicht_alle`,
      `einzelner_gezaehlter_lauf_schliesst_nicht_alle`,
      `zyklus_ohne_mass_abgewiesen_satz`, `umgekehrt_abgewiesen_satz`
                                    -- die S2-Saetze als `theorem` (bewiesen, kein
                                       `sorry`/`axiom`): die Zyklushebung aus der
                                       getragenen Form, die Umgebung aus Deckung
                                       plus Pflichten je Zeile, die Schleifenregel
                                       aus einem Lauf je Schleife (gezaehlt ueber
                                       `DurchgangGezaehlt`), die Induktion ueber
                                       `indizes` als `foldl`-Erhaltung, und die
                                       Abweisung der Ein-Lauf-Formen als Daten

  Entsprechungen (Namen und Form, kein Bezug -- siehe C1):
    `Gefuege.tabelle`             -- `Programm.sig`/`Programm.schleife`
                                     (`Sicherheit/Anweisung.lean`:206)
    `Gefuege.laeuft`              -- `Runs rho f body` (`Body.lean`:1408)
    `Routine.ruft`                -- die Rufstellen des Rumpfes
    `Routine.mass` (`some`)       -- `decreases e` (`SYNTAX.md` §6, «K5.4»);
                                     `none` heisst: kein Mass erklaert
    `Routine.schleifen`           -- die Schleifenkennungen des Rumpfes
                                     (`Programm.schleife`)
    `Durchgang.indizes`           -- `iterate` (`Body.lean`:1415): ein Durchgang
                                     je Index, die Variable daran gebunden
    `Topologisch`/`AzyklischUnter`-- die Induktion ueber die topologische Ordnung
    `RekursionZyklusGetragen`     -- `RecursionCycleCarried` /
                                     `recursion_cycle_carried`
                                     (`Coverage.lean`:972/979)
    `VertragSchranke`             -- `ContractBelowM` (`Body.lean`:1525): der
                                     Vertrag des Zyklusmitglieds, beschraenkt
                                     durch das Mass des Rufers
  `UmgebungOk`                  -- `UmgebungOK` (`Anweisung.lean`:599)
  `SchleifenOk`                 -- `SchleifenOK` (`Anweisung.lean`:608)
  `SchleifeLaeuftImBereich`     -- `RunsLoopIn` (`Body.lean`:1610)
  `SchleifeLaeuftGezaehlt`      -- `RunsLoopN` (`Body.lean`:1671)
  `SchleifenOkAusGezaehltenLaeufen`
                                -- `looprule_of_body_p` (`Body.lean`:1721)
  `MassAussenSchleifeInnen`     -- die Schachtelung aus `KompositionBeweis.lean`
                                      (C6): die Schleifenregel unter den
                                      beschraenkten Vertraegen, der Zyklus aussen

  VORAUSSETZUNGEN, gebucht:
    (P1) Jede Zeile der Tabelle nennt alle Rufe ihres Rumpfes (`ruft` ist
         vollstaendig) und alle Schleifen (`schleifen` ist vollstaendig).
    (P2) `laeuft f` heisst: wo der Rumpf endet, antwortet die Umgebung mit
         genau diesem Zustand und Wert -- was bei `stuck` gilt, sagt die
         Pflicht, nicht diese Datei.
    (P3) Masse sind `Nat`-Werte; der Fall ist strikt (`<`) an JEDER Kante
         zurueck in den Zyklus.

  SCHNITTE, gebucht und nicht versteckt:
    (C1) Kein Import des Modells: die Bahn verbietet den Indexeingriff, und die
         Pruefung laeuft je Datei -- darum gilt die Entsprechung ueber Namen und
         Form, nicht ueber Bezug. Nichts nennt `traverseLauf`/`Runs`/`Contract`
         als Term.
    (C2) Die Pflicht je Rumpf (`pruefeBlock_sicher` ueber dem Koerper, die
         `exited`- und `left`-Zeilen) steht nicht hier: DASS der Koerper seine
         Pflicht haelt, ist die Logik des Schreibers und die Arbeit des
         Pruefers. Diese Datei zeigt nur, WOHIN die Pflicht gehoben wird.
    (C3) Fremde Ruempfe (`extern`, `asm`, anvertraut) haben keine Zeile und
         damit keinen Vertrag: ihre Vertraege bleiben Hypothesen ueber `laeuft`.
  (C4) Nicht in `Grammatik.lean` verdrahtet: der Bahnumfang verbietet den
       Indexeingriff; pruefe diese Datei unmittelbar mit
       `lake env lean Grammatik/Komposition.lean`.
  (C5) `indizes` bleibt `List Nat`; Bereich und Schranke sprechen `Int` wie im
       Modell (`RunsLoopN` laeuft ueber `List Int`). Die Koerzion traegt nur EINE
       Richtung: ein Durchgang besucht keine negativen Indizes -- was das Modell
       mit negativen Indizes sagt, sagt diese Datei nicht.
  (C6) Die Abweisung der umgekehrten Schachtelung steht als `¬`-Form ueber EINEM
       Datum (`Umgekehrt`) -- wie §7 kein Allgemeinsatz, sondern die Gestalt, in
       der die umgekehrte Ordnung nichts schliesst.
  (C7) Die Ein-Lauf-Formen schliessen NICHT: `SchleifenOkAusLaeufen` und
       `SchleifenOkAusGezaehltenLaeufen` folgen aus EINEM Lauf die Regel ALLER
       Schleifen -- das Datum `ZweiSchleifen` (`s1` laeuft, `s2` gilt nicht)
       widerlegt beide (`einzelner_lauf_schliesst_nicht_alle`,
       `einzelner_gezaehlter_lauf_schliesst_nicht_alle`). Was schliesst, ist
       die Verkleinerung: die Regel DIESER Schleife (§10, Projektionen) und
       die Regel aller Schleifen aus einem Lauf JE Schleife
       (`schleifen_ok_aus_allen_lauefen`, gezaehlt
       `schleifen_ok_aus_gezaehlten_allen`).
  (C8) Kein Import auch in §10 (C1 gilt weiter): `Durchgang.indizes`
       (`List Nat`) spiegelt die Indexlisten-Rekursion von `traverseLauf`
       (`Semantik.lean`: `List (Wert D τ)`) -- nicht `Body.iterate` aus
       `programmlogik` (anderes Modell: `Env` plus `List Int`). Die
       Entsprechung gilt ueber Namen und Form, nicht ueber Bezug; nichts in
       §10 nennt `traverseLauf`/`exec`/`Runs` als Term. Die Induktion ueber
       `indizes` (`durchgang_falte_erhaelt`) ist die Schleifeninduktion in
       dieser Gestalt.
  (C9) `theorem` gehoert in §10 der bewiesenen Phase: §1-§9 bleiben `def`-Formen
       und sind unberuehrt -- §10 legt die Saetze daneben, mit `#print axioms`
       je Satz.

  Kein `mathlib`, kein `sorry`, kein `axiom`.
-/

/- Nur Formen, keine Saetze: `Prop`-wertige Aussagen stehen in dieser Bahn als `def`,
   weil `theorem` der spaeteren Phase gehoert. -/
module

public import Grammatik.Logik.Vertraege.Komposition.Teil1
public import Grammatik.Logik.Vertraege.Komposition.Teil2
