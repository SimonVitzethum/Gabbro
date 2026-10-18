/-
  Datei:      Grammatik/InterferenzAllgemein.lean
  Gegenstand: **DAS GEMEINSAME MODELL BELIEBIG VIELER FAEDEN** -- N Faeden (`List Faden`),
               beliebig viele Schritte (eine Weltenkette), geteilte Traeger eingeschlossen
               ueber Invariantendisziplin (CSL-Gestalt: ein Invariantenpraedikat je Traeger,
               Beruehren nur unter der Wache).

  ## Das Modell

  Ein `GemeinsamerLauf` traegt, was die angefuehrten Stellen liefern:

    * `hSchritt` -- jeder Schritt der Kette bleibt im Rahmen seines Fadens (je Schritt
      das, was `exec_rahmen` je Rumpf liefert, `Satz.lean`; die Kette zaehlt die Schritte
      in `schrittFaden`, die Welten in `welten`, verkettet ueber `hKette`),
    * `hPaar` -- je zwei verschiedene Faeden der Liste stehen in `Nb` (deklarierte Paare,
      `Wettlauf.lean` §6; geschlossene Welt ueber den N Faeden),
    * `hGesittet` -- der Lauf ist sperrdiszipliniert (`Gesittet`, `Wettlauf.lean`),
    * `hBeschraenkt` -- nur Deklarierte teilen sich den Lauf (`BeschraenkteVerschraenkung`),
    * `hEintritt` -- jeder Faden haelt beim Eintritt genau seine erklaerten Sperren
      (`EintrittPasst`: die Form von `RufPasst.hh`, SG-20, die Sperrmenge in BEIDEN
      Richtungen, je Faden),
    * `hSchuld` -- jeder Faden haelt die Sperren aller Traeger jeder geschuldeten
      Invariante (`SchuldnerHaelt`: die Gestalt von `invarianten_gehalten`, U003, mit
      `schuldet` als Bedingung; je Rumpf ableitbar, `schuldnerHaelt_gilt`),
    * `hInvSicht` -- die Invariantensicht liest unter gehaltenen Sperren (`InvSichtHaelt`:
      die Gestalt von `heldIn_invarianten` ueber `hEintritt`, je Faden am Eintritt;
      aus `hEintritt` ableitbar, `invSichtHaelt_aus_Eintritt`).

  ## Die Disziplin ueber geteilten Traegern

  `Interferenz.lean` schliesst gemeinsame Schreibtraeger AUS (`Disjunkt`). Hier sind sie
  EINGESCHLOSSEN, aber nur unter Disziplin: `TraegerInv` traegt ein Praedikat je Traeger
  (`inv`) plus die Beruehrregel (`disziplin`: wer schreibt, haelt die Waechter --
  Anfassen nur unter der Wache). `GeteiltGedeckt` sagt, was das fuer die Faeden heisst:
  schreibt ein zweiter Faden denselben Traeger, so ist der Traeger geteilt UND beide
  halten eine gemeinsame Sperre seines Waechter (`GemeinsameSperre`). `InvariantenKontext`
  verlangt das Praedikat an jeder Welt der Kette.

  ## Die Aussage -- Satz, verengt, aber bewiesen

  `StabilSchritt` ist `stabil` (`Interferenz.lean`) als `Prop`-Gestalt; `stabilSchritt_gilt`
  loest sie ein. `StabilKette` faltet die Gestalt ueber die Kette; `stabilKette_gilt` loest
  sie aus `HaengtAb` ein. `allgemeinStabil` ist der Hauptsatz: unter Invariantenkontext,
  geteilter Deckung, rahmenabhaengigen Zusicherungen je Faden, Gueltigkeit am Kettenkopf
  und schrittweiser Erhaltung gilt jede Zusicherung jedes Fadens an der letzten Welt der
   Kette. Die Erhaltung ist je fremdem Schritt eine Disjunktion -- disjunkt (faellt auf
   `stabil` zurueck) ODER erhaltend (die geteilte Seite, von der Invariantendisziplin von
   aussen einzuloesen) -- und je eigenem Schritt eine Erhaltpraemisse. Die Induktion
   (`kette_erhaelt`) laeuft ueber die Schrittzahl; drei kleine Listenhelfer
   (`kette_welt_belegt`, `lt_of_belegt`, `getLast?_eq_getElem` aus dem Kern) tragen die
   Indexrechnung, ganz ohne `mathlib`. `FremdDisziplin` traegt je Schritt Wache plus
   Rahmen; `fremdDisziplin_gilt` loest beides ein (Wache aus der Beruehrregel, Rahmen
   aus `hSchritt`), und `fremdErhalt_disjunkt_aus_Disziplin` zieht die disjunkte
   Erhaltung daraus ueber `stabil`. `invErhalt_aus_Kontext` zieht die invariante
   Erhaltung aus dem Kontext, und `allgemeinStabil_invariant` faltet sie zur Kette:
   dort ist keine geteilte Praemisse mehr anzunehmen. `schuldnerHaelt_gilt` (U003 je
   Rumpf) und `invSichtHaelt_aus_Eintritt` (ueber der beidseitigen Eintrittsmenge)
   loesen die Eintrittsdisziplin ein, soweit die Pruefung sie liefert.

  ## Was dieser Satz NICHT sagt -- jeder Schnitt gebucht

  (G1) `AllgemeinStabil` als voraussetzungslose `def`-Gestalt ist GESTRICHEN; an ihrer
       Stelle steht `allgemeinStabil` mit verengten Praemissen (`hInit` am Kettenkopf,
       `hFremd` als Disjunktion, `hEigen` je eigenem Schritt). Die Induktion ueber die
       Kette wird hier gefuehrt (`kette_erhaelt`), nicht vertagt.
  (G2) Die vorausgesetzte Menge ist der volle Vertragsrahmen (`D.schreibt` /
       `D.gschreibt`), nicht der syntaktische Fussabdruck. Wie in (S1) wird angenommen,
       dass eine Zusicherung nur ihren Rahmen liest (`HaengtAb` als Praemisse, `hAb`).
   (G3) Die Beruehrregel (`disziplin`) ist eine Praemisse, aber je Schritt EINGELOEST
        (`fremdDisziplin_gilt`: Wache aus der Regel, Rahmen aus `exec_rahmen` via
        `hSchritt`); die disjunkte Seite von `hFremd` fliesst daraus ueber `stabil`
        (`fremdErhalt_disjunkt_aus_Disziplin`), die invariante Seite aus dem Kontext
        (`invErhalt_aus_Kontext`, `allgemeinStabil_invariant`). Was BLEIBT, ist die
        geteilte Seite fuer beliebiges rahmenlokales `Q` (rechte Seite von `hFremd` in
        `allgemeinStabil`): dass der Pruefer die gehaltenen Mengen je Schreibstelle
        nachweist, steht nirgends -- der Pruefer kennt keine Haltemengenanalyse
        (`NEBENLAEUFIGKEIT-ENTWURF.md` §6, Punkt 1).
(G4) Sperrgeteilte Traeger sind EINGESCHLOSSEN (rechte Seite von `hFremd`, Deckung als
     `GeteiltGedeckt` getragen). `atomic`-Globale (A10, die Maschine ordnet) und
     `publishes`/`awaits`-Paare (die Paarung ordnet) stehen als Ausnahmen NEBEN
     `GeteiltGedeckt` (`AtomarAusgenommen`, `PaarungAusgenommen`,
     `GeteiltGedecktMitAusnahmen`, §13): befreite Traeger brauchen kein
     Sperrargument (`atomarAusgenommen_entlaedt`, `paarungAusgenommen_entlaedt`,
     `geteiltGedecktMitAusnahmen_von_Ausnahmen`, §15). Was BLEIBT, ist die
     Einloesung je Schreibstelle im Pruefer (G3) -- die Ausnahme entlaedt den
     Traeger, nicht den Nachweis, dass sie greift.
   (G5) `Gesittet` wird getragen, nicht verbraucht (wie S2): HB-Ordnung aus `kein_wettlauf`
        ist unverbunden mit Stabilitaet -- geordnete Schreibzugriffe bleiben
        Schreibzugriffe. `hSchuld` wird ABGELEITET, nicht getragen (`schuldnerHaelt_gilt`:
        U003 gilt je Rumpf, ohne Laufpraemisse); `hDeck` wird weiter getragen: es
        beurkundet die Disziplin, unter der die geteilte Restseite von `hFremd` steht;
        `hInv` wird im invarianten Satz verbraucht (`invErhalt_aus_Kontext`).
 (G6) Der Eintritt je Faden ist eine eigene Welt (`eintritt`), kein Gabelmodell: wie
     Faeden starten und enden, steht nirgends. Erzeugung und Vereinigung stehen als
     Eintraege daneben (`SpawnEintrag`/`JoinEintrag`: die Kindwelt ist die Kettenwelt
     an der eingetragenen Stelle, §12, eingelöst in §16
     `kindEintrittAusSpawn_belegt/mem`, `kindEintrittAusJoin_belegt/mem`,
     `kindEintrittAusGabel_belegt_aus_find/mem`). Was BLEIBT: kein
     Ausfuehrungsmodell der Gabel -- die Eintraege nennen die Stelle, sie erzeugen
     sie nicht. Darum gilt die sequenzielle Gueltigkeit (`hInit`) weiter am
     Kettenkopf, nicht am Eintritt -- `hEintritt` wird getragen, aber `hInvSicht`
     folgt daraus (`invSichtHaelt_aus_Eintritt`: die Gestalt von
     `heldIn_invarianten` ueber der beidseitigen Sperrmenge).
(G7) `Q` des Hauptsatzes spricht nur ueber die Welt; Belegungen stehen als Gestalt
     daneben (`EnvZusicherung`, `FadenEnvZusicherung`, `EnvErhalt`, §14, eingelöst
     in §17: Kette `kette_erhaelt_env`, `fadenEnv_kette_erhaelt`,
     `fadenEnv_letzte_erhaelt`, Hebung `envErhalt_aus_weltErhalt`, Schrittgleichheit
     `envErhalt_refl/symm/trans`): die eigene Belegung bleibt je Schritt fest, kein
     Faden teilt sie. Was BLEIBT (wie in S6): `hEigen` wird angenommen, nicht aus
     der sequenziellen Ausfuehrung abgeleitet -- eigene Schritte erhalten `Q`,
     statt es erst herzustellen.
-/

import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T1
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T2
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T3
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T4
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T5
