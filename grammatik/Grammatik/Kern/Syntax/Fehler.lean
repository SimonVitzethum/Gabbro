/-
  Datei:      Grammatik/Fehler.lean
  Gegenstand: **Der Fehlerausgang als PARALLELES Modell** -- neben `Semantik.lean`, nicht
              darin. Nichts an `eval`, `exec` oder `Ausgang` aendert sich; diese Datei legt
              daneben, was ein benannter Fehler waere, und in welcher Form die Ueberein-
              stimmung stuende, faellt er nicht.

    `Fehlerklasse` -- die vier benannten Fehler: `index` (Index ausserhalb), `ueberlauf`
                      (Ablage ausserhalb der erklaerten Breite), `nenner` (Nenner null),
                      `gestalt` (Gestalt passt nicht).
    `ErgebnisF`    -- der parallele Ausgang eines Ausdrucks: `wert` oder `fehler`.
    `evalF`        -- die parallele Auswertung: `State -> Expr -> Wert plus Fehlerklasse`
                      als Gestalt (`World D -> Expr D Γ Λ τ -> ErgebnisF D τ`, mit
                      Eintrittswelt und Sichtbereich als Argumenten wie bei `eval`).
    `evalF_ok` / `evalF_stimmt`
                   -- die Uebereinstimmungsform als `Prop`-Definitionen: kein Fehler
                      heisst, `eval` stimmt zu -- plus die Beweise, wo sie schliessen
                      (`evalF_ok_halt`, `evalF_stimmt_halt`).
    `IndexFalle` / `FehlerFall`
                   -- die Geschenk-Falsifizierer als DATEN, nicht als Beweise: ein Index
                      ausserhalb seines Bereichs erreicht `fehler .index` per Definition.
    `ErgebnisF.bind` / `map`
                   -- der Ausbreitungskern: ein fehlerhafter Eingang fehlert die Ausgabe.
    `evalArgsMit` / `evalArgsF`
                   -- die `evalAll`-Gestalt: ein fehlerhaftes Argument fehlert die Liste
                      (`evalArgsMit_kopf_fehler`, `_rest_fehler`); was heute nie fehlt,
                      steht als Satz (`evalArgsMit_ok`, `evalArgsF_ok`).
    `AusF` / `AusF.folge`
                   -- die Schrittfolge-Gestalt neben `Ausgang`: ein Fehler laeuft nicht
                      weiter (`folge_fehler`), `ok` schon (`folge_ok`), `logik` und
                      `hardware` bleiben stehen (`folge_logik`, `folge_hardware`).
    `schrittFolge` -- die Blockfolge ueber Welt-Schritte: ein fehlerhafter Schritt
                      fehlert die Folge                       (`schrittFolge_vorn`, `_hinten`).
    `schleifeF` / `durchlaufF`
                   -- der Schleifendurchgang (`foreverLauf`- / `traverseLauf`-Gestalt):
                      ein fehlerhafter Durchgang fehlert den Lauf (`schleifeF_fehler`,
                      `schleifeF_spaeter`, `durchlaufF_kopf`, `durchlaufF_rest`).
    `endZustandF`  -- die `finalState`-Gestalt: ein Fehler hat keinen Nachzustand
                      (`endZustandF_fehler`, `_logik`, `_hardware`, `_ok`).
    `IstBenannt`   -- die Sicherheitsform: `stuck`-oder-Fehler heisst eigene Logik
                       oder benannter Fehler (`fehler_ist_benannt`, `logik_ist_benannt`,
                       `hardware_ist_benannt`, `folge_benannt_bleibt`,
                       `ausF_klassifikation`).
    `AusF.vonAusgang` / `zuAusgang`
                   -- die Einbettung in die Ausfuehrung: jeder `Ausgang` laeuft als
                      `weiter` weiter (`zuAusgang_vonAusgang`), ein benannter Fehler
                      hat keinen `Ausgang` (`zuAusgang_fehler`); `folge_weiter`
                      stimmt die Folge mit `execBlock` (`ok` weiter, sonst `o`),
                      je ein Fortpflanzungssatz pro Ausgang (`folge_zurueck`,
                      `_grund`, `_leave`, `_next` neben `_ok`, `_logik`,
                      `_hardware`).
    `IstStecken`   -- `stuck` als Abwesenheit eines Nachzustands; `stuck` heisst
                      benannt (`stecken_heisst_benannt`) und umgekehrt
                      (`benannt_heisst_stecken`), in disjunktiver Form
                      (`stecken_klassifikation`): die `exec_sicher`-Gestalt.
    `evalArgsMit_stimmt` / `evalArgsF_stimmt`
                   -- die Uebereinstimmung DURCH die `evalAll`-Gestalt: was die
                      fehlerfuehrende Liste traegt, rechnet `evalArgs`.
    `schrittRein` / `schrittFolge_rein`
                   -- die Schrittfolge ohne Fehler faltet die Welt
                      (`execBlock`-Gestalt ohne Fehlerarm).
    `durchlaufRein` / `durchlaufF_rein`
                   -- der Durchlauf ohne Fehler faltet ueber die Elemente
                      (`traverseLauf`-Geruest ohne Invarianten-, `leave`-,
                      `next`-Arme).
    `schleifeF_als_folge`
                   -- die treibstoffbegrenzte Schleife ohne Fehler IST die
                      Schrittfolge ihrer Abwicklungen (`foreverLauf`-Geruest
                      ohne `fortschritt`-Arm).
     `endZustandF_*` -- die `finalState`-Abbildung, vollstaendig: je ein Satz pro
                       Ausgang (`_zurueck`, `_grund`, `_leave`, `_next` neben
                       `_ok`, `_logik`, `_hardware`, `_fehler`).
     `blockF` / `traverseAusF` / `foreverAusF`
                    -- die `execBlock`- / `traverseLauf`- / `foreverLauf`-Gestalt mit
                       Fehlerarm: ein fehlerhafter Kopf fehlert den Block
                       (`blockF_cons_fehler`), `ok` uebergibt (`blockF_cons_ok`),
                       jeder andere Ausgang bleibt stehen (`blockF_cons_weiter`);
                       ein fehlerhaftes Element fehlert den Durchlauf
                       (`traverseAusF_kopf_fehler`), `ok`/`next` laufen weiter
                       (`traverseAusF_kopf_ok`, `_kopf_next`), der fehlerhafte
                       Rest traegt durch (`traverseAusF_ok_rest_fehler`);
                       fehlerfrei stimmt der Durchlauf mit `traverseLauf`
                       (`traverseAusF_stimmt`); der treibstoffbegrenzte Lauf
                       ebenso (`foreverAusF_kopf_fehler`, `_kopf_ok`); ein
                       fehlerhafter Kopf ist benannt
                       (`blockF_cons_fehler_benannt`).

  Warum `evalF` heute nie fehlt -- und das ist die Aussage, kein Mangel: ein
  `Expr.slot`-Index hat den Typ `.index (D.count t)` und traegt seinen Bereichsbeweis
  bei sich; ausserhalb ist nicht schreibbar. Der Fehlerarm ist nur ueber ROHE Daten
  (`IndexFalle`: Tabelle plus nacktes `Int`) erreichbar -- genau die Stelle, an der
  der Pruefer heute den Bereich haelt (`S3-FEHLER-ENTWURF.md`).

  DURCHGEFAEDELT (parallel, nicht am Anschluss): die Ausbreitung steht als parallele
    Form MIT Beweisen -- je eine Ausbreitungsaussage pro Kombinator (siehe oben).
    Der ANSCHLUSS steht als Einbettung mit Uebereinstimmung: `vonAusgang` traegt
    jeden `Ausgang` als `weiter`, `folge_weiter` stimmt die Folge mit `execBlock`,
    `stecken_heisst_benannt`/`benannt_heisst_stecken` sagen `stuck` GENAU DANN,
    wenn benannt, und `evalArgsF_stimmt`/`schrittFolge_rein`/`durchlaufF_rein`/
     `schleifeF_als_folge` stimmen `evalF` DURCH Schritt- und Schleifengestalten
     mit `eval`/`evalArgs`. Was fehlt, ist die Durchfaedelung, nicht die Form:
     `execStmt`/`execBlock`/`traverseLauf` rufen die parallelen Formen nicht auf
     (Schnitt S1'). Seit §11 stehen auch die Block- und Schleifenformen mit
     Fehlerarm als parallele Form mit Beweisen (`blockF_*`, `traverseAusF_*`,
     `foreverAusF_*` samt `traverseAusF_stimmt`); was weiterhin fehlt, ist die
     echte Rekursion ueber `Stmt`/`Block` -- sie steht in `Semantik.lean` und
     ruft die parallelen Formen nicht auf.

  Vorausgesetzt (vertraut, nicht bewiesen):
    P1  `eval` aus `Semantik.lean` ist die Bedeutung: `evalF` ruft es auf, statt es
        nachzubauen. Zwei Auswerter waeren zwei Bedeutungen.
    P2  Rohe Indizes kommen von aussen (`Orakel`, Maschine): `IndexFalle.k` ist ein
        Datum, kein Term der Grammatik.

  Schnitte (gebucht, nicht versteckt):
     S1' Anschluss an `exec` halb geschlossen: Einbettung (`vonAusgang`,
         `zuAusgang`), Folgen-Uebereinstimmung (`folge_weiter` plus je ein Satz
         pro Ausgang), `stuck`-genau-dann-benannt (`stecken_heisst_benannt`,
         `benannt_heisst_stecken`, `stecken_klassifikation`) und die
         Uebereinstimmung durch `evalAll`- (`evalArgsF_stimmt`), Schritt-
         (`schrittFolge_rein`) und Schleifengestalten (`durchlaufF_rein`,
         `schleifeF_als_folge`) stehen mit Beweisen; dazu seit §11 die Block-
         und Schleifenfortpflanzung mit Fehlerarm (`blockF_cons_fehler`,
         `_cons_ok`, `_cons_weiter`, `traverseAusF_kopf_fehler`, `_kopf_ok`,
         `_kopf_next`, `_ok_rest_fehler`, `foreverAusF_kopf_fehler`,
         `_kopf_ok`), die Durchlauf-Uebereinstimmung (`traverseAusF_stimmt`)
         und der Benannt-Anschluss (`blockF_cons_fehler_benannt`); `Ausgang`
         bekommt keinen `fehler`-Fall, und `execStmt`/`execBlock`/`traverseLauf`
         faedeln ihn nicht durch. Die Koordination bleibt, was
         `S3-FEHLER-ENTWURF.md` §6 nennt.
         Offen (braucht `Semantik.lean`, exakt gebucht): die echte
         Durchfaedelung durch `Stmt`/`Block` -- `execStmt`/`execBlock`/`execEnd`
         ueber `P`/`O`/`passes`/`R` und `traverseLauf` mit `Block`-Ruempfen.
         Fehlendes Lemma, exakt: `execBlock_cons_fehler` -- fuer alle `P O`
         `passes R s rest σ ρ k` gilt: liefert die fehlerfuehrende Form von
         `execStmt s σ ρ` den Fehler `k`, so liefert die fehlerfuehrende Form
         von `execBlock (cons s rest) σ ρ` den Fehler `k`. Es schliesst hier
         nicht, weil `Ausgang` keinen `fehler`-Fall traegt und `execStmt`/
         `execBlock` weder `AusF.folge` noch `blockF` rufen; es zu schliessen
         verlangt den Fehlerarm in `Semantik.lean` (Rueckgabe `AusF` statt
         `Ausgang`), und das ist gebucht, nicht getan.
    S2  `evalF` reicht jeden Aufruf an `eval` durch und meldet `wert`: die Fehler-
        arme sind erreichbar nur ueber die Fallen-Daten, nicht ueber Terme.
        Geschlossen dagegen, was schloss: `evalF_ok_halt`, `evalF_stimmt_halt`,
        `evalArgsF_ok` -- und die Uebereinstimmung DURCH die Gestalten:
        `evalArgsMit_stimmt`/`evalArgsF_stimmt` gegen `evalArgs`,
        `schrittFolge_rein`/`durchlaufF_rein`/`schleifeF_als_folge` als Faltung
        ohne Fehlerarm, `endZustandF` je Ausgang. Was heute nie fehlt, steht
        als Satz, nicht als Behauptung.
    S3  Nicht in `Grammatik.lean` verdrahtet: die Bahnbreite verbietet den
        Indexeingriff; pruefen allein mit `lake env lean Grammatik/Fehler.lean`.

  Kein `mathlib`, kein `sorry`, kein `axiom`, kein Import aus `programmlogik/`.
-/

import Grammatik.Kern.Syntax.Fehler.T1
import Grammatik.Kern.Syntax.Fehler.T2
