/-
  Datei:      Grammatik/Ziel.lean
  Gegenstand: **DAS ZIEL**, als Satz ueber der Grammatik -- unabhaengig vom `.rs`-Code.

  > Wer ein Gabbro-Programm verifiziert, beweist NUR seine eigene Logik und seine
  > Hardwaremassnahmen. Den Rest tragen Gabbro und CompCert -- angenommen, Gabbro
  > ist formal verifiziert.

  Was das hier heisst, und warum es nicht vom Pruefer (`.rs`) abhaengt:

    * Die Grammatik ist `Syntax.lean` (getypte Familie): was sie nicht ableitet,
      ist nicht schreibbar -- kein Pass kann es vergessen, weil es keinen Term
      dafuer gibt.
    * Die Bedeutung ist `Semantik.lean` (`eval`/`exec`, totale Funktionen): jeder
      Ausgang ist Kontrollfluss, `logik` oder `hardware` (`zwei_fehler`).
    * Der Rahmen und die Spur sind `Satz.lean` (`exec_rahmen`, `exec_spur`,
      `exec_gut`): ein Rumpf schreibt nur, was sein Vertrag nennt, und jeder
      Zugriff traegt die Waechter seines Traegers.
    * Die Wettlaeufe sind `Wettlauf.lean` (`kein_wettlauf`,
      `kein_wettlauf_global`, `keine_ueberkreuzung`): ueber JEDER Verschraenkung
      solcher Spuren ist ein bewachter Traeger geordnet oder `atomic`.
    * Die Stabilitaet ist `InterferenzAllgemein.lean` (`allgemeinStabil`):
      gueltige und schrittweise erhaltene Zusicherungen gelten an der letzten
      Welt der Kette.
    * Die Komposition ist `Komposition.lean` (`UmgebungOk`, `SchleifenOk`):
      die Ruf- und Schleifenordnung als Gestalt, noch ohne Beweis.
    * Das Geteilte ist `Geteilt.lean` (`geteilt_treu`): als ungeteilt
      Erklaertes erreicht hoechstens ein Faden -- gerechnet, nicht angenommen.
    * Die Zeit ist geteilt («SG-22», `SYNTAX.md` §18): das Budget
      (`costs`, `held <=`, `bounded`, `per_pass … ops`) ist Logik am
      Deklarierten; die Frist (`deadline … arch … falsifier …`) ist das
      Hardware-Ergebnis `fortschritt` -- dieselbe Annahme, die `forever`
      traegt, mit ihrer Sonde.
    * Die C-Seite ist unten als GESCHLOSSENE Liste (`CForm`) geschrieben: was
      nie emittiert wird, braucht keine Semantik. Die Absenkung
      (`Absenkung`) erweitert jede Gabbro-Primitive begrenzt; quantitatives
      CompCert erhaelt die `ops`-Zahl von C nach Asm. Wanduhr und Zyklen
      betreten nie die Logik -- sie betreten durch `deadline` und ihre Sonde.

  QUELLE: `dokumente/SYNTAX.md` §18 (vierte Fassung, 2026-09-09).
  KEIN Import aus `crates/`, `programmlogik/`, `passlogik/` oder `Body.lean`:
  `lakefile.toml` laesst das nicht zu -- was hier steht, gilt mit DIESER Syntax,
  gleichgueltig, was der heutige `.rs`-Code tut oder laesst.

  GRENZEN, gemessen am 2026-09-10 (`messung/ZIEL-BEWERTUNG-2026-09-10.md`):
  kein Satz fuehrt `exec`-Spuren in `Gesittet` ueber (die Bruecke steht in
  `Wettlauf.lean` als `lauf_aus_brav`, mit W3-W5 als Prämissen); die gueltige
  sequenzielle Logik unter Verschraenkung (Owicki-Gries-Schritt) steht nirgends;
  die Frist ist hier nur benannt (`fristAlsAnnahme`) -- gemessen wird sie von
  der Sonde (`sonden/sonde_tick.c`, Probenwaehrung, kein Beweis).
-/

import Grammatik.Kern.Syntax.Ziel.T1
import Grammatik.Kern.Syntax.Ziel.T2
import Grammatik.Kern.Syntax.Ziel.T3
import Grammatik.Kern.Syntax.Ziel.T4
import Grammatik.Kern.Syntax.Ziel.T5
import Grammatik.Kern.Syntax.Ziel.T6
