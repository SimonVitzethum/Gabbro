/-
  Datei:      Grammatik/Satz.lean
  Gegenstand: **DER SATZ**, ueber die GANZE Grammatik, und was neben ihm steht.

  ## Der Satz, in einem Satz

  > Ein Satz der Grammatik hat eine totale Bedeutung, und ihr Ausgangstyp kennt genau zwei
  > Fehler: die Logik des Schreibers und eine Hardwareannahme.

  Der Beweis ist die DEFINITION von `eval` und `exec`: beide sind totale Funktionen
  (`Grammatik/Semantik.lean` uebersetzt), und `Ausgang` hat sieben Konstruktoren. Was hier
  als `theorem` steht, macht das nachpruefbar, ohne die Definition zu lesen:

    §1  `zwei_fehler`          -- jeder Ausgang ist Kontrollfluss, `logik` oder `hardware`
    §2  die Inversionen        -- was die Grammatik an einer Stelle VERLANGT hat
    §3  `exec_gut`             -- ZWEI Saetze in einer Induktion ueber die ganze Grammatik:
                                  der RAHMEN (ein Rumpf schreibt keinen Traeger, den sein
                                  Vertrag nicht nennt) und die SPUR (jeder Zugriff, den ein
                                  Rumpf tut, traegt die Waechter seines Traegers und haelt
                                  dynamisch jede Sperre, die sein Λ nennt). Die Spur ist der
                                  Anschluss an `Wettlauf.lean`: dort steht, dass Faeden mit
                                  solchen Spuren einander nie im Wettlauf beruehren.
    §4  die Sprechproben       -- Saetze, die die Grammatik ABLEITET, ausgewertet

  ## Was der Satz NICHT sagt

  Die Grammatik ist die GANZE Sprache (`Syntax.lean`, Kopf). Was bleibt, sind die drei
  PARAMETER der Bedeutung: das Orakel (H1: was ein fremder Rumpf, ein Register, das
  Speichermodell tut), die Durchgaenge eines `forever` (H2), die Rekursionstiefe (`abstieg`
  ist die Logikstelle `decreases`). *Sie sind die Hardware und die Logik -- genau die zwei,
  die bleiben sollen.* `SYNTAX.md` §16 zaehlt auf, was daraus folgt und was nicht.
-/

import Grammatik.Kern.Syntax.Satz.T1
import Grammatik.Kern.Syntax.Satz.T2
import Grammatik.Kern.Syntax.Satz.T3
import Grammatik.Kern.Syntax.Satz.T4
import Grammatik.Kern.Syntax.Satz.T5
