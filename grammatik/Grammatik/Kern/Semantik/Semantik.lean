/-
  Datei:      Grammatik/Semantik.lean
  Gegenstand: **Was ein Satz der Grammatik BEDEUTET** -- und der Typ, in dem die Bedeutung
              steht, hat genau zwei Fehlerausgaenge.

    `eval`  -- ein Ausdruck liefert IMMER einen Wert seines Typs. Kein `Option`, kein
               `stuck`: es gibt keinen Fall, in dem die Rechnung nicht weiter weiss, weil die
               Grammatik jeden solchen Fall nicht ableitet (Nenner null, Index ausserhalb,
               Bitoperator auf negativer Zahl, falsche Gestalt).
    `exec`  -- eine Anweisung endet in einem `Ausgang`, und `Ausgang` hat sieben
               Konstruktoren: fuenf Kontrollfluss (`ok`, `zurueck`, `grund`, `leave`, `next`)
               und ZWEI Fehler -- `logik` (eine Klausel des Schreibers gilt nicht) und
               `hardware` (eine Annahme ueber die Maschine gilt nicht). **Einen dritten gibt
               es nicht, weil der Typ keinen hat.** Das ist der Satz; `Satz.lean` schreibt
               ihn hin.

  DIE ZWEI FEHLER, und woher jeder kommt
    `Logik.vorbedingung f`  -- `requires` von `f` gilt an der Rufstelle nicht
    `Logik.nachbedingung f` -- `ensures` von `f` gilt am `return` nicht
    `Logik.invariante i`    -- eine Tabellen- oder Gruppeninvariante gilt am Ende eines Rumpfs
                               nicht, der ihren Traeger schreibt (`maintains`)
    `Logik.schleife`        -- die `invariant` einer Schleife gilt an einer Durchgangsgrenze
                               nicht
    `Logik.abstieg f`       -- die Rekursion kommt nicht zum Ende: das `decreases`-Mass faellt
                               nicht (K009: "DASS es faellt, bleibt Beweisersache")
    `Logik.vorzustand`    -- ein `state`-Uebergang `von -> nach`, aber das Feld stand nicht auf `von`
    `Hardware.annahme a`    -- ein `axiom` (jeder fremde Rumpf) antwortet ausserhalb seines Typs
    `Hardware.fortschritt a`-- ein `forever … progress a` wird von der Umgebung nicht beendet
    `Logik.bereich`         -- a float result left its declared range (was `Hardware.ieee`
                               until 2026-09-15: the kernel IEEE model decides it, no oracle)
    `Hardware.register r`   -- ein Register antwortete ausserhalb seines erklaerten Typs
    `Hardware.geraet r`     -- ein Register antwortete gegen seine erklaerte Zusage (`requires`)
    `Hardware.sichtbarkeit` -- ein `awaits` sah die Veroeffentlichung nicht: das Speichermodell
                               (A10) hat nicht gehalten

  DIE SPUR -- was die Welt ausserdem mitfuehrt (seit 2026-09-09 abends)
    Jeder Zugriff auf einen Traeger schreibt ein EREIGNIS in die Welt: Traeger, Lesen oder
    Schreiben, das statische Λ der Stelle und die dynamisch GEHALTENEN Sperren. `locks L`
    schreibt `nimmt L` und `gibt L`. `Satz.lean` beweist, dass jedes Ereignis seine Waechter
    traegt (`spur_bewacht`); `Wettlauf.lean` schliesst daraus ueber JEDER Verschraenkung
    solcher Spuren, dass zwei Faeden einen bewachten Traeger nie im Wettlauf beruehren.

  WAS DIE SEMANTIK ANNIMMT -- benannt, als Parameter
    (H1) das `Orakel`: was ein `axiom` tut, kommt von aussen. Sein Ergebnis wird gegen den
         erklaerten Typ gehalten (`annahme`); seine WIRKUNG auf die Welt nicht -- dass es nur
         schreibt, was sein `effects` sagt, ist Annahme A_n, wie `SYNTAX.md`:1646 sie bucht.
    (H2) `forever` bekommt seine Durchgaenge von aussen (`fuel`); sind sie verbraucht, ist
         der Ausgang `fortschritt a` -- die Annahme, die der Schreiber am `progress` nannte.
-/

import Grammatik.Kern.Semantik.Semantik.T1
import Grammatik.Kern.Semantik.Semantik.T2
