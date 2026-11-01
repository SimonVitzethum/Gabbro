/-
  Datei:      Passlogik/Bereich.lean
  Gegenstand: Der BEREICHSVERBAND von M1 und die drei Flussregeln V1-V3.

  MODELLIERT WIRD
    Intervalle ueber ganzen Zahlen fester Breite, die abstrakten Operationen des Passes
    (`+`, `-`, `*`, unaeres Minus, Schnitt, Huelle), das Ueberlauf-Kriterium `M104`
    ("passt das gerechnete Intervall in den erklaerten Bereich des Ziels?") und die
    Verengungsregeln V1 (Bereichsbedingung) und V2 (Relation zwischen zwei Stellen).

  QUELLSAETZE
    dokumente/LANGUAGE.md:641  -- `intty = ( "u8"|...|"i64" ) [ "in" range ]`,
                                 `range = expr ".." expr | expr "..<" expr`
    dokumente/LANGUAGE.md:647  -- "Every operation must stay inside the range of its result
                                 type; if `a + b` does not fit the target, that is a
                                 compile error, not a runtime check. Division and remainder
                                 demand a denominator whose range excludes zero."
    dokumente/LANGUAGE.md:651  -- 3.2 "The three flow rules -- closed, local, predictable":
                                 "syntax-directed, without fixpoint, without solver: the
                                 checker keeps a fact set per block that grows only at the
                                 three named places and dies on every write to a
                                 participating place."
    dokumente/LANGUAGE.md:684  -- Tafel V1 / V2 / V3
    dokumente/LANGUAGE.md:685  -- V2: "under the fact `a >= b`, `a - b` has type
                                 `0 .. a.max - b.min`, under `a > b` type
                                 `1 .. a.max - b.min`"
    dokumente/LANGUAGE.md:688  -- ZWEITE VORBEDINGUNG (2026-08-20): eine Stelle durch ein
                                 `device`-Register traegt KEINEN Fakt.
    dokumente/LANGUAGE.md:717  -- VORBEDINGUNG (2026-08-18): der `else`-Zweig setzt
                                 TRICHOTOMIE voraus.
    gabbro paesse --je-satz   -- Satz `m1.bereich`, `v1.bereichsverengung`,
                                 `v2.relationale-verengung`

  ANGENOMMEN STATT BEWIESEN
    (A1) Die Zielbreite wird als Intervall `[lo,hi]` GEGEBEN. Dass `u32` gerade
         `[0, 4294967295]` ist, ist eine Ablesung aus der Lexik und steht hier nicht.
    (A2) Die konkrete Semantik der Rechenoperationen ist die UNBESCHRAENKTE Rechnung
         ueber `Int`. Das ist genau die Modellwahl, die `messung/P6.md`:75 fuer die
         Pflichterzeugung getroffen hat ("Ganzzahlen sind `int`, unbeschraenkt") -- und
         sie ist hier tragend: der Satz `passt_dann_kein_ueberlauf` behauptet, dass die
         MATHEMATISCHE Summe im Zielbereich liegt. Dass die Maschine dann dasselbe
         rechnet, ist eine Aussage ueber den Erzeuger und steht NICHT hier.
    (A3) Stabilitaet einer Stelle (`stabil`) ist ein PRAEDIKAT, kein Beweis. Dass eine
         `device`-Registerstelle instabil ist, liest der Pass aus der Deklaration ab.
-/


module

public import Passlogik.Bereich.Teil1
public import Passlogik.Bereich.Teil2
