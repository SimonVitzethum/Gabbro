# Was Gabbro fuer GOLD fehlt — ausser dem Logikbeweis und der Ausdruckskraft

**2026-08-14.** Zwei Posten sind ausdruecklich **nicht** gemeint: der **Logikbeweis** (den schreibt
der Programmierer, in jeder Sprache) und die **Ausdruckskraft** (dass alle Programme, vor allem
Caprock, hineinpassen — das ist der laufende Rueckstand, s. `FERTIG.md` A3/A5/A6/A7).

**Was bleibt, wenn man beides wegnimmt?** Die Antwort ist unbequem und kurz:

> **Gabbro erzeugt Beweispflichten. Es gibt nichts, was sie erfuellt, und nichts, WORUEBER sie
> sprechen.**

Eine Beweispflicht braucht dreierlei: eine **Sprache**, ein **Modell**, in dem sie einen Sinn hat,
und einen **Beweiser**. Gabbro hat die Sprache — halb. Modell und Beweiser hat es gar nicht.

---

## L1 — Ein MASCHINENMODELL. Der schwerste Posten

`axiom write_cr3(p: Pa) effects { writes tlb, writes active_table }` nennt eine **Wirkung auf einen
Zustand, den es nicht gibt.** Es gibt keinen `tlb`, keine `active_table`, keinen Maschinenzustand —
nur ein Wort in einer Wirkungsliste.

**Damit ist heute nicht sagbar, was ein privilegierter Befehl TUT**, nur dass er etwas anfasst. Ein
Gold-Beweis ueber einem Kernel ist aber im Kern ein Beweis **ueber Maschinenzustaenden**: „nach
`write_cr3(p)` uebersetzt jeder Zugriff nach der Tabelle bei `p`".

| | |
|---|---|
| **Was fehlt** | ein Zustandsraum (Register, TLB, Seitentabellen, Geraetezustand) und je Axiom eine **Uebergangsfunktion** darauf |
| **Warum es nicht „Logik" ist** | der Programmierer beweist ueber *seinem* Programm; das Maschinenmodell ist **unter** ihm und fuer alle Programme dasselbe |
| **Groessenordnung** | seL4 hat dafuer ein eigenes Modell in Isabelle. **Das ist kein Nebenposten, das ist ein Teilprojekt** |

---

## L2 — Ein SPEICHERMODELL. Ohne es kein nebenlaeufiger Gold-Beweis

`atomic X : bool publishes { Y } release;` ist heute eine **Schreibweise ohne Bedeutung.** Was
`release` formal heisst — welche vorherigen Schreibvorgaenge fuer welchen `acquire` sichtbar werden
—, steht nirgends.

**Ohne Speichermodell ist ueber einen nebenlaeufigen Kernel nichts zu beweisen.** Und Caprock ist
nebenlaeufig: **2 231 `Ordering::`-Fundstellen**, davon 872 in einer einzigen Datei.

> **Das ist der Posten, den seL4 UMGANGEN hat**, nicht geloest — der seL4-Beweis ist im Kern
> sequenziell. Wer einen nebenlaeufigen Kernel gold beweisen will, betritt Gebiet, das auch die
> Vorbilder nicht betreten haben.

---

## L3 — Ein BEWEISER. Gabbro erzeugt Pflichten und erfuellt keine

Der Typpruefer erledigt **Klempnerei**. Die **Logik**-Pflichten — `ensures`, `maintains`,
`invariant` — erzeugt Gabbro und **niemand entlaedt sie**.

Frueher stand dafuer „ein vorhandener Beweiser" (Verus/GNATprove/Frama-C). **Mit der Entscheidung
„Ausgabe ist C + iasm, Gabbro prueft selbst" ist dieser Weg zu** — und kein Ersatz benannt.

- [ ] **Zu entscheiden, und es ist eine Richtungsentscheidung:** eigener SMT-Anschluss (Z3/CVC5
      hinter `pred`), oder Ausgabe der Pflichten in ein vorhandenes System (Why3, Isabelle), oder
      doch eine zweite Emission. **Jede Antwort kostet etwas anderes**, und heute steht keine da.

---

## L4 — Die Entsprechung Gabbro ↔ C ist BEHAUPTET

„Syntaxgesteuert und nicht optimierend" ist die Bedingung, unter der die Verfeinerung billig wird.
**Nichts prueft sie.** Der Beweis liegt auf der Quelle, ausgeliefert wird das C — dass beide
dasselbe tun, ist **unbewiesen**, und genau diese Luecke schliesst seL4 mit Binaerverifikation
(eigenes Projekt, steht unter „Spaeter").

---

## L5 — Die eigene TCB ist nicht benennbar

Die Annahmenmenge im Erzeugnis („bewiesen unter A1…An") deckt die **Hardware**. Sie deckt **nicht**:

| | unverifiziert |
|---|---|
| der Gabbro-Typpruefer | ja |
| die Absenkung nach C | ja |
| die **Geistertheorie-Schablonen** (dort lebt die strukturelle Induktion) | ja |
| die Axiomschicht | ja, und sie ist die groesste Flaeche |

**Fuer Gold muss man sagen koennen, worauf man vertraut hat.** Heute kann man es fuer die Hardware
und fuer nichts sonst.

---

## L6 — Der ANFANG fehlt

Ein Beweis beginnt in einem Zustand. **Welcher Zustand gilt, bevor der erste Gabbro-Code laeuft?**
Die Bootphase ist als Marke da (`BootPhase`, linear, `boot_end` bildet `.boot` ab) — aber was
**gilt**, wenn sie verbraucht wird, steht nirgends. seL4 hat dafuer einen eigenen Initialisierungs-
beweis.

---

## Was ausdruecklich NICHT auf dieser Liste steht

* **Lebendigkeit und Fortschritt** — kein Mechanismus adressiert sie, und das ist eine
  ausgesprochene Grenze, kein Rueckstand.
* **Der Logikbeweis** — er ist der Punkt der Uebung, nicht ein Mangel.
* **Die Ausdruckskraft** — sie ist der laufende Rueckstand (19 haengende Klempnerei-Pflichten,
  kein Fragment im Ordner), aber sie war ausgenommen.

---

## Die ehrliche Bilanz

**Vier der sechs Posten (L1, L2, L3, L6) sind jeweils ein Teilprojekt**, kein offener Punkt. L2 ist
zusaetzlich einer, den die Vorbilder nicht geloest, sondern **umgangen** haben.

> **Damit ist die Frage „was fehlt fuer Gold" heute nicht mit einer Liste von Konstrukten zu
> beantworten.** Die Sprache kann die Pflichten **aufstellen**; sie hat weder das Modell, in dem
> sie einen Sinn haben, noch das Werkzeug, das sie entlaedt.
>
> **Das ist keine Widerlegung** — Gabbros Zusage war nie, den Beweis zu fuehren. Es ist die
> Feststellung, dass zwischen „erzeugt gute Beweispflichten" und „Gold" **nicht die letzte Meile
> liegt, sondern der Weg**.

- [ ] **Der billigste Schritt dagegen ist L3, und er ist eine Entscheidung, keine Arbeit:** wohin
      gehen die Logik-Pflichten? Solange das offen ist, ist jede weitere Grammatikregel eine Zeile
      fuer einen Empfaenger, den es nicht gibt.
