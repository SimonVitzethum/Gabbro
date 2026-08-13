# Das Kriterium: **nur Logik beweisen, sonst nichts**

**2026-08-13.** Bis hierher war das Ziel eine **Zahl** (0,5 : 1). Sie ist ein Stellvertreter, und
Stellvertreter sind in diesem Projekt eine bezahlte Falle. Das eigentliche Kriterium ist eine
**Art**, nicht eine Menge:

> **Wer ein Gabbro-Programm beweist, beweist die LOGIK seines Programms — und sonst nichts.**
> Alles Uebrige faellt durch Konstruktion.

**Selbst 2 : 1 waere gut, wenn die gezaehlten Zeilen Logik sind.** Und 0,5 : 1 waere ein
Misserfolg, wenn darin Bereichspruefungen von Hand stecken. **Die Zahl wird damit vom Ziel zur
Diagnose.**

---

## Die Trennlinie, und sie muss scharf sein

> **Eine Pflicht ist KLEMPNEREI, wenn ihre Aussage nur die MASCHINE erwaehnt.
> Sie ist LOGIK, wenn sie die SACHE erwaehnt.**

| **Klempnerei — muss durch Konstruktion fallen** | **Logik — die schreibt man, in jeder Sprache** |
|---|---|
| ein Index liegt im Bereich | „der Baum bleibt ein Baum" |
| kein Ueber-/Unterlauf | „der Refcount ist die Zahl der Verweise" |
| kein Alias, keine Ausleihverletzung | „die Nachricht kam beim richtigen Thread an" |
| Rahmenbedingung: was **nicht** angefasst wird | „nach `revoke` hat `s` keine Abkoemmlinge" |
| die Sperre wird gehalten, die Ordnung stimmt | „ein erschoepfter Thread laeuft nicht" |
| kein Datenrennen | „die Faerbung trennt die Mandanten" |
| die Schleife endet, weil die Menge endlich ist | die Schleife endet, weil **der Algorithmus** fortschreitet |
| die Verfeinerung Quelle ↔ C | — |
| die Wohlgeformtheit einer Datenstruktur nach einer **erzeugten** Mutation | die **Formulierung** der Invariante |

**Der Grenzfall ist die Terminierung**, und die Regel entscheidet ihn: „endet, weil ueber eine
endliche Menge gelaufen wird" nennt nur die Maschine — **Klempnerei**. „Endet, weil der Scheduler
Fortschritt macht" nennt die Sache — **Logik**, und sie gehoert hingeschrieben.

---

## Was das mit den vorhandenen Messungen macht

**Die Zahlen bleiben, ihre Lesart aendert sich** — und beide Messungen sind daraufhin **noch nicht
aufgeschluesselt**. Das ist der naechste Papierschritt, nicht eine Behauptung:

| Messung | Zahl | **offen: welcher Anteil ist Logik?** |
|---|---|---|
| `delete_leaf` (Pruefer) | 3,6–6 : 1 ausgeschrieben | Kettenendlichkeit und Indexgrenzen sind **Klempnerei** und muessten fallen; `child_points_back` und `refcount_matches` sind **Formulierungen von Invarianten**, also Logik |
| `Endpoint::call` (Entwerfer) | 1,8–2,3 : 1 | `msg_copied` ist **Logik** und war an nichts gebunden (G2); die fehlende `locks`-Wirkung (G3) ist **Klempnerei**, die gar nicht haette anfallen duerfen |

- [ ] **Beide Messungen nach Logik/Klempnerei aufschluesseln.** Erst dann sagen sie etwas ueber das
      Kriterium. **Eine Zahl ohne diese Aufteilung ist ab jetzt kein Messwert.**

---

## Die Abbruchbedingung wird schaerfer, nicht weicher

Bisher: *„ueber 3 : 1"* — eine Zahl, messbar erst mit Uebersetzer.

**Jetzt:** *„es bleibt eine **benannte** Klempnerei-Pflicht, die der Programmierer von Hand
erledigen muss."*

Das ist **auf Papier je Konstrukt pruefbar** und damit ungleich billiger. Jede solche Stelle ist
entweder ein fehlendes Konstrukt oder das Ende der These.

**Zwei stehen heute schon da, beide aus den Papiertests:**

1. **`self.queues[p]` nach `31 - leading_zeros()`** (`caprock-sched/src/lib.rs:1996`) braucht die
   Datenstruktur-Invariante, um die Indexpflicht zu erledigen. **Reine Klempnerei** — und heute
   nicht durch Konstruktion gedeckt. Entweder M1 traegt sie, oder das Kriterium ist an dieser
   Stelle verletzt.
2. **Die Verfeinerung**, wenn die Absenkung nicht flach genug ist. Sie erwaehnt nie die Sache und
   ist damit per Definition Klempnerei — jedes Verfeinerungslemma ist ein Verstoss.

---

## Warum das Kriterium besser ist als die Zahl

* **Es ist per Konstrukt entscheidbar**, ohne Uebersetzer und ohne Korpus.
* **Es kann nicht durch kurze falsche Zusagen geschoent werden** — der Fund aus
  [`P0-4-GEGENPROBE.md`](P0-4-GEGENPROBE.md) verliert seine Wirkung, weil nicht mehr die **Menge**
  zaehlt, sondern die **Art**. Ein falsches `ensures` ist Logik, die falsch ist; es macht die Zahl
  nicht besser.
* **Es sagt, was Gabbro ist**, in einem Satz, den man widerlegen kann: *alles ausser der Logik
  faellt durch Konstruktion.* Wer eine Klempnerei-Pflicht findet, die haengen bleibt, hat den Satz
  an dieser Stelle widerlegt — und zugleich gesagt, welches Konstrukt fehlt.
* **Es macht die Zahl ehrlich:** 2 : 1 aus lauter Logik ist ein Erfolg. 0,5 : 1 mit
  handgeschriebenen Bereichspruefungen ist keiner.

---

## Was es nicht heisst

* **Die Trennlinie ist eine Entscheidung, kein Naturgesetz.** „Nennt nur die Maschine" ist scharf
  genug fuer die Faelle oben und wird an einem Grenzfall streiten muessen. **Der Streitfall gehoert
  dann hierher, nicht in eine Fussnote.**
* **Es ersetzt die Messung nicht, es ordnet sie.** Ohne Aufschluesselung bleibt jede Zahl das, was
  sie vorher war: ein Stellvertreter.
