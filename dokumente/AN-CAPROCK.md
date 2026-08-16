# An Caprock, nicht an Gabbro

> **Befunde, die in diesem Ordner entstanden sind und deren Gegenstand Caprock ist.**
> Herausgenommen aus [`../TODO.md`](../TODO.md) am 2026-08-16: *eine Aufgabenliste, die zwei
> Projekte führt, sortiert für keines.* **Nicht gelöscht — sie sind Befunde, nur nicht unsere.**
>
> Messbasis durchweg: `SEL4Lake/SEL4Lake` @ `arch/x86_64`, Commit `a1bf707`.

---

## N1 — die zwei Sperrordnungen widersprechen sich · **geklärt, Vorschlag steht**

`kernel/src/system.rs:11–13` führt `… → SCHEDS[*] (R2) → Heap.inner (R3) → MEM (R4,
innerster)` und sagt dazu **„`MEM` hält nie einen weiteren Lock"**. `:724` führt
`CAPS < {EPS[i], NTFNS[i], MEM} < SCHEDS[*] < FP_STATES` — dort hat `MEM` etwas **unter** sich.

**Gemessen (2026-08-15):**

| Frage | Antwort |
|---|---:|
| `MEM`-Halter, die eine andere Sperre nehmen | **0** von 54 |
| Halter äusserer Sperren, die `MEM` nachnehmen | **2** — beide `CAPS` (`space.rs`-Pfad, `system.rs:2495`, `:2509`) |
| Schachtelungen `MEM`/`SCHEDS`, in irgendeiner Richtung | **0** |

> **`MEM` ist Blatt. Der Kopf beschreibt den Code; `:724` ist falsch.**

**Vorschlag** (nicht ausgeführt — Caprock wurde nicht geändert):

```
// Sperrordnung (außen->innen): CAPS < {EPS[i], NTFNS[i]} < SCHEDS[*] < FP_STATES < MEM.
// MEM ist Blatt (R4) und haelt nie einen weiteren Lock -- gemessen: 0 von 54 Nahmestellen.
```

## N2 — welche Atomics sind Ordnungsteilnehmer?

`system.rs:725` führt `FP_OWNER` als **atomares Beiboot** der Sperrordnung: der
Reschedule-Pfad hält `SCHEDS[core]` „+ atomares `FP_OWNER`", und das Atomic ist
**ausdrücklich Teil der Deadlock-Herleitung**.

**Offen:** die Ordering-Vollzählung braucht eine Spalte *„Ordnungsteilnehmer"*. Welche
Atomics das sind, entscheidet, ob sie in die Paarung oder in die Sperrordnung gehören — und
`FP_OWNER` steht heute in **keiner** der beiden dokumentierten Ordnungen, obwohl es in der
Herleitung vorkommt. **Eine dritte Fassung derselben Sache, diesmal unvollständig.**

## K1–K3 — das Ordering-Protokoll um die Wegfälle ergänzen

Es sind **Wegfälle, keine Widerlegungen**:

* **K1** — unter Sperre entfällt das Atomic; ein Teil der 2 231 Fundstellen verschwindet.
* **K2** — Konstruktinneres zählt in die Schablonenfläche statt in die Stichprobe.
* **K3** — `accumulates` mit Verbund ist an `caprock-sync:572-592` **strikt besser als das
  Original**.

## Eager-FP je Architektur oder global

Berichtigt: auf **x86 ist es eager** (`system.rs:1215`, mit genau der CVE-Begründung), **lazy
ist der aarch64-Pfad**. Das Dekret trifft also die andere Architektur, wo das Argument nicht
in derselben Form greift.

> **Blockiert, und nicht aus Zeitgründen:** der einzige aarch64-Baum im Ordner ist **kein
> zweiter Kernel**, sondern ein älterer Schnappschuss derselben Abstammung (`git log --follow`:
> `R099`, Umbenennung mit 99 % Ähnlichkeit). Siehe
> [`MESSUNGEN.md`](MESSUNGEN.md), *Die aarch64-Lücke*.

## Zwei Klempnerei-Pflichten, die offen stehen

Je eine Widerlegung des Kriteriums an ihrer Stelle:

1. `self.queues[p]` nach `31 - leading_zeros()` (`caprock-sched/src/lib.rs:1996`) — braucht die
   **Datenstruktur-Invariante**, um die Indexpflicht zu erledigen. Reine Klempnerei, und heute
   nicht durch Konstruktion lösbar.
2. **Jedes Verfeinerungslemma**, falls die Absenkung nicht flach genug ist.

## Fortschritt / Aushungern (D8)

Fällt unter **keinen** der Mechanismen M1–M4. Offen, ob das so bleibt oder ob es einen
sechsten bräuchte — *aber das ist eine Frage an Caprocks Scheduler-Garantien, nicht an
Gabbros Typsystem.*

---

## Was NICHT hier steht

Die `2 231 publishes`-Stellen und die Basisrate bleiben in Gabbros Listen: sie messen zwar
**an** Caprock, aber sie beantworten eine Frage **über Gabbro** — trägt das Konstrukt die
Last, und ist die Falle häufig genug für eine Sprache. *Der Unterschied ist, wessen
Entscheidung am Ende daran hängt.*
