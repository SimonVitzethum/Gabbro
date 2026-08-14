# Der Logik/Klempnerei-Split — erstmals gemessen, und er faellt gegen den Entwurf

**2026-08-14.** Zehn handuebersetzte Fragmente aus acht Bereichen, **74 Beweispflichten** einzeln
zugeordnet. Das Kriterium aus [`KRITERIUM.md`](KRITERIUM.md) hatte bis dahin **nie** eine Messung
gesehen.

---

## Das Aggregat

| | |
|---|---|
| Beweispflichten gesamt | **74** |
| **Logik** (erwaehnt die Sache) | 17 |
| **Klempnerei** (erwaehnt nur die Maschine) | 57 |
| **davon bleibt beim Programmierer haengen** | **19 — also 33 %** |
| Logik-Pflichten, die **gar nicht formulierbar** sind | **1** |

**Nach Bereich:** Parser 1/9 haengend, IPC 1/8 — **die halten**. Scheduler + SMP 5, MMU 2 plus ein
Ausdrucksloch. **`programs/` bricht vollstaendig: 4 von 4**, alle an der Dienstschleife von
`virtio-blk`.

> **Damit ist die Zusage „alles ausser dem Logikbeweis faellt durch Konstruktion" an 19 benannten
> Stellen widerlegt.** Nach der Entscheidung vom 2026-08-14 ist das **kein Abbruch, sondern
> Eskalation**: fuer jede der elf Klassen ist das Konstrukt zu entwerfen, das sie abnimmt.

---

## Die drei Verdachtsstellen — alle drei bestaetigt

### `per_pass bounded n cycles` ist ein Ritual

96 Endlosschleifen im Baum. **Fuer acht ist die Zusage nachweislich falsch:** ihr Durchgang enthaelt
einen Ticket-Spinlock ohne Schranke (`crates/caprock-sync/src/lib.rs:821` — **nachgeprueft: der
Crate hat kein `try_lock`, null Fundstellen**) oder Ed25519 ueber ein Manifest beliebiger Laenge.

**Drei Fehler in einem Konstrukt, und alle drei stehen im eigenen Register:**

1. **Gabbro sagt nirgends, ob Sperrwartezeit in `per_pass` zaehlt.** Zaehlt sie, ist die Klausel
   fuer **jede** sperrende Schleife unerfuellbar; zaehlt sie nicht, sagt sie **nichts ueber
   Latenz** — also nichts.
2. **`retry` hat `on_exceeded` als Pflicht, `forever` hat es nicht.** Eine Schranke ohne benannten
   Ueberlauf — **D11 woertlich**: „wer eine Kapazitaet einfuehrt, muss den Ueberlauf BENENNEN".
3. **Das einzige `forever`-Beispiel steht auf `cycles`** — der Groesse, die Caprock bei **D10** als
   unbrauchbar gemessen hat („eine Iterationszahl ist eine Eigenschaft des Programms, eine
   Zeitmessung nicht").

### `publishes` steht an der falschen Stelle

671 Deklarationen. **Die Klausel sitzt an der Deklaration, die Nutzlast entsteht am Store.**

* `FP_OWNER[core]` veroeffentlicht `FP_STATES[<die tid, die es selbst traegt>]` — **selbstbezueglich**,
  und der Kernindex **existiert an der Deklaration nicht**.
* `STALE_STEP.store(2)` veroeffentlicht „in der `senders`-Queue steht ein toter Eintrag" — **kein
  `place`**, sondern eine Aussage.
* **Die sicherheitskritischste Veroeffentlichung im Baum ist gar kein Atomic:** `Queue::publish`
  (virtio-`avail`-Index) ist ein volatiler Store in eine DMA-Region **an ein Geraet**.
* Fuer reine Zaehler gibt es **keine korrekte Schreibweise**: die Prosa sagt „Pflicht", die EBNF
  sagt optional, und `placelist` hat **kein leeres Wort**.

### Eine echte Eigenschaft faellt aus allen sieben Domaenen

**W^X ueber eine zweistufige Seitentabelle** (`crates/caprock-hal/src/x86_64/mmu.rs:1283`, **im
Kernel gefahren**). Die innere Quantifizierung braeuchte eine Domaene ueber einem **dereferenzierten,
gerechneten Zeiger**; `descendants of` folgt der Parent-Relation *einer* Tabelle, und
`reaches … via` ist ein Praedikat, kein Domaenenkonstruktor.

> **Die Ursache liegt eine Ebene tiefer: ein PTE ist zugleich Zeiger UND Bitfeld**, und dafuer hat
> Gabbro kein Konstrukt. Das ist die Wurzel, nicht die fehlende achte Domaene.

---

## Und die Subtraktionsmessung kippt mein `narrow`-Ergebnis

**[`NARROW-GEMESSEN.md`](NARROW-GEMESSEN.md) ist damit ueberholt, und der Fehler ist meiner.**

| | meine Messung | die Gegenmessung |
|---|---|---|
| Korpus | 94 (25 `-=`, 69 `a - b`) | **255** (27 `-=`, 228 `a - b`) |
| flusssensitiv | 4 (`leading_zeros`) | **102** |
| **davon relational** (`if a >= b { a - b }`) | **0** | **54** |

**Entscheidend ist nicht die Zahl, sondern die Form.** Ein `if a >= b { a - b }` ist eine
**Beziehung zwischen zwei Variablen**, und die kann ein Intervalltyp **nicht tragen** — er sagt
etwas ueber *einen* Wert. Die vier `leading_zeros`-Stellen, aus denen ich *„M1 braucht genau eine
Flussregel, keine allgemeine Inferenz"* abgeleitet habe, sind **alle vier einstellig**: meine
Stichprobe enthielt **null** relationale Faelle.

> **Das ist das Hausmuster, angewandt auf mich:** ein Satz, der wahr waere, haette ich den
> Geltungsbereich nicht stillschweigend erweitert. Ich habe aus einer Stichprobe, die die harte
> Form **strukturell ausschloss**, auf alle Faelle geschlossen. **Offener Punkt 1 in `SYNTAX.md`
> geht von `[x]` zurueck auf `[ ]`.**

*Nachgezaehlt: mein engeres Muster ergibt weiterhin 25 und 65. Die Korpusgroesse haengt am
regulaeren Ausdruck; beide Zahlen sind Untergrenzen verschiedener Muster. **An der Form aendert das
nichts** — 54 relationale Faelle sind 54, wie immer man den Nenner zaehlt.*

---

## Zwei Funde, die nicht im Auftrag standen

**`keeping` toetet Falle 4 nicht — es BENENNT sie.** In meinem eigenen `device`-Beispiel ist die
Bitliste falsch: **GCMD-Bit 30 ist `SRTP`** (nachgeprueft: `const GCMD_SRTP: u32 = 1 << 30;`,
`vtd.rs:58`) — ein **Ein-Schritt-Kommando**, kein Zustandsbit. Jedes Kommando haette „Set Root Table
Pointer" neu ausgeloest. Und `IRE`/`QIE`, die Caprock mitfuehren **muss**, fehlen.

> **Der Beleg gegen das Konstrukt ist, dass sein Erfinder es im eigenen Beispiel falsch gefuehrt
> hat.** Die Liste richtig zu bekommen **ist** das urspruengliche Problem; `keeping` verschiebt es
> von der Schreibstelle in die Deklaration. Das ist besser — **einmal statt je Aufruf** —, aber es
> ist Verschiebung, nicht Beseitigung, und genau so gehoert es dazustehen.

**Es gibt kein `break` und kein `continue`.** `breaking` ist das Invariantenkonstrukt; die Liste
„Was es absichtlich nicht gibt" nennt `while`, `for`, `goto` — **`break` nicht**. Vermutlich
versehentlich, und es trifft genau den Fall, den §8 als `forever`-Beispiel fuehrt: **die
Hauptschleife eines Servers**.

---

## Der Streitfall, den die Trennlinie nicht entscheidet

`depleted_count -= 1` ist **Klempnerei** (ein Unterlauf) — aber sie faellt **nur** ueber die
Invariante *„der Zaehler ist die Zahl der erschoepften Konten"*, und die ist **Logik**.

**Hier wird eine Invariante nicht ERHALTEN, sondern BENUTZT**, um eine Bereichspflicht zu erledigen.
[`KRITERIUM.md`](KRITERIUM.md) kennt diesen Fall nicht.

- [ ] **Eine dritte Spalte, oder „faellt durch Konstruktion" wird zur bequemen Buchung.** Vorschlag:
      **Klempnerei, getragen von Logik** — sie faellt, aber **nur so weit, wie die Invariante
      bewiesen ist**. Damit ist sie kein Freibetrag mehr, sondern haengt sichtbar an einem
      Logikposten. *Das ist der erste Streitfall der Trennlinie, und er gehoert hierher statt in
      eine Fussnote.*

---

## Was jetzt zu entwerfen ist — elf Klassen, Eskalation statt Abbruch

- [ ] **`forever` braucht `on_exceeded`** wie `retry`, und eine Aussage darueber, **ob Sperrzeit in
      `per_pass` zaehlt.** Ohne beides ist die Klausel ein Ritual.
- [ ] **`per_pass` in einer anderen Groesse als `cycles`** — D10 hat Zeit als Mass verworfen.
- [ ] **`publishes` an den STORE**, nicht an die Deklaration; eine Form fuer „nichts" und eine fuer
      **volatile Stores an ein Geraet**, die keine Atomics sind.
- [ ] **Ein Konstrukt fuer „Zeiger UND Bitfeld"** (PTE). Daraus folgt die achte Domaene von selbst.
- [ ] **Eine Form fuer relationale Vorbedingungen** (`a >= b`), die ein Intervalltyp nicht tragen
      kann. **Das ist der grosse Posten** — 54 Fundstellen.
- [ ] **`break`/`continue`** entscheiden: aufnehmen oder ausdruecklich verbieten.
- [ ] Die uebrigen fuenf Klassen aus dem Bericht im Scratchpad.
