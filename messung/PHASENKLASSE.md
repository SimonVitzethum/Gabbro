# «B18» — `device` kennt keine Phasen: wo die Phase steht, und woher ein Pass sie kennt

*Entschieden am 2026-08-28, Bahn A, Schritt A1. Jede Zahl nennt den Befehl, der sie
nachrechnet. Gemessen auf `ki-pc-fisch-101:gabbro-A`, Binärprogramm `4dd17209`,
**vor jeder Änderung**.*

---

## 1. Der Befund

`dokumente/PFLICHTEN.md` führt «B18» an **zwei** Korpusstellen (`F4`:785–792 und
`F4`:833–834), und die zweite ist die tragende. Beide Hälften sind mit dem **unveränderten**
Prüfer nachgemessen (W24).

```bash
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/release/gabbro pruefe ~/gabbro-A-w24/a1-phase.gab'
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/release/gabbro pruefe ~/gabbro-A-w24/a1-heimlich.gab'
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/release/gabbro pruefe ~/gabbro-A-w24/a1-voll.gab'
```

| Probe | geschrieben | gemessen |
|---|---|---|
| **A** | die Zeile des Fragments wörtlich: `reg USED_IDX : u16 wrapping @0x202 class rw in Setup, r in Live` | `Fehler: [P026] … im `device`-Rumpf erwartet: mirrors, reg, bank, transition -- `in` gefunden` — **die Form fällt am PARSER** |
| **B** | `impl fn heimlich(q : ptr<dma, rw> Virtq) effects { writes q } costs <= 4 ops { q.USED_IDX = 7; }` — **keine Marke in der Signatur** | **4 Items, 0 Fehler, 0 Hinweise** |
| **C** | dieselbe Ordnung `QueuePhase order { setup, live }`, ein `extern fn queue_arm advances setup -> live`, und ein Rumpf, der **nach** `queue_arm` noch `q.USED_IDX = 1` schreibt | **6 Items, 0 Fehler, 0 Hinweise** |

**Drei Befunde, und der dritte ist der teure.**

1. **A ist ein echter Formmangel**, kein falscher Eintrag. Der Parser kennt nach
   `class regklasse` kein `in` — die Form existiert nirgends, auch nicht halb.
2. **B reproduziert die Berichtigung vom 2026-08-26.** `L101` trägt die Stelle nicht:
   *eine lineare Marke ist eine Erlaubnis, die niemand halten MUSS.*
3. **C ist die Zeile, um die es geht** (`FRAGMENTE.md`:833–834: *„nach `queue_arm` kann kein
   Pfad `USED_IDX` schreiben"*). Der Rumpf hält die Marke, macht den Schritt und schreibt
   **danach** weiter — und der Prüfer sagt kein Wort. *Die Phasenordnung ist gebaut und wird
   an dieser Stelle nicht gelesen.*

Und die Zeile, die eine feste Klasse ausschliesst, steht im Fragment selbst: **`class r`
allein wäre hier falsch** — es verböte genau das Nullen, mit dem der Treiber die bezahlte
Falle einer wiederbenutzten Region entschärft. *Die Klasse ist nicht falsch, sie ist
phasenabhängig.*

---

## 2. Die Formen, gegeneinander — je Form beide Seiten

### Form 1 — die Phase steht am REGISTER

```gabbro
reg USED_IDX : u16 wrapping @0x202 class rw in setup, r in live
```

**Dafür**

* **Kein neues Wort.** `in` ist seit jeher reserviert (`kw.rs`:82), `class` steht schon in
  `regdecl`. `SCHLEIFENINVARIANTE.md` §3: *eine zweite Fundstelle für ein vorhandenes Wort
  ist billiger als ein zweites Wort.*
* **Es ist die Stelle, an der die Klasse schon steht.** «B23» hat 2026-08-20 dieselbe
  Bewegung gemacht — eine Klasse je Feld, am Register, ohne neues Terminal. Der Leser
  (`m3.rs::registerklassen`) sitzt bereits dort.
* **Das Fragment schreibt genau diese Form hin**, als Kommentar, weil es sie nicht schreiben
  kann. Regel A ist damit gemessen und nicht entworfen.

**Dagegen**

* Die Ordnung, aus der `setup`/`live` stammen, steht **anderswo** (`linear ghost type
  QueuePhase order { … }`). Die Zeile nennt Stufen, ohne den Träger zu nennen — die Zuordnung
  muss der Pass finden. *Das ist der Preis und er wird in §3 bezahlt: die Stufennamen müssen
  aus GENAU EINER Ordnung stammen.*

### Form 2 — die Phase steht am GERÄT

```gabbro
device Virtq(basis : Pa) at dma phases QueuePhase {
    in setup { reg USED_IDX : u16 @0x202 class rw }
    in live  { reg USED_IDX : u16 @0x202 class r  }
}
```

**Dafür**

* Der Träger ist genannt (`phases QueuePhase`), die Zuordnung braucht keine Suche.
* Ein Gerät, dessen ganze Registerbank die Phase wechselt, schreibt sich kürzer.

**Dagegen — und diese Zeile entscheidet**

* **Die Registerliste steht zweimal**, und `@0x202` mit ihr. Ein Gerät hat typischerweise
  *ein* phasenabhängiges Register unter zwanzig festen; die Form verlangt, alle zwanzig je
  Phase zu wiederholen, oder einen zweiten Vererbungsbegriff zu erfinden.
* Sie kostet ein **neues Wort** (`phases`) und eine neue Blockform im `device`-Rumpf.
* Zwei Deklarationen desselben Registers an derselben Adresse sind eine Einladung an genau
  den Fehler, gegen den `D2` steht (`N003`, überlappende Lagen).

### Form 3 — die Phase steht an der FUNKTION

```gabbro
impl fn nullen(q : ptr<dma, rw> Virtq) in setup { q.USED_IDX = 0; }
```

**Dafür**

* Die Aufrufstelle liest sich ohne Suche: die Phase steht in der Signatur.
* Kein Rumpfdurchlauf nötig — die Phase ist konstant je Funktion.

**Dagegen — zweimal, und beide Male grundsätzlich**

* **Es ist eine BEHAUPTUNG des Rufers, keine Tatsache.** `in setup` sagt nicht, dass die
  Marke auf `setup` steht; es sagt, dass jemand das glaubt. Um daraus etwas zu machen, müsste
  jede Aufrufstelle geprüft werden — und dann ist der Träger doch wieder die Marke.
* **Es ist ein ZWEITER Mechanismus neben der Ordnung** (W7: zwei Register über einer Sache).
  `phasen.rs` verfolgt die Stufe je Marke durch den Rumpf, mit Zweigeinigung (`O006`) und
  Schleifenverbot. Eine Phase an der Signatur führte dieselbe Auskunft ein zweites Mal, und
  bei Widerspruch entschiede die Reihenfolge im Quelltext.

---

## 3. Die Entscheidung, und der Grund ist der Begriff

**Gewählt ist Form 1: die Phase steht am Register, die Stufen sind die einer schon
deklarierten `order`, und der Pass liest die Stufe aus der Marke — kein zweiter Mechanismus.**

Der Grund ist nicht der Preis, sondern der Begriff: **eine Registerklasse ist eine Aussage
über die HARDWARE, und die Hardware ändert ihr Verhalten mit der Phase.** Die Phase ist damit
ein Merkmal der Klasse, nicht der Funktion und nicht des Geräts. Genau so hat «B23» die
Klasse ans Feld gebracht: nicht weil es billiger war, sondern weil `FSTS` je Feld etwas
anderes ist.

Und die zweite Hälfte der Entscheidung ist die, die «B18»s tragende Stelle schliesst:

> **Wo die Stufe nicht bestimmt ist, gilt, was JEDE Stufe erlaubt.**

Das ist kein neuer Zwang. Es zwingt niemanden, die Marke zu halten — *eine lineare Marke
bleibt eine Erlaubnis.* Es sagt nur, was ohne sie folgt: wer die Phase nicht kennt, darf das,
was in allen Phasen gilt. Für `class rw in setup, r in live` ist der Schnitt **`r`** — und
damit fällt `heimlich` aus Probe B, **ohne dass eine Pflicht erfunden wurde, die Marke zu
führen.**

*Die Alternative — „wer ein phasenklassiertes Register anfasst, MUSS die Marke führen" — wäre
genau der zweite Mechanismus aus Form 3, nur an der anderen Seite. Der Schnitt ist die
schwächere Aussage und schliesst die gemessene Stelle trotzdem.*

**Zwei Rückschlüsse fallen daraus, und beide sind gewollt:**

* Die Vollständigkeit ist Pflicht: **jede Stufe der Ordnung muss genannt sein, genau einmal.**
  Eine ungenannte Stufe wäre ein stilles Loch in einer Regel, deren ganzer Zweck es ist, das
  Loch zu schliessen. *Von streng lässt sich lockern, umgekehrt nie* (K11.1).
* **Neue Kennung nur EINE: `R009`**, und zwar für die **Deklaration**. Die Zugriffsverletzung
  behält `R005`/`R006` und bekommt eine Notiz, die die Stufe nennt — *«B23»s Präzedenzfall,
  wörtlich: dieselbe Regel, eine anders nachgeschlagene Klasse.* Zwei Kennungen für einen
  Begriff wären W7.

---

## 4. Was diese Entscheidung NICHT kauft

* **Sie sagt nichts über die Phase der HARDWARE.** Die Stufe ist die des Treibers; ein
  feindliches oder abgestürztes Gerät verlässt `live` von sich aus, und keine Zeile hier
  hält es. *Aus der Marke eine Tatsache über das Gerät zu machen, wäre der «B33»-Fehler noch
  einmal — derselbe, gegen den «B26» in A2 steht.*
* **Sie prüft keinen Zugriff, der am Gerätegriff vorbeigeht.** Ein `asm`-Block, ein roher
  Zeiger auf dieselbe Adresse, ein `unsafe`-Nachbar: `m3.rs` sagt dort schon heute nichts
  (W9, die Grobheit hat eine Richtung), und das ändert sich nicht.
* **Sie macht die Stufe nicht modulübergreifend genau.** Was `fluss` verfolgt, ist ein Rumpf;
  über eine Rufgrenze hinweg trägt nur die Signatur (`advances`). Eine Funktion **ohne**
  `advances`, die eine Marke im Parameter führt, hat eine **unbestimmte** Stufe — und fällt
  damit unter den Schnitt, nicht unter eine geratene Stufe.
* **Sie prüft einen Schleifenrumpf mit Phasenschritt nicht auf Registerklassen.** Der ist als
  Ganzes schon abgelehnt (`O006`: *ein Schritt geschieht einmal, eine Schleife oft*); ein
  zweiter Befund an derselben Zeile wäre Lärm.
* **Sie senkt nichts ab.** Der Erzeuger sieht die Phase nicht; `class` war noch nie eine
  Absenkung, sondern eine Ablehnung. *Der phasenklassierte Zugriff ist geprüft oder gar
  nicht — er wird nicht anders übersetzt.*

---

## Nachtrag, 2026-09-01 — **Form 3 ist am vierten Tag wiedergekommen, unter einem anderen Namen**

`PLAN-HARDWARE.md` §42 hat vorgeschlagen, den Mechanismus zu einem Wort `phase` zu
verallgemeinern, **anwendbar auf `table`, `ops`, `fn` und `reg`**. Die ersten beiden Träger
haben keinen Wert in einer Signatur, durch den eine Stufe fließen könnte — *damit ist es
genau Form 3 aus §2*, und die Absage dort gilt wörtlich weiter: **eine Behauptung des Rufers
und ein zweiter Mechanismus neben der Ordnung (W7).**

Nachgerechnet in **`messung/PHASENKONSTRUKT.md`**, und drei Zahlen daraus gehören neben §4:

* Der Handel wäre **ein Wort** (`order` + `advances` fallen, `phase` kommt), nicht vier.
* Der versprochene *„EINE Absenkungssatz statt vier"* ist **null statt null** — §4 oben sagt
  es schon, und `emit.rs`:44 sagt die andere Hälfte: *„ghost types (they lower to NOTHING)"*.
* Die sechs Fundstellen von `class … in <phase>` wurden als Posten gezählt. **Sie kosten
  heute nichts** — §2 Form 1 hat das als ihren ersten Vorzug gebucht.

> *Eine Entscheidung, die einen BEGRIFF als Grund hatte, muss ihn beim nächsten Vorschlag
> noch einmal aussprechen — sonst liest ihn jemand als Preisfrage und rechnet ihn nach.*
