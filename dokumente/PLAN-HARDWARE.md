# PLAN-HARDWARE — die vier Punkte, die Vertrauensbasis und die Verdrahtung

*Angelegt 2026-09-01 auf `f1831fa`. **Jede Zahl hier ist an diesem Stand gemessen**, und
wo eine fehlt, steht das dabei. Der Plan entstand aus einer Durchsprache der vier
hardwarenahen Punkte — MMIO, DMA, Interrupts, Seitentabellen — und hat unterwegs die
Frage verschoben, um die es eigentlich geht.*

---

## §0 — Zuerst die Definition, sonst ist die Frage unbeantwortbar

„Ohne `unsafe`" kann zwei Dinge heißen, und **nur eines davon ist erreichbar.**

**Nicht erreichbar: keine Vertrauensbasis.** Irgendwo endet jede Kette in einer Aussage,
die niemand aus etwas anderem ableitet — dass dieses Gerät an dieser Adresse liegt, dass
diese Speicherart so ordnet, dass der Prozessor das tut, was das Handbuch sagt. Verve, das
genaueste Ergebnis im Feld, hat einen verifizierten Assembler-Nucleus und einen Beweis, der
ihn mit dem Rest verbindet. **Auch dort ist die Basis nicht null — sie ist klein, benannt
und maschinell geprüft.**

**Erreichbar und der eigentliche Inhalt: kein Konstrukt, das Prüfung abschaltet.** Rusts
`unsafe` ist ein Schalter mit unbegrenztem Umfang. Gabbros `assume … falsifier` ist das
Gegenteil: eine einzelne benannte Aussage mit einem Weg, sie umzuwerfen.

> **Der Unterschied ist nicht Sicherheit gegen Unsicherheit, sondern ZÄHLBAR gegen
> UNZÄHLBAR.**

Der Rest ist Arbeit an einer Zahl: wie viele Annahmen, wie groß jede, **wie viele haben eine
Probe, die auf der Architektur läuft, auf der sie brechen könnte.**

### Der Satz, gegen den dieser Plan gemessen wird

> **„Ohne `unsafe`" ist heute wahr in dem Sinn, dass kein Konstrukt Prüfung abschaltet. Es
> ist noch nicht wahr in dem Sinn, dass die Absenkung nicht raten darf. Der Unterschied ist
> zwölf Wildcards weit, und das ist eine Bahn, keine Forschungsfrage.**

---

## §1 — Die Vertrauensbasis liegt nicht, wo sie vermutet wurde

Bis zum 2026-08-31 wurde die `assume`-Liste als Vertrauensbasis geführt. **Das ist falsch,
und die Messung sagt es:**

```rust
fn breite_von(i: &IntTy) -> u32 {          // emit.rs:3447
    U8|I8 => 1,  U16|I16 => 2,  U32|I32 => 4,
    _ => 8,
}
```

**Unter allen vier Hardwarepunkten liegt diese eine Zeile.** Ein `u128`-Register, ein neuer
Ganzzahltyp — und der Erzeuger schreibt still `volatile uint64_t *` auf ein Gerät. Der
Prüfer sagt `0 errors`, `cc -Werror` ist sauber, das Gerät bekommt einen falsch breiten
Zugriff. **Kein Gabbro-Programm kann sich davor schützen.**

> **Die Vertrauensbasis von Gabbro ist nicht die `assume`-Liste, sondern der Erzeuger** —
> ein paar tausend Zeilen Rust ohne Beweis. **Zwölf Wildcards und sechs Verteilerinstanzen
> sind die gemessene Form davon.**

Daraus folgt die Rangfolge von §6: **Punkt 1 bis 4 im Typsystem zu schließen ändert nichts,
solange die Absenkung raten darf.**

### Die zwölf, gemessen (2026-08-31, `eprintln!` statt `panic!`)

```
emit.rs:3488   148 Treffer   1 Fall    (8, false)      gabbro_setz_le64
emit.rs:3510   107 Treffer   1 Fall    (8, false)      gabbro_le64
emit.rs:2410    26 Treffer   1 Fall    Typ(Bool)
emit.rs:1813    21 Treffer   1 Fall    None
zeugnis.rs:758  18 Treffer   5 FAELLE  ElementeVon KetteIn Schlange SlotsVon Threads
domaene.rs:898   8 Treffer   1 Fall    Wahrheit
emit.rs:3690     4 Treffer   1 Fall    I64
emit.rs:3447     —                     `_ => 8` — liefert eine ZAHL, vom String-Grep nicht gesehen
still: fremdverengung.rs:67 · aufrufgraph.rs:825 · zeremonie.rs:826 · m1.rs:4181
```

**Drei Kategorien, nicht zwei** — und das ist die ehrliche Buchung:

| | |
|---|---|
| **1 echter Befund** | `zeugnis.rs:758` — nicht injektiv, s. §5 |
| **6 prospektive Löcher** | tragende Standardzweige, als `_` geschrieben statt benannt. *Falsch wird erst der siebte Fall* |
| **4 Korpuslücken** | „schweigt über 494 Dateien" ist eine Aussage über den **Korpus**, nicht über die Sprache |

**Kein einziges heute falsch erzeugtes Byte.** Ein gutes Ergebnis und ein langweiliges, und
es gehört so gebucht, damit die Arbeit nicht rückblickend dringender aussieht, als sie war.

> *Ausnahme, gemessen am 2026-09-01: der siebte Fall zu `emit.rs:2410` **wurde
> geschrieben**. `0 errors`, und der Erzeuger schreibt `stufe = 0` (`u32 in 1..9`,
> außerhalb des Typs). **Aus prospektiv wird gemessen.***

### Warum die Reparatur billig ist

**Totalität ist in Rust erzwingbar.** `#![deny(unreachable_patterns)]` hilft nicht, aber
jeden Wildcard über einem sprachnahen Enum zu streichen schon.

> **Danach ist jeder neue Sprachfall ein Übersetzungsfehler statt eines stillen Bytes.**

Für `breite_von` reicht Aufzählen nicht: **eine Breite außerhalb der Aufzählung muss `C001`
sein, kein Vorgabewert.** Der Erzeuger sagt an anderer Stelle schon genau so ab, und der
Text steht da: *„the emitter refuses by name instead of emitting something plausible — a
generator that guesses undoes every pass in front of it."*

**Die Absicherung ist vorhanden und Pflicht:** die Gegenrichtung über alle Korpusdateien
muss nach dem Aufzählen byteweise unverändert sein — `pruefe` **und** das erzeugte C, zwei
Binärprogramme. *Kippt eine Datei, war die Zuordnung geraten.*

---

## §2 — MMIO: am nächsten an fertig, und zwei Löcher

### Was steht

```gabbro
device Virtq(kopf : Pa) at dma {
    reg USED_IDX  : u16 wrapping @0x202 class rw in setup, r in live
    reg AVAIL_IDX : u16 wrapping @0x102 class rw
}
```

```c
uint16_t _v = (*(volatile uint16_t *)(d->basis + 16));
(*(volatile uint16_t *)(d->basis + 16)) = (uint16_t)((_v & (uint16_t)~(uint16_t)240u) | …);
```

Feste Adresse, exakte Breite, `volatile` (120 Vorkommen). Und darüber hinaus:

* **`class rw in setup, r in live`**, getragen von `linear ghost type QueuePhase order { setup, live }`.
  *Ein Register, dessen erlaubte Operationen sich mit dem Protokollzustand ändern, und ein
  Prüfer, der den Zustand mitführt.* Adas Representation Clauses legen Layout und
  Volatilität fest, **die Zugriffsrechte sind dort statisch für die Lebensdauer des
  Objekts.** Aus keiner produktiven Sprache ist mir das bekannt. *Das ist ein schmalerer
  Anspruch als „einzige Sprache mit sicherem Hardwarezugriff" — und er hält.*
* **`u16 wrapping`** — der Umlauf steht an der Deklaration, nicht in der Rechnung.
* **„Ein Register wird EINMAL gelesen"** (`beispiele/44`) — die Bindung trägt die Schranke.

### Geprüft und in Ordnung: `~` trägt die Breite

Alle vier Erzeugerstellen schreiben `({c})~({c})…`. Numerisch nachgerechnet:
`(uint16_t)~(uint16_t)240u` = `0xFF0F`, Ergebnis `0xAB3D` — richtig. **Ohne den äußeren
Cast wäre der Zwischenwert `0xFFFFFF0F`** (Integer Promotion nach `int`), und `-Wall
-Wextra` warnt dort meist nicht. **Die Falle ist real und hier nicht offen.**

*Pikant bleibt: der Erzeuger schreibt `~`, die Sprache kennt es nicht (`L006`). Es gibt
also keine Quellzeile, in der die Breite steht — sie kann nur aus dem Kontext kommen.*

### Was fehlt

- [ ] **Die Absenkung muss total sein** — Breite außerhalb der Aufzählung ist `C001`. §1.
- [ ] **`at port` ist abgesagt, nicht gelöst.** *Eine abgesagte Absenkung ist ein Loch im
      Anspruch, kein geschlossener Punkt.* Solange Portzugriffe außerhalb der Sprache
      stattfinden, gilt „MMIO gelöst" **für memory-mapped und nicht für x86-I/O.**
      *(Der Befund davor war schärfer: `at port` senkte `0x3FD` als Speicheroffset ab — „the
      generated C reads RAM. Not a missing instruction: a different instruction on a
      different thing." Heute benannt abgesagt, `0 device … at port` im Korpus.)*
- [ ] **RMW auf ein Gerät ist drei Erzeugerschritte, und die Atomarität steht nirgends.**
      Bei einem Register, das ein Gerät nebenläufig ändert, ist RMW schlicht falsch. Ein
      `modify`-Konstrukt, das **W1C-Register und geteilte Register unterscheidet**, wäre die
      Fortsetzung derselben Idee wie die Phasenklasse.

---

## §3 — DMA: der Kern ist Sichtbarkeit, nicht Kohärenz

### Was steht

Sechs Adressräume im Typ: `normal 312 · mmio 29 · dma 13 · port 6 · code 2 · boot 1`.
Die Eigentumsübergabe an das Gerät ist **`consumes` plus Phasenklasse** — die lineare Marke
schreitet fort, und der Prüfer weiß, wem das Register gehört.

`device … at dma` **senkt nicht ab** und sagt es unter Namen (`C001`): *„Welche Barriere ein
DMA-Zugriff braucht, ist eine Aussage über das Speichermodell, und der Erzeuger baut sie
nicht — er trägt sie unter ihrem Namen."*

### Der Befund: `dma_kohaerent` ist eine Konjunktion mit EINEM Falsifikator

```gabbro
assume dma_kohaerent
    "Ein Traeger im dma-Raum ist kohaerent: Geraet und Kern sehen dieselben Zellen ohne
     Cache-Pflege, und zwei volatile Zugriffe in Programmreihenfolge werden dem Geraet in
     dieser Reihenfolge sichtbar."
    falsifier sonde_dma_reihenfolge;
```

**Zwei unabhängige Behauptungen unter einem Namen:**

1. **Kohärenz** — Gerät und Kern sehen dieselben Zellen ohne Cache-Pflege.
2. **Ordnung** — zwei volatile Zugriffe werden dem Gerät in Programmreihenfolge sichtbar.

**Die zweite folgt nicht aus der ersten, und beide sind architekturabhängig.** Auf AArch64
gilt die Ordnungsaussage für Device-nGnRnE, aber `volatile` in C11 erzeugt dort **keine
Barriere gegenüber normalem Speicher**: ein Deskriptorschreiben in kohärentem RAM und ein
anschließendes Doorbell-Schreiben ins Gerät können ohne `DSB` in falscher Reihenfolge
sichtbar werden. *Der Deskriptor ist normaler Speicher, das Doorbell ist Device-Speicher,
und genau diese Kombination ordnet ARM nicht.*

**Caprock hat beide Architekturen.** Die Annahme ist für x86 wahr und für AArch64 in der
wichtigsten DMA-Konfiguration falsch — **und ihr Text trägt keinen Architekturparameter.**

```
assume = "assume" ident string …        SYNTAX.md:1476   KEIN `arch`
arch kennen: entry · boot · device      23x x86_64, 2x aarch64
```

> **Ein Falsifikator, der auf x86 grün ist, sagt nichts über den Fall, in dem die Annahme
> tatsächlich bricht.**

### Und die Ordnungshälfte ist gar keine Annahme

Sie ist **ableitbar**. Welche Barriere zwischen einem Schreiben in `normal` und einem
Schreiben in `dma` oder `mmio` nötig ist, folgt aus dem Speichermodell der Architektur und
aus **den beiden Adressräumen, die im Typ schon stehen.** Der Erzeuger hat alle Information,
um `DSB ST` bzw. `sfence` selbst zu setzen.

> **Das wäre der Punkt, an dem Gabbro etwas kann, das keine andere Sprache tut: Barrieren
> aus Adressraumwechseln ABLEITEN statt sie anzunehmen.** Die sechs Räume sind die
> Voraussetzung dafür, und sie existieren schon.

### Aufgaben

- [ ] `assume` bekommt einen `arch`-Parameter, wie `entry` ihn hat.
- [ ] `dma_kohaerent` wird zwei Annahmen, jede mit `arch` qualifiziert.
- [ ] **Zählen, wie viele der übrigen `assume` dieselbe Gestalt haben** — eine Konjunktion
      unter einem Namen mit einem Falsifikator für beide Hälften.
- [ ] Barrieren aus Adressraumwechseln ableiten. **Hängt an `assume … arch`.**

### Was Annahme bleiben muss

Dass ein `dma`-Träger überhaupt kohärent gemappt ist — das entscheidet die Seitentabelle,
also §5. **Der Falsifikator muss auf AArch64 laufen, sonst prüft er den Fall nicht, für den
er da ist.**

### Was nicht modellierbar ist

Dass das Gerät den Puffer **nur im vereinbarten Fenster** berührt. Das ist eine Aussage über
fremde Hardware. *`consumes` plus Phase ist die richtige Kodierung der Absicht, ein Beweis
wird es nie.*

---

## §4 — Interrupts: Vertrag vollständig, Rumpf ist C

```gabbro
entry syscall vector 0x80 arch x86_64 {
    regs in  { nr : rax, a0 : rdi, a1 : rsi, a2 : rdx, a3 : r10, }
    regs out { ret : rax, }
    preserves { rbx, rbp, r12, r13, r14, r15 }
    clobbers  { rcx, r11 }
    stack kernstapel per cpu nested never
    dispatch beispiel::eintritt::syscall_verteiler;
}
```

Registerbelegung, Erhaltung, Zerstörung, **welcher Stapel und ob er verschachteln darf** —
als Typ, nicht als Kommentar. `lock … masks irqs` an 8 Stellen.

**Aber `entry` erzeugt einen Prototypen und einen Vektor, keinen Rumpf.** Solange der
Verteiler außerhalb liegt, sind `preserves` und `clobbers` **Behauptungen über fremden
Code.**

- [ ] **Den Rumpf in Gabbro schreiben.** Möglich und nicht besonders schwer — *der
      schwierige Teil, die Registerkonvention, steht schon im Typ.*
- [ ] **Was ein Handler aufrufen darf.** `nested never` regelt Verschachtelung, aber nicht,
      dass ein Handler keine Sperre nimmt, die ein unterbrochener Pfad hält.
      **Der Rangpass kennt Ränge und `masks irqs`, ihm fehlt nur die Regel** — ein
      `entry`-Rumpf darf keine Sperre nehmen, die IRQs nicht maskiert. *Verdrahtung zwischen
      zwei vorhandenen Teilen, s. §7.*

---

## §5 — Seitentabellen: drei Schichten, und die billigste ist die dritte

```gabbro
walk Seitentabelle levels 4 {
    node : [Pte; 512],
    down : rahmen when it.praesent && !it.gross,
    invariant wx_getrennt cost O(n) runs online :
        forall m in mappings of Self : !(m.schreibbar && !m.nx);
}
```

Was das erzeugte C dazu sagt:

```c
/* invariant wx_getrennt runs online -- COMPILE TIME (W6), not re-checked here;
 *   it quantifies over `mappings of`, whose bound is an open finding
 *   about the COST PASS. This descent walks ONE path and claims nothing
 *   about the domain */
```

`walk` trägt **Struktur und Terminierung** (4 Ebenen, 512 Einträge, Abstieg endet durch
Konstruktion). Die Invariante trägt es nicht.

### Der Befund vor den drei Schichten

> **`device … at dma` senkt nicht ab und sagt es unter Namen: `C001`. `walk … invariant …
> runs online` senkt ab, erzeugt Code, und schreibt in einen KOMMENTAR, dass es das
> Versprochene nicht tut.**
>
> Zwei Konstrukte derselben Sprache behandeln dasselbe Versagen verschieden, und nur eines
> davon ist im Prüferprotokoll sichtbar.

- [ ] **`runs online` ohne erzeugte Prüfung ist `C001`.** Kostet nichts, und die Lücke steht
      danach in der Absageliste statt im C-Kommentar — gezählt wie die anderen `H`-Pflichten.

### Schicht 1 — TLB *(billig, real ausnutzbar, kein Beweisanteil)*

W⊕X kann im Speicher gelten und **in einem veralteten TLB-Eintrag verletzt sein** — und
dieser Eintrag ist die Abbildung, die die Hardware tatsächlich benutzt. Zwischen dem
Schreiben eines PTE und dem `invlpg`/`TLBI` existiert ein Fenster; **bei mehreren Kernen ist
es kein Fenster, sondern ein Shootdown-Protokoll.**

**Kein Konstrukt der Sprache nennt es.** Gemessen: `tlb`/`invlpg`/`shootdown` kommen in
keinem Sprachkonstrukt vor.

- [ ] Ein `mapping`-Konstrukt, **dessen Absenkung die Invalidierung selbst erzeugt.** Die
      Regel ist mechanisch: PTE-Schreiben erzeugt `invlpg`/`TLBI`, und für mehrere Kerne
      wird **der Shootdown Teil der Absenkung statt Sache des Aufrufers.**

*Bestes Verhältnis von allen: ein vergessener Shootdown ist ein realer Ausnutzungspfad, und
die Reparatur braucht keine neue Theorie.*

### Schicht 2 — Erhaltung *(mittel)*

**W⊕X ist keine Eigenschaft des Abstiegs, sondern der Änderung.** Erhalten werden muss die
Invariante an jeder Stelle, die einen PTE schreibt.

- [ ] Ein `mapping`-Konstrukt mit der `walk`-Invariante als **Nachbedingung**.

Und die Präzisierung, die die Kosten halbiert:

> **Ein einzelner PTE-Schreibvorgang kann W⊕X nur an dem einen Eintrag verletzen, den er
> schreibt.** Als Induktion geführt statt als globale Aussage braucht die Prüfung keine
> Quantifizierung über die Domäne — **und damit fällt `mappings of` als Kostenproblem für
> diese Invariante weg.**

### Schicht 3 — Selbstbezug *(Forschungsanteil)*

Der Kern verändert die Abbildung, unter der sein eigener Code läuft. **Niemand hat das
gelöst;** seL4 zieht den Schnitt und beweist funktionale Korrektheit unter der Annahme, dass
der Kern gemappt bleibt.

- [ ] Ein Konstrukt, das erklärt, **welcher Bereich unter jeder Änderung unverändert bleiben
      muss** — die ehrliche Kodierung davon.

---

## §6 — Und das Zeugnis ist die zweite Hälfte der Absenkungsfrage

Das Zeugnis soll belegen, **dass das C das Programm ist**. Gemessen am 2026-08-31:

```
traverse t over threads  by unvisited …     6 items, 0 errors, 0 hints
traverse t over queue r  by unvisited …     6 items, 0 errors, 0 hints
                                            Quellen: EINE Zeile Unterschied

gabbro zeugnis  ->  md5 152d61a6…  BEIDE MALE
                    table.induktion   proved   1x  traverse
```

`zeugnis.rs:758` führt `ElementeVon`, `KetteIn`, `Schlange`, `SlotsVon` und `Threads` auf
einem `_ => "traverse"` zusammen.

> **Ein Zeugnis, das zwei verschiedene Programme belegt, belegt keines von beiden.**

Und der Grund, warum das mehr ist als Kosmetik:

> **Ein Zeugnis, das injektiv ist, wäre die eigentliche Absicherung gegen Erzeugerfehler,
> weil es nicht vom Erzeuger abhängt.**

Das Paar liegt als `messung/proben/probe-zeugnis-injektiv-{a,b}.gab` im Baum. Die Heilung
ist **nicht gebaut** — welchen Ausweis jede der fünf Formen bekommen soll, folgt erst aus
dieser Messung.

- [ ] Injektivität bauen, und die Probe so, dass sie es **misst statt behauptet**: das Paar
      muss danach verschiedene Zeugnisse haben, und die Gegenrichtung — zwei gleiche
      Programme geben gleiche Zeugnisse — gehört daneben.

---

## §7 — Das Bauprofil: sechs Instanzen, und es ist ein Prozessbefund

Am 2026-08-31/09-01 ist **sechsmal dieselbe Form** an unabhängigen Stellen gefallen:

| Teil A | Teil B | was fehlte |
|---|---|---|
| `linear ghost` (Griff) | `27-freiliste.gab` | der Zeuge existiert, die Freiliste führt ihn nicht |
| `boot` | `backed` | `bss_nullen(0x2000,0x3000)` = 4 KiB, größtes Feld 16 MiB |
| Prüfer | Erzeuger | `match g { Griff(i) => … }` prüft grün, `C001` beim Erzeuger |
| `gabbro lean` | `umgebung::kandidaten` | `lean` **klebt Text**; der Resolver folgte `use` längst |
| `m2::endet` | `crate::endet_immer` | ein **viertes** Register derselben Dreierliste, andere Semantik |
| `breite_von` | zwei Verteiler | eine Wurzel, zwei Wege, keiner kennt den anderen |

> **Die Teile entstehen einzeln und korrekt, die Verdrahtung entsteht nie — weil sie zu
> keinem Konstrukt gehört und deshalb in keiner Bahn steht.**

**Vier Instanzen sind keine Anekdote mehr, sondern ein Bauprofil.** Die Konsequenz ist
prozessual: **eine Bahn, deren einziger Inhalt „welche zwei vorhandenen Teile wissen nichts
voneinander" ist**, mit derselben Vorabmessung wie jede andere — wie viele Stellen, wie
viele fielen heute. Die sechs oben sind der Startkorpus; **die Zählung sagt, ob es acht sind
oder fünfzig.**

Kandidatenformen für den Zähler, jede mit Begründung:

* **zwei Register über derselben Menge** (W7) — `Return|Leave|Next` steht viermal im Baum.
  *Und die schärfere Frage vor dem Zusammenziehen ist, ob sie dasselbe sagen SOLLEN.*
* **ein Konstrukt beschreibt, ein zweites müsste erhalten** — `walk` gegen PTE-Schreiben,
  `backed` gegen `boot`.
* **Prüfer nimmt an, Erzeuger sagt `C001`** — die vier offenen `H`-Pflichten.
* **ein Angebot, das keine Pflicht ist** — `linear ghost` existiert, zwei Tabellen mit `ops`
  führen es nicht.

---

## §8 — Die Rangfolge, und sie ist nicht knapp

| # | Was | Warum hier |
|---|---|---|
| **1** | **`breite_von` und die zwölf Wildcards** | **liegt unter allen vier Punkten**, und eine Reparatur dort trägt jede spätere Sprachregel. Keine Forschungsfrage. |
| **2** | **TLB / `mapping`** | billig, **real ausnutzbar**, kein Beweisanteil |
| **3** | **Barrieren aus Adressräumen** | die Aussage, **die Gabbro von anderen Sprachen abhebt**. Hängt an `assume … arch` |
| **4** | Sperrregel für `entry`-Rümpfe · `assume … arch` | Verdrahtung, beides vorhanden |
| **5** | Zeugnis injektiv | Absicherung gegen Erzeugerfehler, **unabhängig vom Erzeuger** |
| **6** | Erhaltungsregel (Schicht 2) | Forschungsanteil, aber durch die Induktionsfassung halbiert |
| **7** | Selbstbezug (Schicht 3) | ungelöst, auch bei seL4 |

---

## §9 — Was außerhalb der Sprache bleibt, und das gehört benannt

**Caprocks geteilter Speicher über Capabilities.** Wenn zwei Prozesse dieselbe Seite
schreibbar haben, sagt Linearität nichts — **und kein Konstrukt kann das ändern, weil die
Bedingung stimmt.**

> Der Schnitt ist derselbe wie bei seL4: **geteilter Nutzerspeicher ist außerhalb** — und
> das gehört benannt statt implizit gelassen.

- [ ] Eine Zeile in `BEWEIS.md`, die den Schnitt zieht. *Keine Bahn, eine Zeile.*

Ebenso außerhalb, aus §3: dass das Gerät den DMA-Puffer nur im vereinbarten Fenster berührt.

---

## §10 — Was dieser Plan NICHT ist

Er ersetzt weder `PLAN-VOLLSTAENDIGKEIT.md` (senkt jedes angenommene Programm ab?) noch
`PLAN-VERIFIKATION.md` (was ist bewiesen?). **Er beantwortet eine dritte Frage: wie weit
trägt der Anspruch am Blech**, und wo endet er in einer Annahme statt in einem Beweis.

Und er verpflichtet zu nichts, was nicht gemessen ist. **Jeder Punkt oben mit einem
Kästchen hat entweder eine Zahl daneben oder den Satz, dass sie fehlt.**

---

# TEIL II — Der Wortschatz, und warum er die Beweiskostenkurve ist

*Angefügt 2026-09-01. Derselbe Plan, weil dieselbe Frage: **wo endet der Anspruch in einer
Annahme statt in einem Beweis** — nur diesmal an der Sprache statt am Blech.*

## §11 — Ein Wort ist eine erzeugte Form, und jede erzeugte Form braucht einen Satz

```
Wortschatz (kw.rs)   234 Woerter      C: 32      Ada: 70
Absenkungssaetze     Absenkung_Parametrisch.thy deckt EINE (`ops relabel`)
```

> **Die Beweislast wächst mit dem WORTSCHATZ, nicht mit der Programmgröße.**

Und sie wächst, weil **Totalität mit Vokabular bezahlt wird**: jede neue Rekursionsform
braucht ein neues Konstrukt statt eines Terminierungsbeweises. Das ist der Handel, den
Gabbro überall macht, und er ist bisher nirgends **beziffert**.

- [ ] **Eine Ratsche auf den Wortschatz**, wie der Baum sie sonst überall führt: *ein neues
      Wort nennt entweder das Wort, das es ablöst, oder die Messung, warum keine vorhandene
      Form es trägt.* **Das ist die Zahl, die im ganzen Dokumentensatz fehlt**, während
      `narrow ≤ 24` als Widerlegungsmarke sauber gesetzt ist.

### Ein Kandidat steht in der eigenen Tafel

`by decreasing e` — *„the same walk. The measure is a witness and says nothing about the run
that `unvisited` does not."*

**Es ist ein Beweiszeuge, kein Laufmodus.** Als dritter Modus neben `unvisited`/`consuming`
steht es in der falschen Zone; es gehört zu den **Verträgen**, nicht zum Ablauf.
*Drei Modi, zwei Läufe.*

---

## §12 — Domänen sind der größte Einzelposten

```
ancestors of · chain · child · descendants of · elems of · levels · mappings of
observed · occupied · parent · queue · reaches · sibling · slots of · threads · tree
```

**Siebzehn Wörter**, und *user-defined quantifier domains* existieren ausdrücklich nicht.
Deshalb braucht **jede neue Datenstruktur ein neues Domänenwort.**

> **Es ist kein Zufall, dass `zeugnis.rs:758` als einzige Stelle fünf Fälle hatte:**
> `ElementeVon`, `KetteIn`, `Schlange`, `SlotsVon`, `Threads` sind genau diese Liste.
> §6 und §12 sind dieselbe Sache von zwei Seiten.

**Der Vorschlag ist nicht, benutzerdefinierte Domänen freizugeben** — das öffnet die
Terminierungsfrage wieder. Sondern:

- [ ] **Eine Domäne als deklarierte Erreichbarkeit über einem Tabellenfeld, mit
      Wohlfundiertheitsnachweis an der Deklaration.** *Ein Wort statt siebzehn, ein
      parametrischer Absenkungssatz statt siebzehn einzelner.*

Das ist **dieselbe Bewegung, die `Absenkung_Parametrisch.thy` an der Zielsemantik macht,
nur an der Domänenseite — und sie hat dort schon funktioniert.**

**Nebeneffekt:** `mappings of` bekommt seine Schranke aus derselben Regel statt aus dem
Kostenpass. Damit fällt der offene Kostenbefund aus §5 auch von dieser Seite.

---

## §13 — Die Lemma-Decke jetzt entscheiden, nicht bei Caprock

*„hand-written lemmas"* existieren nicht. **Das ist die riskanteste Entwurfsentscheidung im
Dokumentensatz, weil sie erst bricht, wenn der Korpus groß ist — also spät und teuer.**
Das offene Item sagt es selbst: *ein einziger Fall in der letzten Spalte setzt die Decke
tiefer.*

Die Fluchttür existiert praktisch schon (Kanal A, `pflichten --lean`), **steht aber nicht
als Entwurfsaussage da.**

- [ ] Sie ausschreiben: **keine Lemmata in der Quelle; Pflichten verlassen die Sprache
      BENANNT und werden außerhalb erledigt.** Dann ist die Regel wahr und zugleich keine
      Ausdrucksdecke — **und die 67 abgesagten Pflichten sind eine Reichweitenzahl statt
      einer Niederlage.**

---

## §14 — Keine Parametrizität: gemessen, und die Frage ist erledigt

Cogent hat genau hier verloren — die Sprache blieb sauber, **die Duplikation wanderte in den
Korpus und von dort ins handgeschriebene C.** Die Frage ist also nicht ob, sondern wie viel.

**Gemessen 2026-09-01 über die 77 echten Programmdateien** (ohne `gift/`, `proben/`,
`grammatik/`), `table`/`format` mit mindestens zwei Feldern, Skelett = Folge der Feldnamen:

```
68 Deklarationen        62 verschiedene Skelette
davon MEHRFACH: 5       ('belegt','wert') 3x · Pte 2x · ('benutzt','zaehler') 2x
                        ('kopf','naechst') 2x · FaultRecordHi 2x
```

**Die Duplikation ist klein, und die Mehrfachen sind überwiegend dasselbe Lehrbeispiel in
zwei Dateien.** Ohne die Filter sieht es dramatisch aus — 226 Deklarationen, 34 mehrfache
Skelette, `table { wert }` fünfzehnmal — aber das sind Giftproben und Minimalfälle.
*Der Nenner entscheidet die Antwort, nicht der Zähler (W25).*

> **Monomorphie ist damit richtig, und die Frage ist erledigt** — bis der Korpus wächst.
> Die Messung gehört wiederholt, wenn Caprock ganz übersetzt ist.

---

## §15 — Vier kleine, konkrete

### `w1c` und `rc` stehen unter *Typen* und gehören zu *class*

**Ein Write-1-to-Clear-Register ist keine Zahl mit anderem Typ, sondern ein
Zugriffsverhalten.** Es gehört neben `rw`/`r`.

> **Solange es ein Typ ist, ist ein Read-Modify-Write darauf typkorrekt und falsch — und
> der RMW-Erzeuger baut ihn.**

Das ist die zweite Hälfte des offenen `modify`-Punkts aus §2.

### `progress` und `assume` sind dieselbe Sache in zwei Listen

`forever … progress timer_tick_arrives` ist **eine Umgebungsannahme mit Falsifikator** — und
sie gehört in dieselbe zählbare Liste wie `assume`.

> Sonst hat die Vertrauensbasis **zwei Register über derselben Sache.** Dieselbe Form wie
> W7, und dieselbe wie die vier Register von `Return|Leave|Next` in §7.

### `assume` braucht `arch`

Aus dem AArch64-Grund in §3. **Derselbe Posten, hier nur ein zweites Mal getroffen** — was
für ihn spricht.

### E3 gilt für Programme, nicht für den Übersetzer

Die Sprache hat `exhaustive` als Quellwort und **verbietet Auffangzweige** — und der
Erzeuger hatte zwölf.

> **Das ist keine Ironie, sondern eine Regel, die man anwenden kann: `forbid(unsafe_code)`
> hat ein Geschwister, und es heißt „kein `_` über einem Sprach-Enum".**

- [ ] Nach der Aufzählbahn (§1) als **Lint durchsetzbar** — und dann gilt E3 auch für die
      Werkzeugkette, die E3 durchsetzt.

---

## §16 — Was Teil II an der Rangfolge ändert

Nichts an Platz 1: `breite_von` bleibt unter allem. **Aber §15 letzter Punkt hängt daran** —
die Aufzählbahn macht den Lint erst möglich, und der Lint ist es, der die Reparatur
*dauerhaft* macht statt einmalig.

Neu einzureihen:

| # | Was | Warum dort |
|---|---|---|
| **3a** | **`w1c` von *Typen* nach *class*** | billig, und ein RMW auf W1C ist heute **typkorrekt und falsch** |
| **3b** | `progress` in die `assume`-Liste | ein Register statt zwei, W7 |
| **5a** | **Die Domänenregel** (§12) | löst §6, §12 und die `mappings of`-Schranke aus §5 **auf einmal** |
| **6a** | Wortschatzratsche (§11) | die fehlende Zahl; billig, aber ohne sie wächst der Rest unbemerkt |
| **6b** | Lemma-Decke ausschreiben (§13) | **kostet nichts und verhindert eine späte, teure Entdeckung** |

Und die Messung aus §14 ist **abgeschlossen**: keine Bahn, kein Kästchen, ein Ergebnis.

---

# TEIL III — Gegen SPARK/Ada gehalten

*Angefügt 2026-09-01. **Der Vergleich ist die einzige Weise, die Wette zu beziffern** — und
er liefert vier Anleihen, von denen eine groß ist.*

## §17 — Der Unterschied auf drei Achsen

### Beweisen gegen Unschreibbarmachen

SPARK ist **Allzwecksprache plus Verträge plus SMT-Beweiser**: du schreibst die Eigenschaft
hin, das Werkzeug erledigt sie. Gabbro macht die Eigenschaft zur **Grammatikeigenschaft** —
ein Versatz ohne Länge ist nicht formulierbar.

> **Das sind verschiedene Versagensarten.** Bei SPARK bleibt eine Pflicht **unerledigt und
> du siehst sie**. Bei Gabbro ist die Eigenschaft **unausdrückbar und du verlässt die
> Sprache**: `extern`, `iasm`, `assume`.

### Kosten pro Programm gegen Kosten pro Konstrukt — die eigentliche Wette

SPARK zahlt die Spezifikationslast **in jedem Programm neu**; Gabbro zahlt sie **einmal im
Sprachentwurf**. Aber sie verschwindet nicht:

> **Der Wortschatz IST die amortisierte Spezifikation.** Die Wette geht auf, wenn viele
> Programme wenige Konstrukte benutzen, und sie geht schlecht aus, wenn jedes neue Problem
> ein neues Wort braucht.

Das ist §11 von Ada aus gesehen — **und es ist die Zahl, an der man die beiden Ansätze
tatsächlich vergleichen kann.**

### Absage gegen Abstufung

Ada hat einen **Abstiegspfad**: was SPARK nicht beweist, bleibt eine Laufzeitprüfung und
wird zu `Constraint_Error`. Gabbro kennt das nicht — **entweder die Sprache trägt es oder du
bist draußen.**

> Das ist strenger und **praktisch riskanter**, weil der Ausstieg ins Unverifizierte führt
> statt in eine schwächere, aber noch sichere Form.

Dazu die Asymmetrie aus §1: **Adas Zusage gilt für die Quelle, und GNAT ist qualifiziert.
Gabbros Zusage muss durch den eigenen Erzeuger** — also steht er in der Vertrauensbasis.

---

## §18 — Vier Anleihen, und die erste ist groß

### `Depends` — Informationsfluss statt nur Rahmen

**Die wertvollste Anleihe, und die, die `effects` nicht hat.**

```
effects { reads A, writes B }     sagt WAS BERUEHRT WIRD
Depends => (B => A)               sagt WELCHE AUSGABE VON WELCHER EINGABE ABHAENGT
```

Der Unterschied ist genau der zwischen *„diese Funktion liest den Cap-Space"* und *„dieses
Ergebnis hängt von diesem Slot ab"*.

> **Für einen Capability-Kern ist das nicht Kosmetik.** Nichtinterferenz zwischen Domänen
> ist die Eigenschaft, die Caprock eigentlich beweisen will, und **seL4 brauchte dafür eine
> eigene, große Beweisarbeit oben auf der funktionalen Korrektheit.** Aus Flusskontrakten
> fällt eine schwächere Version davon fast umsonst ab.

- [ ] **Und die Erweiterung ist klein, weil `effects` die Namen schon führt — es kommt ein
      Pfeil dazu.**

### Abgeleitete Typen — und diese Fehlerklasse ist bezahlt

`type Portnummer is new u16` — gleiche Darstellung, **nicht mischbar**.

> **Der `at port`-Fehler war exakt das:** eine Portnummer als Speicherversatz gegeben,
> `0x3FD` auf einen Zeiger addiert.

`index into T` macht das für Tabellen schon; **für Skalare gibt es nichts.** Physische gegen
virtuelle Adresse, Slot-Index gegen Objekt-Index, Zyklen gegen Nanosekunden — alles `u64`
und alles verwechselbar.

- [ ] Billig, **erasure-frei**, und trifft eine Fehlerklasse, die der Baum bereits bezahlt hat.

### Der Abstiegspfad, in Gabbros Form

**Nicht Adas Laufzeitausnahme übernehmen, sondern das Prinzip:** eine Pflicht, die statisch
nicht fällt, wird eine **benannte Laufzeitabsage** statt eines Übersetzungsfehlers oder einer
`assume`. `check` und die Absage-Disziplin sind der Baukasten dafür.

> **Der Gewinn ist, dass der Ausstieg IN DER SPRACHE bleibt und zählbar ist, statt in
> `extern` zu führen.**

### Benannte Beschränkungsprofile

`pragma Restrictions` und Ravenscar sind die Idee, dass **eine Teilmenge einen NAMEN hat**
und ein Programm erklärt, in welcher es liegt.

- [ ] Ein Kernmodul erklärt sein Profil, **und das Zeugnis trägt es** (§6).

---

## §19 — Was NICHT übernommen wird

Adas Sichtbarkeitsregeln, `private`-Teile, Vererbung, Generics in Ada-Form — *das ist die
Komplexität, wegen der niemand die Sprache im Kopf hat.* Und §14 hat gemessen, dass
Parametrizität hier kein Bedarf ist.

Und eine Stelle, an der **Gabbro besser ist und die als solche geführt gehört**:

> `pragma Assume` ist **schwächer** als `assume … falsifier`. **Eine Annahme ohne benannte
> Probe ist eine Annahme, die nie umfällt.**

---

## §20 — Der Test, der beide Ansätze vergleichbar macht

Er steht aus, und er ist präzise formulierbar:

> **Eine Caprock-Struktur in beiden Sprachen, und gezählt wird nicht „geht es", sondern die
> ZEILEN SPEZIFIKATION JE ZEILE ERZEUGNIS.**

Der Eichpunkt ist seL4s **20:1**. SPARK gegen diese Zahl, Gabbro gegen dieselbe.

| Ergebnis | was es heißt |
|---|---|
| Gabbro 3:1, SPARK 12:1 | **die Wette ist belegt** |
| beide bei ~10:1 | eine schönere Sprache **und kein Kostenargument** |

> **Und das zweite wäre ein BEFUND, kein Scheitern.** Es steht hier, damit es beim Messen
> nicht nachträglich zum Scheitern umgedeutet wird — dieselbe Disziplin wie bei jeder
> anderen Zahl in diesem Baum.

- [ ] Struktur wählen, beide schreiben, zählen. **Vor dem Schreiben festlegen, was als
      „Spezifikationszeile" zählt** — sonst entscheidet die Definition das Ergebnis (W25).
