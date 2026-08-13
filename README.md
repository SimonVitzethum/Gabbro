# Gabbro

**Eine Sprache, in der jedes Konstrukt seinen Vertrag mitbringt** — Bereich, Fortschritt,
Wirkungsraum, Vorbedingung, Zustandsübergang, Hardware-Annahme. Wer sie schreibt, hat einen Teil der
Spezifikation schon geschrieben. Der Beweis wird danach von einem **vorhandenen** Beweiser geführt;
Gabbro selbst beweist nichts.

**Welcher Teil — das ist die ganze Frage, und sie hat zwei verschiedene Antworten:**

| Für … | ist erreichbar | weil |
|---|---|---|
| **`format`** | **funktionale Korrektheit** — die These „billig zu beweisen" ist hier verteidigbar | der Beschreiber **ist** die vollständige Spezifikation: das Format *ist*, was der Leser tun muss |
| **alles andere** (`table`, `traverse`, `state`, Kernelcode) | **Sicherheitshülle + deklarierte Invarianten** | Bereich, Terminierung, Rahmen, Überlauffreiheit, erlaubte Übergänge — **nicht**, dass der Rumpf das Richtige tut |

> Der Traversierungskörper `{ if it == s { found } }` ist **Code**. Dass er das Richtige *sucht*,
> steht in keinem Vertrag — und die Linie schliesst allgemeine Nachbedingungen ausdrücklich aus.
> Das ist keine Lücke im Entwurf, sondern sein Preis; es gehört nur hingeschrieben.

Eine Sprache für Formate, Tabellen — und, als ausgesprochenes Fernziel **mit eigenem Tor**, für
Kernelcode. Ausgabe: **C**. Übersetzer in **sicherem Rust** (`forbid(unsafe_code)`).

> **Zwei Berichtigungen stehen bewusst vor allem Weiteren**, und die zweite ist die lehrreichere:
> „per Konstruktion **beweisbar**" war eine Überschreibung — und „Programme, deren **GOLD**-Beweis
> billig ist" war die **nächste**, eine Stufe leiser, entstanden beim Berichtigen der ersten. Der
> Fehler wanderte vom Verb zum Objekt. Beide samt Lehre in [`HISTORIE.md`](HISTORIE.md).

Stand: 2026-08-13. **Nichts davon ist gebaut.** Was gemessen ist, steht als gemessen da; alles
andere ist ausdrücklich Absicht.

---

## Wo was steht

| Datei | Inhalt |
|---|---|
| `README.md` | dies — Zweck, Geltungsbereich, Regeln, Grenzen |
| [`DESIGN.md`](DESIGN.md) | **die Quelle für die Konstrukte** und für das, was jedes einzelne einem Beweiser einbringt |
| [`TODO.md`](TODO.md) | **ausschliesslich Offenes** |
| [`ROADMAP.md`](ROADMAP.md) | Phasen mit **Entscheidungstoren**: jede Phase liefert eine Zahl, die über die nächste entscheidet — samt Abbruchbedingungen |
| [`HISTORIE.md`](HISTORIE.md) | **was an diesem Entwurf schon falsch war**, mit Lehre |

---

## Warum der Name

**Gabbro ist der plutonische Zwilling des Basalts**: dieselbe Zusammensetzung, aber langsam
abgekühlt — deshalb grosse, regelmässige Kristalle statt feinem Gefüge. Genau das tut ein
erzeugendes Werkzeug: derselbe Stoff wie handgeschriebener Code, nur langsam und absichtlich
auskristallisiert. Das Wort ist in Deutsch und Englisch identisch und passt zu Caprock (beides
magmatisch); *Basalt*, der erste Vorschlag, ist bereits von einem Übersetzer belegt.

- [ ] **Nachprüfen, nicht glauben.** Von dieser Maschine aus ist die Namensfreiheit nicht zu
      belegen; „ich habe nichts gefunden" ist ein Nullbefund ohne Grösse. Vor der ersten
      Veröffentlichung eine Suche über Paketregister (crates.io, PyPI, npm), GitHub und
      Sprachlisten — mitsamt dem, was gefunden wurde.

---

## Das Wort „Gold" trägt zwei Bedeutungen, und der Vergleich lief über die Kluft

Die Kennzahl dieses Ordners ist *Zeilen Spezifikation je Zeile Code*: **seL4 rund 20 : 1**
(Isabelle über C), HACL\* in derselben Grössenordnung.

**Nur ist das eine Zahl für volle funktionale Korrektheit.** In AdaCores Übernahmeleiter für SPARK
heisst diese Stufe **Platinum**; *Gold* steht dort eine Sprosse tiefer für „zentrale
Integritätseigenschaften", und *Silber* für Abwesenheit von Laufzeitfehlern. Was die sieben
Konstrukte liefern, liegt zwischen **Silber und Gold in diesem Sinn** — und wurde mit einer
**Platinum**-Zahl verglichen.

- [ ] **Die Leiter nachprüfen, nicht aus dem Gedächtnis zitieren.** Von dieser Maschine aus ist
      keine SPARK-Dokumentation greifbar; die Zuordnung der fünf Stufen ist aus der Erinnerung und
      trägt so kein Argument.

**Die Folge ist keine Wortklauberei, sondern eine Messvorschrift:** solange nicht dasteht, *welche
Stufe* gemessen wird, liefert jedes Verhältnis die Zahl, die man haben wollte. Das Protokoll dafür
steht in [`ROADMAP.md`](ROADMAP.md) als Abbruchbedingung 0b.

---

## Der Riss: `format` und `table` sind NICHT dieselbe Kategorie

**Ein Formatleser ist eine reine Funktion an einer Grenze**: Bytes rein, Struktur oder benannte
Absage raus. Dort ist „per Konstruktion" ein sauberer Begriff — der erzeugte Code ist der
**einzige**, der die Bytes anfasst.

**Eine Tabelle wie der Cap-Space ist MUTIERTER ZUSTAND**, und die Mutation macht handgeschriebener
Kernelcode. Die eigenen Fundstellen zeigen es:

* `refcount -= 1` ohne Bedingung lebt im **Mutations**code, nicht im Prüfer. Ein erzeugter
  `gabbro_capspace_audit` fände den stillen Umlauf **hinterher** — das ist ein besserer
  `audit_cdt`, keine Unformulierbarkeit.
* S1a ist nur dann unformulierbar, wenn **der Traversierungscode selbst erzeugt** ist *und* der
  Kernel gezwungen wird, ihn zu benutzen.

**Damit hängt Phase 4 an einer Frage, die der Sprachentwurf nirgends beantwortet:**

| | Gabbro erzeugt … | Folge | **wo die Invariante laufen kann** |
|---|---|---|---|
| **(a)** | nur den Prüfer | billig und ehrlich — aber der Nutzen ist „`audit_cdt` ohne seine Fehler". **Laufzeitprüfung, nicht Konstruktion.** S1a und S1b fallen als Abnahmekriterien weg, und damit die schärfste Rechtfertigung von Phase 4 | **nur offline/idle** — Diagnostik, kein Schutz |
| **(b)** | Prüfer + Zugriffshelfer | Bereichssicherheit beim Lesen, Mutation bleibt von Hand | ebenfalls nur offline |
| **(c)** | Prüfer + Zugriff + **Mutation** (`insert`/`remove`/`revoke`) | das erzeugte C **besitzt** die Datenstruktur, der Kernel ruft hinein. Ein massiver Schnittstelleneingriff — unter dem Kern-Lock, mit Latenzbudget. **Der Aufwand steht in keiner Phase.** | **inkrementell möglich** — und nur hier |

**Das Kostenmodell entscheidet den Zuschnitt mit; es ist kein unabhängiger offener Punkt.**
Eine vollständige Prüfung von `kind_zeigt_zurueck` ist naiv **O(n · Kettenlänge)** über
80 256 Slots. `colors.rs` hält heute **42 Ticks** unter einer Sperre und gilt deshalb als
Schuldposten — eine Ordnung darüber ist in keinem heissen Pfad denkbar. Es bleiben zwei Auswege:

* **offline/idle prüfen** — dann ist es **Diagnostik, kein Schutz**. Legitim, aber eine *andere*
  Behauptung als die im ersten Entwurf.
* **inkrementell prüfen** — nur, was eine Mutation berührt hat. Das setzt voraus, dass der Prüfer
  das **Delta** kennt, und das Delta kennt **nur der Mutator**.

> **Wer Invarianten im heissen Pfad will, hat den Zuschnitt (c) bereits gewählt — ob er es
> aufgeschrieben hat oder nicht.**

- [ ] **Diese Entscheidung gehört VOR Phase 0.** Denn sie ändert, was Phase 0 überhaupt töten kann:
      **EverParse macht ausschliesslich die `format`-Hälfte.** Liegt der eigentliche Wert bei
      `table` — und dafür spricht viel, denn verifizierte Drahtparser sind ein gelöstes Problem,
      erzeugte Invarianten-Infrastruktur für kernelinterne Tabellen nicht —, dann kann EverParse
      Gabbro **gar nicht erledigen**, sondern nur die halbe Daseinsberechtigung streichen.

### Die Domäne, aus echten Fundstellen

| Muster | wo es in Caprock vorkommt |
|---|---|
| Drahtformat mit Versionskopf | Manifest, Checkpoint, Sidecar, virtio-Deskriptoren, GPT, FAT |
| Tabelle mit Invarianten | Cap-Space + CDT, Seitentabellen, IRTE, DMAR |
| Aufzählung mit Absage | Fehlercodes, `MANGEL_*`, `LocalReason` |

„Fünfmal dasselbe Muster von Hand ist fünfmal dieselbe Falle" — **und genau dieser Satz ist
ungezählt.** Er widerspricht der Messdisziplin, auf die sich dieser Ordner beruft.

- [ ] **Die Basisrate zählen, bevor irgendetwas gebaut wird.** Wie viele Formate hat Caprock
      wirklich? Wie oft ändern sie sich? **Wie viele Fehler dieser Klasse sind pro Jahr
      tatsächlich entstanden** (aus `done.md` auszählbar)? Bei rund sechs stabilen Formaten ist
      einmaliges sorgfältiges Handschreiben plus Differenz-Fuzzing gegen ein Zweitmodell
      wahrscheinlich **billiger** als ein Übersetzer, den man baut *und wartet*.
      **Fällt die Zählung klein aus, ist das ehrlichste Ergebnis dieses Ordners nicht
      „EverParse trägt", sondern „die Falle ist zu selten für eine Sprache".**

---

## Die vier Entwurfsregeln

Jede ist als Antwort auf einen bezahlten Fehler formuliert. Die Konstrukte selbst stehen in
[`DESIGN.md`](DESIGN.md); hier stehen die Regeln und ihre Fundstellen.

### 1. Total per Konstruktion — und „endlich" ist das SCHWÄCHSTE Versprechen

Es gibt **keine unbegrenzte Schleife**, sondern nur Traversierungen mit `over`/`by`/`touches`.

> *Fundstelle:* `migration_candidate` läuft eine Kette `while i != NIL` **ohne Schrittgrenze**,
> während der Prüfer über derselben Kette eine führt. Unter dem Kern-Lock ist ein Zyklus dort ein
> stehender Kern.

Terminierung allein kauft wenig: eine Schleife mit Schrittgrenze **terminiert** und kann trotzdem
ausserhalb der Tabelle indizieren — genau das ist **S1a**. Die Schrittgrenze aus B-5.5 schützt gegen
**Zyklen**, nicht gegen einen Index **ausserhalb**.

### 2. Keine Zeiger — nur Versätze, jeder gegen eine Länge im Geltungsbereich

Ein Versatz ohne die Länge, gegen die er gilt, ist nicht schreibbar. Die Bereichsprüfung entsteht
nicht durch Sorgfalt, sondern weil es keine andere Formulierung gibt.

> *Fundstelle:* `audit_cdt` prüft `parent` gegen `nslots`, liest dann aber `first_child` und die
> Geschwisterkette **ungeprüft**. Mit `panic = "abort"` reisst der Prüfer den Knoten mit — bei
> genau der Anomalie, die er melden soll.

### 3. Abweisen, nie deuten

Eine unbekannte Version, ein gesetztes reserviertes Feld, eine krumme Länge: **benannte Absage**,
je Grund ein eigener Code — nicht ein gemeinsamer Formfehler.

> *Fundstelle:* Eine Prüfung las **ein Byte** des Kernel-Hashes statt 512 Byte zu vergleichen:
> Falsch-Alarm bei 1 von 256 Bauten, **blind bei 255 von 256** echten Überschreibungen.

**Diese Regel hat einen Preis, und er steht bei `by unbesucht`:** ein blosser Schrittzähler würde
einen Zyklus **stillschweigend abschneiden** statt ihn als Absage zu melden — das wäre Deutung. Die
Sprache zwingt damit in die teure Fassung (Bitmap oder Generationsstempel), s. `DESIGN.md`.

### 4. Feste Breiten, ausgesprochene Bytereihenfolge

Kein `usize`, kein Wirtslayout, kein `#[repr]`-Vertrauen. Was auf dem Draht steht, steht im
Beschreiber.

> *Fundstelle:* `MASK_BITS` war nicht die Farbanzahl — auf x86 (256 Farben) zufällig richtig, auf
> aarch64 (16) falsch. Bei 16 Farben bekam Streifen 0 **alle** Farben und die übrigen keine, und
> weil leere Mengen sich nicht schneiden, meldete der Selbsttest „disjunkt".

---

## Warum C — und warum das die Beweisfrage nicht beantwortet

* **Zwei Verbraucher ohne Umweg**: Rust bindet C über FFI, SPARK ebenso.
* **Binärverifikation existiert als Weg**: seL4 beweist den *übersetzten* Code gegen das C.
* **Vorhersagbarer Codegen** — geradliniger Code, keine Halde, keine versteckte Kontrolle.

**Nur: „der Beweis wird von einem vorhandenen Beweiser geführt" nennt bisher drei Wege in einem
Nebensatz, und die drei sind nicht gleich teuer.** Das war eine Drift zwischen Kopf und Rumpf —
`TODO.md` sagt „Rust-Ausgabe erst, wenn C trägt", Ada kommt sonst nirgends vor.

| Weg | was er kostet |
|---|---|
| **Frama-C/WP über dem erzeugten C** | der ehrlichste, weil kein zweites Erzeugnis — aber **ACSL bringt eigene Spezifikationslast mit**, und die zählt in den Zähler. Der schwerste Fall, bisher mit einem „oder" überspielt |
| **Verus über Rust-Ausgabe** | der nächstliegende Beweiser der nahen Zukunft — aber dann gibt es **zwei Ausgaben**, bewiesen wird die eine, ausgeliefert die andere |
| **GNATprove über Ada-Ausgabe** | steht in keinem anderen Dokument dieses Ordners und ist bis auf Weiteres **gestrichen** |

> **Zwei Ausgaben erzeugen eine Entsprechungspflicht, die niemand einlöst.** Bewiesen in Rust,
> ausgeliefert in C — dass beide Emissionen dasselbe tun, ist unbewiesen. Genau diese Lücke schliesst
> seL4 mit Binärverifikation, und sie ist nicht gratis.

- [ ] **Der Beweisweg gehört VOR die Messung von 0b entschieden**, weil er bestimmt, was im Zähler
      steht. Die drei sind nicht unabhängig von der Kennzahl — ACSL erhöht sie unmittelbar.

### Leistung ist ein Entwurfsziel, kein Nachgedanke

* **Keine Allokation** — `(ptr, len)` rein, Struktur des Aufrufers raus.
* **Bereichsprüfungen, die der Übersetzer entfernen kann**, weil jeder Versatz gegen eine Länge im
  Geltungsbereich steht: LLVM sieht den Beweis und streicht die Prüfung, nicht der Mensch.
* **`restrict` an den Parametergrenzen**, aus der Struktur statt als Zusage.
* **Geradlinig statt schleifend**, wo die Länge konstant ist.
* **Messbar, nicht behauptet**: jedes erzeugte Format bringt eine Messzeile mit (Zyklen je Aufruf,
  gegen eine handgeschriebene Referenz). Ohne die Gegenzahl ist „schnell" ein Gefühl.

---

## Der Übersetzer — und der neue Kanal für den Wunschform-Beweis

**In sicherem Rust**, `#![forbid(unsafe_code)]`, ohne Abhängigkeiten ausserhalb einer benannten
Liste — dieselbe Regel, die Caprock für seine Handler-Module durchsetzt. Ein Erzeuger, der selbst
ausbrechen kann, macht die Eigenschaft seines Erzeugnisses wertlos.

SPARK wäre die Alternative und ist **verworfen**: der Übersetzer ist ein Textwerkzeug mit Halde und
Zeichenketten; SPARKs Stärke zahlt sich dort kaum aus, seine Schwäche schlägt voll durch. Beim
*Erzeugnis* liegt es umgekehrt.

> **Der unverifizierte Erzeuger emittiert in dieser Architektur nicht nur Code, sondern auch die
> ANNOTATIONEN, die der Beweiser prüft.** Ein Erzeuger, der versehentlich abgeschwächte Verträge
> ausgibt, produziert einen **grünen Beweis über eine schwächere Aussage** — wörtlich
> „ein Beweis, der die Wunschform beweist". Das ist ein Kanal, den es bei einem reinen Codeerzeuger
> nicht gibt.

Das Gegenmittel steht schon im Werkzeugkasten und muss nur **auf die Annotationen gerichtet**
werden. Die Aufteilung ist scharf, und der dritte Fall ist der, der zählt:

| Mutation im Erzeuger | wer fängt sie |
|---|---|
| **Code** abgeschwächt, Vertrag bleibt | der nachgelagerte **Beweis** fällt |
| **Vertrag** abgeschwächt, Code bleibt | der Beweis bleibt grün — nur eine **Mutationsprobe auf der Annotationsemission** fängt es |
| **beide** stimmig abgeschwächt | **kein Beweis der Welt** — der Code erfüllt seinen (schwächeren) Vertrag. Nur der **Differenztest gegen die handgeschriebene Referenz** sieht es |

Damit hat der Differenztest eine benannte Aufgabe statt der Rolle eines allgemeinen Netzes: **er ist
das einzige, was einen stimmig abgeschwächten Erzeuger fängt.**

---

## Was Gabbro **nicht** löst

* **Falsche Formate.** Gabbro zeigt, dass der Leser dem Beschreiber entspricht — nicht, dass der
  Beschreiber der Wirklichkeit entspricht. Wer die Bytereihenfolge falsch aufschreibt, bekommt einen
  makellosen falschen Leser.
* **Hardware-Zusagen.** `assume`/`falsifier` **benennt** sie und macht sie zählbar; es macht sie
  nicht wahr. Eine bestandene Sonde ist eine Stichprobe.
* **Nebenläufigkeit.** Gabbro beschreibt Daten, nicht Abläufe. „Der Aufrufer hält den Spinlock" kann
  auch SPARK nicht ausdrücken — es ist der grösste Einzelposten des Kernel-Zweigs und dessen Tor.
* **Die Klasse Fehler, die diese Woche wehtat.** Ein fehlendes `US`-Bit auf der Zwischenebene, ein
  Index über den Slot statt über die Identität, eine Wachseite, die einen Farbstreifen sprengt:
  **Fehler über Bedeutung, nicht über Form.** Gefunden hat die alle die Messdisziplin.

---

## Verwandtschaft, und warum trotzdem etwas Eigenes

| Projekt | was es kann | warum es hier nicht reicht |
|---|---|---|
| **F\*/Low\*** | Gold, extrahiert nach C, in HACL\* ausgeliefert | Allzwecksprache — die Spezifikationslast bleibt |
| **Kaitai Struct** | Formate deklarativ, viele Zielsprachen | keine Beweise, keine Absage-Disziplin, kein `no_std`-C |
| **P4, Nail, EverParse** | verifizierte Parser aus Beschreibern | **EverParse ist der nächste Verwandte** und ernsthaft zu prüfen, bevor hier eine Zeile entsteht |
| **Verus / GNATprove** | Beweise auf vorhandenem Code | beweisen, was jemand modelliert hat — und **an genau dieser Abwertung hat sich die eigene Messung gerächt**, s. unten |

**Vor dem ersten Übersetzerlauf gehört EverParse gelesen und gemessen.** Wenn es trägt, ist Gabbro
überflüssig, und das wäre das beste Ergebnis dieses Ordners.

### Der Verus-Vergleich, an der eigenen Messung geprüft

Der naheliegende Schluss lautet: *SPARK fand zwei Fehler, die Verus nicht fand — also bringt eine
eigene Sprache etwas.* **Die eigene Messung stützt das nicht.**

Der Gewinn kam **nicht** aus Adas Sprachvermögen, sondern aus einer **Voreinstellung**: GNATprove
behandelt **jede** Indizierung und **jede** Arithmetik als Beweispflicht. Verus beweist, was jemand
**modelliert** hat — und gemessen steht `refcount` im Verus-Modell als `nat`, kann über
`refcount -= 1` also **nicht einmal die Frage stellen**. Dieselben 15 Stellen sind mit Verus **am
echten Code** erreichbar.

**Die starke Fassung bleibt stehen, und sie ist prüfbar:**

> **Vorgabe schlägt Fähigkeit.** Eine Sprache, in der „alles muss bewiesen werden" die
> **Voreinstellung** ist, erzeugt andere Ergebnisse als eine, in der man es anschaltet — auch wenn
> beide es können.

- [ ] **Messbar statt Ansichtssache:** Verus **am echten Cap-Space**, mit dem Anspruch „jede
      Indizierung, jede Arithmetik". Findet es die 15 Stellen, war es die Vorgabe — und Gabbros
      Beitrag schrumpft auf Ergonomie. Findet es sie nicht, ist das die **erste harte Evidenz**.

---

## Das Fernziel: ein Kernel in Gabbro

Gewünscht ist ausdrücklich, dass man darin am Ende einen **sicheren und schnellen Kernel** schreiben
kann, und dass die **Syntax dafür schwer sein darf**.

**Das ist eine andere These als die oben, und der Widerspruch gehört ausgesprochen:** die Rechnung,
die Gabbro billig macht, ist die **geschlossene Domäne**. Eine Sprache, in der man einen Kernel
schreibt, hat keine — die Spezifikationslast kehrt zurück, und man steht im Gebiet von
**F\*/Low\***.

Es gibt einen Entwurf, der beides trägt, und er hängt am Zugeständnis „die Syntax darf schwer sein":

> **Ein kleiner Kern mit linearen/affinen Typen, Regionen und Totalität als Vorgabe** — und
> `format`/`table` sind **Bibliotheken darüber**, keine zweite Sprache daneben.

**Der Preis ist ehrlich zu nennen:** das ist nicht mehr ein Erzeuger von Wochen, sondern die
ATS-/Low\*-Klasse von Aufwand. Und `Parked` taugt **nicht** als Argument dafür — es zählt dagegen,
s. [`HISTORIE.md`](HISTORIE.md).

### Die Deckungsquote — gemessen, 2026-08-13

Bisher stand hier eine **Liste** dessen, was fehlt. Eine Liste hat keine Grössenordnung. Gemessen
über `kernel/src`, `crates/*/src` und `programs` (Rust, ohne Leerzeilen): **66 651 Zeilen.**

| | Zeilen | Anteil |
|---|---|---|
| **`format` — hart** (`caprock-part` 462, `caprock-fat` 652, `checkpoint.rs` 862) | 1 976 | 3,0 % |
| **`table` — hart** (`space.rs`, Cap-Space + CDT) | 1 105 | 1,7 % |
| **zusammen, hart** | **3 081** | **4,6 %** |
| grosszügig dazu: ELF-/Manifestteil des Laders, DTB, ABI, ACPI-`dmar`, virtio-Deskriptoren | ~2 900 | |
| **Obergrenze, grosszügig gerechnet** | **~6 000** | **≤ 9 %** |

**Und die `table`-Hälfte zählt nur im Zuschnitt (c)**, der nicht entschieden ist. Bei (a) sinkt die
harte Quote auf **3,0 %**.

Was strukturell **ausserhalb** der sieben Konstrukte liegt, im selben Baum gezählt:

| | Fundstellen |
|---|---|
| `Ordering::` (Atomics) | **2 231** |
| `unsafe {` | 482 |
| Rohzeiger `*const`/`*mut` | 403 |
| Sperrnahmen `.lock()`/`.read()`/`.write()` | 406 |
| `asm!`/`naked_asm!`/`global_asm!` | 161 |
| `read_volatile`/`write_volatile` | 125 |

**Die 2 231 Atomics sind die Antwort auf die Frage**, und sie decken sich mit dem, was die Liste
unten schon als grössten Einzelposten führte: 872 davon stehen allein in `threads/mod.rs`. Eine
Sprache, die „der Aufrufer hält den Lock" nicht ausdrücken kann, deckt den Kern des Kernels nicht —
nicht schlecht, sondern **gar nicht**.

> **Ein Rewrite ist damit nicht knapp verfehlt, sondern um eine Grössenordnung entfernt.** Für das,
> wofür Gabbro entworfen ist, deckt es ≤ 9 % — und das ist kein Einwand gegen die Sprache, sondern
> die Bestätigung ihres Zuschnitts. Es ist ein Einwand gegen das Wort *Rewrite*.

### Und die 15,7 %, über die Gabbro gar nichts sagt

`bringup.rs`, `fuzz.rs`, `selftest.rs`, `dmatests.rs` und die drei `*mark.rs`: **10 471 Zeilen,
15,7 %** — Berichts-, Mess- und Selbsttestgerüst. **Das ist der Teil, der die Fehler gefunden hat**,
und er ist mehr als dreimal so gross wie alles, was die sieben Konstrukte hart decken.

Wer einen Rewrite erwägt, rechnet gegen die falsche Grösse, solange dieser Posten nicht danebensteht.

### Was für einen KOMPLETTEN Kernel fehlt

| Was | warum es nicht nebenbei geht |
|---|---|
| **Nebenläufigkeit** | Atomics, Barrieren — und „der Aufrufer hält den Lock", das **weder SPARK noch Rust** ausdrücken kann. Regionen + Fähigkeiten im Typsystem. Der grösste Einzelposten |
| **Volatile/MMIO** | vier Geschmacksrichtungen wie in SPARK (`Async_Readers`/`Writers`, `Effective_Reads`/`Writes`). Machbar, aber Sprachkern |
| **Zwei Adressachsen** | `Pa` und `Iova` getrennt, Arithmetik darauf — `index into` verallgemeinert dorthin, ist aber nicht dasselbe |
| **Bau und ABI** | Multiboot-Kopf, Sektionen, Ausrichtung, ELF32-Abstieg. Kein Sprachthema, muss aber existieren — und hat eine Woche einen halben Tag gekostet |
| **Kein Laufzeitsystem** | kein Allokator, kein Panik-Apparat, kein Abwickeln |
| **FFI** | für HACL\*/EverCrypt — und jede FFI-Grenze **bricht die Garantie** |
| **Beobachtbarkeit** | dieses Projekt lebt von Berichtszeilen. Eine Sprache, in der Formatierung teuer ist, ist hier unbrauchbar |

**Die ehrliche Summe: das ist eine Allzweck-Systemsprache** — ein zweites Projekt, und die Kernthese
(geschlossene Domäne ⇒ Spezifikation billig) gilt für ihn **nicht**.

### Syscalls ohne Assembler — das Vorzeigebeispiel hat die schwächste Deckung

Der Eintritt ist heute Assembler aus **einem** Grund: die CPU übergibt die Kontrolle in einem
Maschinenzustand, den keine Hochsprache zusichert. Ohne Assembler braucht es vier Dinge im
Sprachkern: Eintrittsfunktionen mit **erklärtem Registerabdruck**; **registergebundene Werte**; eine
**eigene Aufrufkonvention** (die Interrupt-Frame-ABI); und **`iretq`/`eret` als Sprachkonstrukt** —
ein typisierter Übergang in einen gespeicherten Kontext, also der `state`-Übergang, angewandt auf
den Maschinenzustand. Das ist die Klasse **typisierter Assemblersprachen** (TAL) und keine Erfindung.

> **Es entfernt das Vertrauen nicht, es VERLAGERT es** — die Instruktionsfolge erzeugt dann der
> Übersetzer statt der Mensch. Der Gewinn ist trotzdem echt: **eine Implementierung statt 153
> Fundstellen, die nie jemand einzeln prüft.**

**Und hier steht das stärkste Wort an der Stelle mit der schwächsten Deckung** — dieselbe Form wie
die zwei Überschreibungen in `HISTORIE.md`, deshalb ausdrücklich:

* „Eine Implementierung, **einmal geprüft**" trägt nur, wenn „geprüft" einen **Prüfer** hat.
* **Der nachgelagerte Beweiser reicht dorthin nicht.** Verus beweist keine Inline-Assembler-Semantik
  und keine Registerabdrücke; Frama-C/WP über erzeugtem C erst recht nicht.
* Ein TAL-Typsystem wäre der Prüfer — dann prüft **Gabbro sich selbst**, und der Erzeuger ist
  unverifiziert. Zirkulär, solange niemand ihn verifiziert.

**Die haltbare Fassung ist deshalb schwächer und immer noch ein Gewinn:** die vertrauenswürdige
Fläche **schrumpft** von 153 Fundstellen auf eine Emissionsstelle. Das ist eine Reduktion, keine
Beseitigung, und sie hat **keinen nachgelagerten Beweiser**.

### Das Tor des Zweigs — mit einem fahrbaren Versuch

Der Zweig war **am weitesten von einer Kennzahl entfernt** und steht deshalb unter „Später,
ausdrücklich nicht jetzt". Er bekommt eine, und sie ist billig:

> **Nimm den schwersten Einzelposten — „der Aufrufer hält den Lock" — und versuche ihn HEUTE in
> Verus auszudrücken.** Ein Nachmittag.
>
> * **Kann Verus es**, verliert der Zweig seine Hauptbegründung — **das billigste Nein, das dieser
>   Ordner bekommen kann.**
> * **Kann Verus es nicht**, ist das die **erste echte Evidenz**.

Dieselbe Logik wie Phase 0 gegen EverParse, nur für den Zweig: *der nächste Verwandte ist gebaut,
der Ordner nicht.*
