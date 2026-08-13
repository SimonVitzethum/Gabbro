# Gabbro für ganz Caprock — und für beliebige Programme

**Was hier geplant wird, und was es kostet, steht vor dem Plan.**

Dieses Dokument verlässt den Zuschnitt, den `README.md` verteidigt. Es plant eine
**Allzweck-Systemsprache**. Damit fällt die Rechnung, die Gabbro billig machte — die geschlossene
Domäne —, und die Spezifikationslast kehrt zurück. **Die Linie wandert**, und `README.md` hat genau
das als den unbequemen Ausgang vorhergesagt: *dann ist Gabbro der Beweisassistent mit Syntax, dem es
ausweichen wollte.*

Die Messung dazu steht und wird nicht schöngeredet: die sieben Konstrukte decken heute **≤ 9 %** von
Caprock, hart **4,6 %**. Dieses Dokument plant die übrigen **91 %**.

> **Die Form ist eine SEHR ENGE Sprache, ungefähr so ausdrucksstark wie C** — nicht ein Katalog aus
> einem Schlüsselwort je Fehlerklasse. Die erste Fassung dieses Dokuments war genau das (zwanzig
> Konstrukte) und ist in §2 berichtigt. **Vier Mechanismen, zwei Deklarationsregeln**; alles andere
> fällt als Bibliothek heraus.

Stand 2026-08-13. **Nichts davon ist gebaut.**

---

## 1. Die Evidenz — 100 bezahlte Fallen, klassifiziert

Ein Plan aus Konstrukten, die jemand für gut hält, ist ein Wunschzettel. Die Konstrukte unten sind
aus der **Basisrate** abgeleitet: den 100 Einträgen der Liste „Fallen, die dieses Projekt bereits
bezahlt hat". Jeder Eintrag ist einzeln klassifiziert in
[`fallen-klassifikation.tsv`](fallen-klassifikation.tsv); die Zahlen unten sind mit
`./zaehle-fallen.sh` **abgeleitet**, nicht danebengeschrieben.

| Klasse | Anteil | heisst |
|---|---|---|
| **S** — Sprache | **36 %** | ein Konstrukt macht es unformulierbar |
| **M** — Messdisziplin | **36 %** | der Prüfer war das Problem, nicht der Code |
| **W** — Werkzeug/Prozess/Bau | **18 %** | CI, git, Cargo, Skripte — **keine Sprache hilft** |
| **B** — Bedeutung | **10 %** | der Beschreiber war falsch — **keine Sprache hilft je** |

**Damit ist die Obergrenze für den Sprachanteil 72 %, nicht 100 %.** 28 der 100 Fallen wären auch in
einer perfekten Sprache genauso passiert.

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

### Was die BIBLIOTHEKSSCHICHT allein deckt — gemessen, 2026-08-13

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

### Der Befund, der den Plan umstellt

Aufgeschlüsselt nach Konstrukt sieht die Verteilung so aus:

| Konstrukt | getötete Fallen |
|---|---|
| **`check`** (Messdisziplin als Konstrukt) | **33** |
| `linear` (echte Linearität) | 5 |
| `device` (Registerbeschreiber) | 5 |
| `assume`/`falsifier` | 3 |
| `lock`, `region`, `wirkung`, `einheit`, `grundmenge`, `absage`, `ableitung`, `stellentyp`, `arithmetik` | je 2 |
| `state`, `atomic`, `barrier`, `bitfeld`, `platzierung`, `menge`, `recht` | je 1 |

> **Das wertvollste Konstrukt einer Gabbro-Vollversion ist keine Typsystem-Eigenschaft.**
> Es ist die **Messdisziplin dieses Projekts, in die Sprache gezogen** — und sie tötet mehr Fallen
> (33) als alle Typkonstrukte zusammen (S = 36, verteilt auf zwanzig Konstrukte, das grösste mit 5).

Das passt zu der anderen Zahl, die beim Messen anfiel: **15,7 % von Caprock sind Berichts-, Mess-
und Selbsttestgerüst**, und das ist der Teil, der die Fehler gefunden hat. Keine vorhandene Sprache
— nicht Rust, nicht SPARK, nicht Verus, nicht F\*, nicht ATS — sagt darüber irgendetwas.

**Wenn dieser Ordner eine Daseinsberechtigung als Vollsprache hat, dann hier.** Alles andere ist
Nachbau von Vorhandenem.

---

## 2. BERICHTIGUNG: die erste Fassung war eine Merkmalsliste, keine Sprache

Sie führte **zwanzig** Konstrukte — `device`, `lock`, `atomic`, `barrier`, `bitfeld`, `einheit`,
`menge`, `recht`, `platzierung`, `grundmenge`, `ableitung`, `stellentyp`, `absage`, `region`,
`linear`, `wirkung`, `state`, `arithmetik`, `check` … — eines je Fehlerklasse. Das ist die
naheliegende Ableitung aus einer Fallenliste und der falsche Schluss: **eine Sprache, die für jeden
bezahlten Fehler ein Schlüsselwort bekommt, ist ein Katalog.** Sie wächst mit jedem Fund, und
niemand kann sie mehr im Kopf halten.

Gefragt ist das Gegenteil: **eine sehr enge Sprache, ungefähr so ausdrucksstark wie C**, aus deren
wenigen Mechanismen die zwanzig als **Bibliothek oder Deklaration** herausfallen.

> **Gabbro = C ohne seine Löcher, plus zwei Dinge.**
> Die zwei sind **Bereichstypen** und **lineare Werte (auch geisterhafte)**. Alles andere ist eine
> **Einschränkung** von C, keine Erweiterung.

---

## 3. Der Kern — vier Mechanismen und zwei Deklarationsregeln

### M1 — Bereichstypen

Ganzzahlen tragen ihren **Wertebereich**, und jede Operation muss darin bleiben. Das ist Adas
Trick, und **genau er** hat S1a/S1b gefunden — nicht „Ada ist sicherer".

```gabbro
type SlotIdx  = u32 in 0 .. NSLOTS-1
type Refcount = u32 in 0 .. u32'max
type Zyklen   = u64 in 1 .. u64'max      -- Null ist ein Befund, kein Messwert
```

### M2 — Lineare Werte, auch geisterhafte

Ein linearer Wert **muss** verbraucht werden; ein geisterhafter existiert nur im Beweis und wird
vor der Codeerzeugung gelöscht (**kein Byte, keine Halde** — an Verus gemessen).

```gabbro
linear       type Parked                 -- muss zugelassen werden
linear ghost type Hält(CAPS)             -- Sperrbeleg, kostenlos
linear ghost type Pflicht(check)         -- eine unerfuellte Pruefzusage
```

### M3 — Adressräume und Zugriffsrechte am Zeiger

Ein Zeiger trägt **wohin** er zeigt und **was** man damit darf. C hat das als Erweiterung; hier
ist es die Voreinstellung.

```gabbro
ptr<mmio, write_only>   gcmd            -- ein Lesen zum Zurueckschreiben ist nicht schreibbar
ptr<dma,  read_write>   puffer
ptr<code, execute@ring3> sonde
```

Barrieren gehören zum Adressraum, nicht zur Architektur — `dsb sy` gegen `dmb ish` ist keine
Stilfrage mehr, sondern folgt aus `mmio` gegen `normal`.

### M4 — Kein ungeprüfter Index, keine unbegrenzte Schleife

Indizieren geht nur mit einem Beleg der Zugehörigkeit; jede Schleife nennt ihr Abstiegsmass.
`traverse` ist die bequeme Schreibweise dafür, kein eigener Mechanismus.

### D1/D2 — die zwei Deklarationsregeln

* **Undurchsichtige Neutypen ohne implizite Umwandlung.** `Pa`, `Iova`, `Farben`, `MaskenBits`
  sind verschiedene Typen — C's `typedef` ist durchsichtig, das ist das Loch.
* **Vollständige Layouts, kein Auffangzweig.** Jedes Bit eines Wortes ist benannt, jede Aufzählung
  ist erschöpfend.

### Was C hat und bleibt

Funktionen, Zeiger, `struct`, feste Breiten, Kontrollfluss, Funktionszeiger, explizite Umwandlung
zwischen **verträglichen** Typen. **Was wegfällt:** implizite Umwandlung, `void*`, Zeigerarithmetik
ohne Grundlage, `goto`, Auffangzweige, `union` als Umdeutung (das kann M3), Präprozessor.

---

## 3b. Die zwanzig fallen heraus — als Bibliothek, nicht als Syntax

**Das ist der Test der Reduktion.** Bleibt eine Zeile ohne Ableitung, fehlt ein Mechanismus.

| vormals „Konstrukt" | folgt aus | wie |
|---|---|---|
| `einheit` (Pa/Iova/Farben) | **D1** | undurchsichtiger Neutyp |
| `arithmetik` (S1b) | **M1** | `Refcount` verlässt seinen Bereich nicht |
| `absage`, `grundmenge` | **D2** | erschöpfende Aufzählung, kein Auffangzweig |
| `bitfeld` (Marke auf Bit 63) | **D2** | vollständiges Layout — das Zahlenfeld ist belegt |
| `menge` statt Kardinalzahl | Bibliothek | ein Feldtyp über M1 |
| `ableitung` | `const`-Auswertung | hat C auch, nur ohne Prüfung |
| `stellentyp` (Konstruktor je Stelle) | **M2** + Modulgrenze | undurchsichtig, ein Erzeuger |
| `recht` (lesen ≠ schreiben) | **M3** | zwei Zeigerrechte, nicht eine Zeile mit zwei Richtungen |
| `device`, Registerklassen | **M3** + **D2** | `mmio` + `write_only` + vollständiges Layout |
| `barrier`-Domäne | **M3** | folgt aus dem Adressraum |
| `platzierung` (`.user_text`) | **M3** | `code`-Raum mit `execute@ring3` |
| `region`, Eigentum | **M2** | ein linearer Block ist seine Region |
| `linear` (`Parked`) | **M2** | der Mechanismus selbst |
| `state` (Typzustand, x2APIC) | **M2** | linearer Wert, dessen Typ den Zustand trägt |
| `lock` / `held(L)` | **M2** | `linear ghost Hält(L)` — an Verus **gemessen**, dass das trägt |
| Sperr**ordnung** ⇒ Deadlockfreiheit | **M2 + M1** | die Stufe ist ein Bereichstyp, Nehmen verlangt echt kleinere Stufe |
| `atomic`-Veröffentlichung | **M2** | `release` gibt einen Geisterbeleg ab, `acquire` nimmt ihn |
| `wirkung` (Global/Depends) | **M2** | Wirkungen **sind** geisterhafte Fähigkeiten im Parameter |
| `traverse` (S1a) | **M4** | Schreibweise, kein Mechanismus |
| `format` / `table` | Bibliothek | Deklarationen über M1/M3/D2 |
| **`check`** | **M2** | **s. u. — die schönste Ableitung** |

### Die vier alten Entwurfsregeln — sie sind jetzt ABLEITUNGEN, keine Regeln

Regel 1 ist **M4**, Regel 2 ist **M1 + M4**, Regel 3 ist **D2**, Regel 4 ist **D1 + D2**. Sie
stehen hier weiter, weil ihre **Fundstellen** die Evidenz sind — jede ist ein bezahlter Fehler.

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

### `check` ist keine Sonderform, sondern eine lineare Pflicht

Das Konstrukt mit den 33 getöteten Fallen braucht **kein eigenes Schlüsselwort**:

* Ein `check` erzeugt ein `linear ghost Pflicht`. **Wer sie nicht verbraucht, übersetzt nicht** —
  das ist wörtlich „ein `check`, der in keiner Gatterliste steht, ist ein Fehler" (Falle 17, und
  das `all_done()`-Loch 21 gegen 24), und es fällt aus M2 heraus statt aus einer Sonderregel.
* Die **Sprechprobe** ist eine zweite Pflicht, die nur ein *fehlgeschlagener* Lauf verbraucht.
* Die **Untergrenze** ist M1: eine gemessene Grösse mit `in 1 ..` kann nicht null melden.
* „Der gemessene Pfad schreibt die Grösse selbst" ist ein **Schreibrecht** — M3.

**Damit bleibt die These dieses Ordners bestehen und wird kleiner:** das Wertvollste ist nicht ein
Prüf-Schlüsselwort, sondern dass **Prüfzusagen dieselben linearen Werte sind wie Ressourcen.**

---

## 3c. Wie ein GOLD-Beweis billig wird — der Kern der These

Gold heisst funktionale Korrektheit, und **Gabbro beweist sie nicht.** Die Frage ist, wo seL4s
**20 : 1** hingehen und welchen Teil davon eine Sprache wegnehmen kann. Drei Posten, und nur der
erste ist unantastbar:

| Posten | wer ihn trägt | nimmt eine Sprache ihn weg? |
|---|---|---|
| **Die abstrakte Spezifikation** — *was* soll der Kernel tun | der Mensch | **nein, nie.** Das ist die Aussage selbst |
| **Invariantenerhaltung** — jede Mutation erhält jede Invariante | der Beweis, und das ist der grösste Posten | **ja** |
| **Verfeinerung** — abstrakt → ausführbar → C, über drei Sprachen (Isabelle/Haskell/C) mit einer Naht an jeder Grenze | der Beweis | **grösstenteils** |

### Das Wort „Gold" trägt zwei Bedeutungen

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

### M-Gold-1 — Invarianten an der Struktur, Mutationen erzeugt

Der Invariantenposten ist gross, **weil jede handgeschriebene Mutation gegen jede Invariante
gezeigt werden muss.** Wird die Mutation aus Struktur + Invariante **erzeugt**, fällt der Beweis
**einmal je Operation im Erzeuger** an statt einmal je Aufrufstelle.

**Das ist der Zuschnitt (c) — und er hat damit erstmals einen Grund jenseits der Ergonomie.**
Die alte Notiz „der Aufwand steht in keiner Phase" gilt weiter; neu ist, dass die Alternative
(handgeschriebene Mutation) den teuersten Posten des Gold-Beweises **behält**.

### M-Gold-2 — syntaxgesteuerte, NICHT optimierende Absenkung

Die Verfeinerung Quelle → C ist billig, wenn die Absenkung **flach und strukturerhaltend** ist.
Das ist Low\*s Anordnung, und es ist der Grund, warum „nicht optimierend" hier eine **Bedingung**
ist und keine Einschränkung.

**Der Preis steht daneben:** Optimierung findet danach statt, im C-Übersetzer, und die ist dann
**nicht** Teil der Zusage. Wer Leistung *und* eine flache Verfeinerung will, verschiebt das
Vertrauen zu LLVM — dieselbe Grenze, an der seL4 die Binärverifikation ansetzt.

### M-Gold-3 — Spezifikation und Implementierung in DERSELBEN Sprache

seL4 zahlt an **jeder Naht** zwischen Isabelle, Haskell und C. Gabbro hat zwei Ebenen und keine
Naht:

```gabbro
spec fn cdt_wohlgeformt(c: CapSpace) -> bool      -- mathematisch, nicht ausfuehrbar,
    = forall s: c.eltern_kette(s) endet in Wurzel  -- keine Ressourcengrenzen

impl fn delete_leaf(c: &mut CapSpace, s: SlotIdx)
    erhaelt cdt_wohlgeformt                        -- die Verfeinerungspflicht wird ERZEUGT
```

**Das ist die eigentliche Antwort auf „macht seL4-Beweise leicht":** nicht, dass Gabbro beweist,
sondern dass es die **drei Sprachen zu einer macht** und die Verfeinerungspflicht selbst aufstellt.

### Die Vorhersage — und sie korrigiert das eigene Ziel nach unten

**≤ 1 : 1 war für `format` gesetzt**, wo der Beschreiber die vollständige Spezifikation *ist*.
**Für einen Kernel ist der Boden die abstrakte Spezifikation**, und die nimmt niemand weg.

> **Ehrliche Vorhersage: 20 : 1 → etwa 0,8 : 1** — Herleitung unten. Eine frühere Fassung sagte
> hier **5 : 1**; sie behandelte den Beweisaufwand als unteilbar und maß gegen den falschen Nenner.

- [ ] **Verfehlt Gabbro 2 : 1 deutlich, ist die Gold-These widerlegt**, und übrig bleiben
      Zusage 1 (Speichersicherheit) und 2 (Rennfreiheit). Das wäre **immer noch** mehr als heutiges
      Rust — aber es wäre nicht *„macht seL4-Beweise leicht"*.

### Was < 1 : 1 verlangen würde

> **BERICHTIGUNG (2026-08-13, wenige Stunden nach der ersten Fassung).** Hier stand eine Rechnung
> mit dem **falschen Nenner**: Spezifikationszeilen gegen die *handgeschriebene Rust-Referenz*.
> Rust ist hier irrelevant — es geht um einen Kernel, der **in Gabbro geschrieben** und dann
> verifiziert wird. Der Nenner ist **Gabbro-Code**. Die falsche Fassung kam zu „für Caprock als
> Ganzes: nein"; mit dem richtigen Nenner lautet die Antwort **bedingt ja**, und die Bedingung ist
> benennbar. *(Die frühere Fassung hatte eine eigene Berechtigung — als Frage „lohnt der Umstieg",
> nicht als Frage „ist der Beweis billig". Zwei Fragen, ein Bruch.)*

### Die Zählregel muss zuerst stehen, sonst misst sie nichts

**Das eigentliche Problem dieser Kennzahl in Gabbro:** viele Konstrukte sind **beides** —
eine Bereichsangabe, ein `device`-Block, ein `over`/`by` sind Spezifikation *und* Programm. Wer sie
als Code zählt, bekommt eine glänzende Zahl ohne Aussage; wer sie als Spezifikation zählt, eine
schlechte.

> **Regel: Spezifikation ist, was KEINE Laufzeitwirkung hat** — was der Übersetzer vor der
> Codeerzeugung löscht. Alles, was im erzeugten C ankommt, ist Code.

Sie ist die einzige, die sich nicht durch Umschichten von Text gewinnen lässt:

| zählt als **Spezifikation** (gelöscht) | zählt als **Code** (im C) |
|---|---|
| `spec fn`, Invarianten, `requires`/`ensures` | `device`-Blöcke (sie erzeugen die Zugriffe) |
| Schleifeninvarianten, Abstiegsmasse | `format`-Beschreiber (sie erzeugen Leser/Schreiber) |
| `linear ghost`-Werte, Sperrbelege | gewöhnliche Funktionsrümpfe |
| `touches`, Verfeinerungsannotationen | Bereichs**prüfungen**, die stehen bleiben |

**Zwei Wege, sie trotzdem zu schönen** — beide gehören in das Protokoll:
* **Prüfen statt beweisen.** Wer eine Eigenschaft zur Laufzeit prüft, statt sie zu beweisen,
  verschiebt Zeilen von oben nach unten. Das ist kein Betrug — es ist ein **anderes Programm**,
  langsamer, und genau das wird ausgeliefert. Die Zahl bleibt ehrlich, wenn die Laufzeitmessung
  danebensteht.
* **Geschwätziger Code.** Deshalb wird in **Anweisungen** gezählt, nicht in Zeilen.

### Der Boden ist nicht 5 : 1 — er ist die abstrakte Spezifikation, und die ist klein

Die 20 : 1 von seL4 sind **kein einzelner Posten**. Aufgeteilt (Zahlen aus dem Gedächtnis,
Grössenordnung, s. offener Punkt):

| | ungefähr | nimmt Gabbro es weg? |
|---|---|---|
| **abstrakte Spezifikation** — *was* der Kernel tut | rund **0,5 : 1** | **nein, nie** |
| **Beweis** — dass der Code sie erfüllt | rund **19,5 : 1** | **darum geht es** |

**Damit ist der Boden ≈ 0,5 : 1 und nicht 5 : 1.** Meine frühere 5 : 1-Vorhersage stammt aus
derselben Verwechslung wie der Nenner: sie behandelte den Beweisaufwand als unteilbar.

- [ ] **Die seL4-Aufteilung nachprüfen**, nicht aus dem Gedächtnis zitieren. Sie trägt hier ein
      Argument. Von dieser Maschine aus ist keine Quelle greifbar.

### Was auf null muss — und was nicht kann

| Beweisposten | in Gabbro | Zeilen |
|---|---|---|
| Speichersicherheit, Bereichs- und Überlauffreiheit | **M1 + M4**, im Typ | **0** |
| Rahmenbedingungen, Nichteinmischung | **M2**, Wirkungen als Fähigkeiten | **0** |
| Datenrennen, Sperrdisziplin, Protokollphasen | **M2** | **0** |
| **Invariantenerhaltung** — der grösste Posten bei seL4 | Mutationen aus Struktur + Invariante **erzeugt** (Zuschnitt (c)) | **nahe 0** |
| **Verfeinerung Code ↔ Spezifikation** | syntaxgesteuerte Absenkung, `spec`/`impl` in **einer** Sprache | **nahe 0** |
| **Funktionale Korrektheit algorithmischer Rümpfe** | IPC-Fastpath, Scheduler, `revoke` | **NICHT null — hier bleibt echte Arbeit** |

> **< 1 : 1 ist erreichbar, wenn die ersten fünf Posten wirklich auf null gehen** — dann bleibt die
> abstrakte Spezifikation (≈ 0,5) plus die funktionalen Beweise für den sicherheitskritischen Kern.

**Die Überschlagsrechnung, mit ausgesprochenen Annahmen:** braucht etwa ein Zehntel des Kernels
funktionale Korrektheit (Fähigkeitssystem, IPC, die Autoritätsteile des Schedulers — in Caprock
grob 5–8 kZeilen von 66,7 k) und kostet dieser Teil 5 : 1, während der Rest nur seine
Spezifikation trägt (≈ 0,3), dann liegt das Mittel bei etwa **0,8 : 1**.

**Das ist eine Rechnung, keine Messung**, und sie hängt an drei Annahmen, die alle falsch sein
können: der Anteil, der Faktor 5, und dass die ersten fünf Posten tatsächlich null werden. **Die
dritte ist die riskanteste** — „nahe 0" bei Invariantenerhaltung setzt Zuschnitt (c) voraus, und
der ist unentschieden.

### Die drei Bedingungen, ohne die es nicht geht

1. **Die Deklaration IST die Annotation.** Wer `device` schreibt *und* Invarianten *und*
   Beweishinweise, hat drei Zähler statt einem.
2. **Die Absenkung muss flach bleiben.** Jedes Verfeinerungslemma ist eine Zeile im Zähler, und
   sie wachsen schnell.
3. **`revoke` muss in den Konstrukten ausdrückbar sein** — sonst bleibt die gefährlichste Mutation
   handgeschrieben, und mit ihr kehrt die Invariantenerhaltung als Beweisposten zurück. Der
   Papiertest entscheidet damit nicht nur den Zuschnitt, sondern **die Kennzahl**.

- [ ] **Die billigste Prüfung, ohne Übersetzer: EIN Modul zweimal auf Papier** — als Gabbro-Quelle
      und mit dem, was ein Beweiser darüber hinaus bräuchte. `space.rs` ist der richtige Fall, weil
      es beides enthält: beschreibende Struktur **und** algorithmisches `revoke`.

## 3c-bis. Der Zuschnitt (a)/(b)/(c) — er entscheidet die KENNZAHL, nicht nur den Nutzen

> **Neu gewichtet:** solange die Mutation handgeschrieben bleibt, kehrt die Invariantenerhaltung
> als Beweisposten zurück — und mit ihr fällt die 0,8 : 1-Vorhersage. Der Zuschnitt ist damit
> keine Nutzenfrage mehr, sondern die **Voraussetzung der Kennzahl**.

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

---

## 3d. Rennfreiheit — jetzt einzuplanen, sonst nie

**Datenrennen fallen aus M2 + M3 heraus** (Eigentum und Zugriffsrechte). Das ist der gelöste Teil,
und Rust kann ihn heute.

**Protokollrennen nicht — und die sind die teuren.** Der Beleg steht im eigenen Register:

> **D0 war KEIN Datenrennen.** `spawn()` reihte ein, `bind_pd()` kam danach; jeder Zugriff war
> ordentlich synchronisiert, kein Rust-`unsafe`, kein fehlender Atomic. Der Fehler war, dass ein
> Thread **erreichbar** wurde, bevor er Autorität hatte. Rate **0,018 %**, zehn Tage Suche, und
> **jeder** Datenrennen-Prüfer der Welt hätte geschwiegen.

| Klasse | Beispiel aus dem Register | fällt aus |
|---|---|---|
| **Datenrennen** | ungeschützter gemeinsamer Zugriff | M2 + M3 — gelöst, auch in Rust |
| **Sichtbarkeit vor Fertigstellung** | **D0** (lauffähig vor `bind_pd`) | **M2**, wenn die Phase ein **linearer Wert** ist: `Parked` → `admit`. Genau so wurde D0 auch tatsächlich behoben |
| **Verlorenes Wecken** | **Z24** (ein Bit für vier Gründe) | **M2**: der Wecker verbraucht **genau seinen** Grund; eingereiht wird nur bei leerer Menge |
| **Veröffentlichung ohne Nutzlast** | Loom sah die Nutzlast nicht (Falle 33) | **M2**: `release` gibt einen Geisterbeleg ab, `acquire` nimmt ihn |
| **Fortschritt / Aushungern** | **D8** (erschöpfter Thread) | **gar nicht.** Kein Mechanismus adressiert Lebendigkeit — das gehört ausgesprochen |

**Warum es jetzt in den Entwurf muss und nicht später:** wenn Phasen und Sperrbelege lineare Werte
sind, steht das in **jeder Signatur**, die geteilten Zustand anfasst. Nachträglich eingeführt heisst:
jede dieser Signaturen ändert sich. Das ist dieselbe Lehre wie „ein Umbau, der einen neuen Zustand
einführt, muss jede Stelle mitnehmen, die über Zustände urteilt" — dort waren es 61 Aufrufstellen.

---

## 3e. Unsicherer Bootcode — mit BEWEIS, dass er danach nie wieder läuft

Ein Kernel braucht ihn: rohe Physadressen, bevor die MMU steht; Multiboot-Strukturen; die
Kern-Übergabe. Die Forderung ist nicht „möglichst wenig `unsafe`", sondern **„`unsafe`, aber
nachweislich abgelaufen"** — und das ist strikt stärker als alles, was Rust heute kann.

**Es fällt aus M2 heraus, ohne neuen Mechanismus:**

```gabbro
linear ghost type Bootphase              -- genau EINE Instanz, beim Eintritt erzeugt

roh fn phys_schreiben(p: Pa, w: u64) benoetigt &Bootphase
roh fn mb_info_lesen(p: Pa) -> Info      benoetigt &Bootphase

fn boot_ende(t: Bootphase)               -- VERBRAUCHT die Marke; es gibt keine zweite
    entfernt code<boot>                  -- ... und bildet .boot im selben Zug ab
```

**Zwei Ebenen, und die zweite ist der eigentliche Gewinn:**

| | Aussage | wie |
|---|---|---|
| **statisch** | keine `roh`-Funktion ist nach `boot_ende` aufrufbar | die Marke ist **linear**, nicht affin — sie lässt sich nicht kopieren und nicht wiederherstellen. **Genau das kann Rust nicht** (affin) und Verus' `tracked` auch nicht |
| **strukturell** | der Code ist danach **nicht mehr da** | `boot_ende` verbraucht die Marke **und** bildet den `boot`-Codeabschnitt ab — ein Ereignis, nicht zwei. Ein wilder Sprung dorthin faultet |
| **prüfbar** | die Behauptung ist falsifizierbar | Sonde nach dem Boot auf eine `.boot`-Adresse: **muss** faulten. Das ist `falsifier`, und ohne ihn wäre „ist weg" eine Behauptung |

**Dass es beide Ebenen sind, ist der Punkt.** Nur statisch hiesse „kein Aufrufer" — und das eigene
Register kennt die Gegenprobe: **Falle 47**, ein Abschalter für eine Sicherheitseigenschaft wird
gesetzt und nie zurückgenommen. Eine Eigenschaft, die daran hängt, dass niemand eine Funktion ruft,
ist eine Bitte. Eine, deren Code **abgebildet** ist, ist eine Zusicherung.

- [ ] **Aus der Basisrate ist dieser Punkt NICHT abgeleitet** — er kommt aus der Anforderung. Die
      100 Fallen enthalten keine Instanz „Boot-`unsafe` später benutzt"; die nächstverwandte ist
      Falle 47. **Das gehört gesagt**, sonst sieht eine geforderte Eigenschaft aus wie eine
      gemessene.

---

## 3f. Was Kernel-Logik AUSSERDEM verlangt — und wo das Vertrauen sich sammelt

„Alle Kernel-Logik ausdrückbar" ist eine Vollständigkeitsforderung, und sie hat eine Liste. M1–M4
decken sie **nicht** allein.

| Was | Antwort | ehrlich dazu |
|---|---|---|
| **Absichtliche Nichtterminierung** (Leerlauf-, Hauptschleife) | `divergent fn` — **ausgesprochen**, nie versehentlich | M4 verlangt sonst ein Abstiegsmass; die Ausnahme muss benannt sein, nicht erschlichen |
| **Unterbrechbarkeit** | eine **Wirkung**: `unterbrechbar` / `maskiert`. Ein Handler ist kein Aufruf — er kann zwischen zwei beliebigen Anweisungen laufen | fällt aus M2, wenn die IRQ-Maske ein linearer Beleg ist. Falle 93 (Guard über den Rumpf) ist genau das |
| **Kontextwechsel** | Sprachprimitiv `wechsle(von: &mut Kontext, zu: &Kontext)` mit Vertrag über den Maschinenzustand | Stapelwechsel ist in **keiner** strukturierten Sprache ausdrückbar. Das ist der `state`-Übergang auf Maschinenebene — und er wird **emittiert**, nicht geschrieben |
| **Privilegierte Befehle** (`mov cr3`, `wbinvd`, `sti`, `invlpg`, `tlbi`) | eine **Axiomschicht**: je Befehl ein erklärter Effekt auf das Maschinenmodell | **Hier sammelt sich das Vertrauen, und es ist irreduzibel.** Jedes Axiom ist ein `assume` — mit `falsifier`, wo einer fahrbar ist |
| **Code als Daten** (der Lader) | `code`-Raum ist nur über ein **Prüftor** erreichbar (Signatur, Layout) | Caprock macht das bereits; neu ist, dass der Weg dorthin der **einzige** ist |
| **Sprungtabellen** (Syscall-Verteiler) | Funktionszeiger mit vollständiger Signatur, Tabelle erschöpfend (D2) | — |
| **Ausrichtung und Layout** | Teil des Typs, nicht des Übersetzers | — |

#### Ergänzend: die Posten, die M1–M4 gar nicht berühren

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

> **Die ehrliche Summe: M1–M4 + Axiomschicht + drei Primitive** (`divergent`, `wechsle`, Prüftor).
> Die Axiomschicht ist die grösste unbewiesene Fläche der ganzen Sprache — grösser als der
> Übersetzer —, und sie ist **zählbar**: eine Ratsche über der Menge der Axiome, die nur fallen darf.

### Was NICHT herausfällt — und darum ehrlich danebensteht

| | |
|---|---|
| **Verträge** (`requires`/`ensures` über deklarierte Prädikate) | nötig für Falle 1/2 (Bedingung über Registergrenzen). Damit ist die Linie gewandert, wie `README.md` vorhergesagt hat — und **allgemeine Quantoren über Rechenausdrücke bleiben trotzdem draussen** |
| **Der Eintritt (Assembler)** | M1–M4 sagen nichts über Registerabdrücke. **Neu seit der Zielsetzung „C + iasm": er ist Teil der AUSGABE**, also aus einer Beschreibung emittiert statt je Fundstelle geschrieben — vertrauenswürdige Fläche **eine Emissionsstelle statt 161**. Bewiesen ist er weiterhin nicht, und er tötet **0** bezahlte Fallen |
| **Fortschritt** (Aushungern, D8) | kein Mechanismus adressiert ihn |

## 3g. Was Gabbro wie SPARK könnte — und was besser

Beides ist gemessen, nicht geschätzt: zwei SPARK-Experimente am Cap-Space und am Scheduler, dazu
das Verus-Tor vom 2026-08-13.

### Wie SPARK — und M1/M2 liefern es strukturell

| SPARK-Stärke | in Gabbro |
|---|---|
| **Jede Indizierung, jede Arithmetik ist Pflicht** — der Grund, aus dem S1a/S1b fielen | **M1**: Bereichstypen. Es ist keine Voreinstellung, die jemand umlegen kann, sondern der Typ |
| `Global`/`Depends` — **63 von 63** Datenabhängigkeiten bewiesen | **M2**: Wirkungen sind geisterhafte Fähigkeiten im Parameter |
| **Abdeckungsratsche** (34 von 34 unter `SPARK_Mode => On`, kein `Off`) | die Ratsche über der **Axiommenge** — dieselbe Mechanik, anderer Gegenstand |

### Besser als SPARK — fünf Punkte, jeder an einer gemessenen Schwäche

| | SPARK heute | Gabbro |
|---|---|---|
| **Linearität ohne Allokation** | „leak **proved**" ist SPARKs stärkster Einzelpunkt — **hängt aber an einer Allokation** (gemessen, und der Preis steht in Caprocks Register) | **M2**: geisterhafte lineare Werte, vor der Codeerzeugung gelöscht. **Kein Byte, keine Halde** — an Verus gemessen. Strikt besser auf SPARKs eigenem Feld |
| **„Der Aufrufer hält den Lock"** | **keine Ausdrucksform** — bleibt ein Kommentar | **M2**: linearer Geisterbeleg. Verus kann es heute, was zeigt, dass es geht |
| **Adressräume, MMIO-Rechte** | vier Volatilitätsvarianten, aber kein `write_only`-Register, kein Adressraum, keine Barrierendomäne | **M3** — und damit vier bezahlte Fallen (1, 2, 4, 5) unformulierbar |
| **Terminierung** | Silber verlangt sie **nicht** | **M4**: Pflicht. Genau die Lücke I5, die im eigenen Verus-Modell offen war |
| **Bootphase mit Ablaufbeweis** | gibt es nicht | **M2 + M3**, zweistufig, falsifizierbar (§3e) |

Dazu der Unterschied, der keine Sprachfrage ist: **SPARK prüft vorhandenen Code, Gabbro erzeugt
ihn** — deshalb fällt die Invariantenerhaltung einmal je Operation an statt je Aufrufstelle (§3c).

### Schlechter als SPARK — und das entscheidet die Praxis

* **Reife.** GNATprove ist über Jahrzehnte automatisiert und industriell zugelassen (DO-178C).
  Gabbro hat nichts davon, und der Verus-Lauf hat gezeigt, wie teuer Unreife wird: vier Abstürze,
  eine versiegelte Schnittstelle, fehlende Spezifikationen für Iterator-Adapter.
* **SPARKs Leckprüfung feuert von selbst.** Gabbros muss es erst zeigen — „geht im Prinzip" ist
  bei einem Prüfer die schwächste aller Aussagen.
* **Ein einziger Datenpunkt je Behauptung.** Zwei Experimente sind keine Erhebung.

## 4. Was auch dann nicht besser wird — 28 %

| | | Beispiel |
|---|---|---|
| **W (18)** | Werkzeug, Bau, Prozess | `.git/info/exclude`; `grep -q` unter `pipefail`; ein CI-Gate im Format des falschen Servers; zwei Suiten, die dasselbe Gerät verschieden aufsetzen |
| **B (10)** | Bedeutung | „unten zuerst" war ein Zufall der Grössenrelation; der Lader meldet seinen eigenen Speicher als frei; eine Ablage je Rolle |

Dazu die Hardware: `assume`/`falsifier` macht Annahmen **zählbar**, nicht wahr.

**Ein Rewrite, der 100 % erwartet, rechnet mit 72 % — im besten Fall, bei perfekter Umsetzung
jeder Stufe.**

---

## 4b. AUSGELÖST 2026-08-13: Abbruchbedingung 2 hat für M2 gegriffen

Die Gegenrechnung „was können Rust + Verus + Loom heute schon?" ist für den schwersten Posten
gefahren, und sie ist **gegen** diesen Plan ausgegangen.

| Stufe | gemessener Stand gegen Verus/Rust heute |
|---|---|
| **M2 am Sperrbeleg** | **Kopfbegründung gefallen.** „Der Aufrufer hält den Lock" ist in Verus ein `tracked`-Zeuge: richtiger Kern `verified`, fremder Kern Beweisfehler, selbstgebauter Beleg Typfehler — `no_std`, ohne Byte im Erzeugnis. **Ungemessen bleiben** Sperrordnung ⇒ Deadlockfreiheit und `haelt_hoechstens`; Falle 41 und 93 sind damit noch nicht vergeben |
| **M1 + M2 (Arithmetik/Linearität)** | **Arithmetik und Indexgrenzen: gefallen.** Verus findet S1a und S1b am echten Code für **0 Zeilen** (ein Schalter). **Linearität: halb** — `tracked` ist affin, eine Leckprüfung kostet eine hingeschriebene Bilanz. Rusts `Parked` liefert die andere Hälfte zu null Kosten |
| **M3 (`device`)** | **ungemessen — und der Gegner ist gar nicht Verus.** Typisierte Registerzugriffe (`tock-registers`, `svd2rust`-Art) sind eine **Rust-Bibliothek**. Die Frage ist nicht „kann eine Sprache das", sondern „was fehlt der Bibliothek": Übergänge über Bits, Bedingungen über Registergrenzen, Barrierendomäne im Typ |
| **M3 (Platzierung)** | **ungemessen**, und `#[link_section]` gibt es. Die Lücke ist, dass niemand es **prüft** — das kann eine Lint |
| **Eintritt (TAL)** | tötet **0** bezahlte Fallen und hat nirgends einen Beweiser |
| **`check` über M2** | **kein Gegner gefunden.** Weder Rust noch SPARK noch Verus noch Loom sagt etwas über Sprechprobe, Gatterung, Untergrenze oder isolierende Gegenprobe |

> **Die ehrliche Bilanz nach der ersten Gegenrechnung: übrig bleiben die lineare Prüfpflicht
> (`check` über M2), die Sperrordnung und M3 — und M3s Gegner ist eine Rust-Bibliothek, keine
> Sprache.** Die lineare Prüfpflicht braucht als *Wirkung* keine Sprache: V−1 baut sie als
> Makrobibliothek. Was sie als *Mechanismus* braucht, ist echte Linearität — und die hat Rust nicht.

Damit ist die Reihenfolge nicht mehr „V−1 zuerst, weil billig", sondern **„V−1, weil alles andere
gerade seinen Gegner gefunden hat".**

## 5. Der Plan, mit Toren

Jede Phase liefert eine Zahl, die über die nächste entscheidet. Ohne Zahl kein Weiterbau.

| Phase | Inhalt | **Tor** |
|---|---|---|
| **V−1** | **`check` allein, als Rust-Makrobibliothek** — ohne eigene Sprache, ohne Übersetzer | Es rüstet die 33 Fallen in Caprock nach. **Fangen die Regeln mindestens 5 davon rückwirkend** (mit Mutation belegt), ist die These getragen. Fangen sie 0–1, ist `check` Ergonomie |
| **V0** | Stufe 0 + Stufe 6 als echte Sprache, ein Modul erzeugt | Spezifikationsverhältnis nach dem Protokoll 0b **an zwei Modulen**, beide berichtet |
| **V1** | Stufe 1 (Nebenläufigkeit) | `caprock-sync` + der Cap-Space-Lock übersetzt, **Loom-Beweise gehen durch**, Sperrordnung fängt eine eingebaute Verletzung |
| **V2** | Stufe 2 (`device`) | `vtd.rs` (1 448 Zeilen) übersetzt, **die DMA-Suite bleibt grün**, und vier Mutationen (Fallen 1, 2, 4, 5) übersetzen **nicht** |
| **V3** | Stufe 3 (Linearität/Regionen) | `Parked` und die Endowment-Kette; Mutation zu Falle 96 übersetzt nicht |
| **V4** | Stufe 4+5, Eintritt | ein Syscall-Eintritt ohne `asm!`, gemessen gegen die heutige Zyklenzahl |
| **V5** | Umstellung nach Strangler-Muster | s. u. |

### Die Umstellung nimmt zuerst das Werkzeug auseinander, das die Fehler findet

**Das ist das grösste Risiko des ganzen Vorhabens, und es folgt aus der eigenen Messung.** 15,7 %
von Caprock sind Prüfgerüst; ein Rewrite fasst genau das zuerst an — und für die Dauer der
Umstellung läuft die Abnahmereihe nicht, also die Disziplin, die **jeden** der 100 Einträge oben
gefunden hat.

Daraus folgt die einzige vertretbare Form: **Modul für Modul, beide Fassungen gleichzeitig lebendig,
Differenztest zwischen ihnen.** Nie ein grosser Schnitt. Und die Abnahmereihe bleibt in Rust, bis
`check` in Gabbro sie **nachweislich** ersetzt — nicht umgekehrt.

---

## 5b. Das Abnahmekriterium: Caprock vollständig in Gabbro, Suite grün

**Die Forderung ist falsifizierbar, und das ist ihr Wert.** Nicht „es fühlt sich besser an",
sondern: der Gabbro-gebaute Kernel besteht **die vorhandene Abnahmereihe** — 14 Punkte, x86 in
fünf RAM-Grössen, Lade-Suite, aarch64-Bau **und** -Suite, Host-Tests, Kerngrenze, Wächter.

**Aber die Suite allein reicht nicht, und das ist gemessen, nicht befürchtet:**

> Über die Behebungen von **D8, D9 und D10** hinweg blieb die Signatur der x86-Suite
> **byte-identisch** (`e419003d625f`, 500 Läufe je Stand). Drei echte Kernfehler, und die Suite hat
> keinen davon ausgelöst. **„Alle Tests grün" ist für einen Rewrite deshalb ein notwendiges und
> kein hinreichendes Kriterium.**

Daraus folgt die Abnahme in **drei** Teilen, nicht einem:

| | Kriterium |
|---|---|
| **A** | die 14-Punkte-Abnahme grün, in allen RAM-Grössen und auf beiden Architekturen |
| **B** | **Differenztest gegen die Rust-Fassung**, Modul für Modul: gleiche Eingaben, gleiche Ausgaben, gleiche Absagecodes. Das ist der Teil, der D8/D9/D10 gefangen hätte |
| **C** | die **Wiederholungsmessung** hält: `RUNS`-Signaturvergleich mit Quervergleich zwischen den Strömen — und ein Nullbefund braucht seine Stichprobengrösse, nicht bloss ein grünes Feld |

**Die Reihenfolge ist erzwungen, nicht gewählt:** modulweise, beide Fassungen gleichzeitig lebendig.
Ein grosser Schnitt schaltet für seine Dauer genau die Reihe ab, die jeden der 100 Einträge gefunden
hat — Abbruchbedingung 4.

- [ ] **Die Prüfsuite selbst ist der letzte Umzug, nicht der erste.** Sie ist 15,7 % des Codes und
      besteht aus `check`-Zusagen; sie bleibt in Rust, bis die Gabbro-Fassung **gegen sie** bewiesen
      ist. Wer sein Messgerät zuerst umbaut, misst den Umbau mit dem Umbau.

## 6. Die Kosten, ehrlich

**Der Übersetzer.** Die sieben Konstrukte waren „ein Erzeuger von Wochen". Stufe 0–6 sind die
Klasse ATS / F\*-Low\*-KaRaMeL / Verus — Arbeiten mehrerer Forschungsgruppen über Jahre.
**Eine belastbare Schätzung habe ich nicht**, und eine erfundene wäre schlimmer als keine; deshalb
stehen oben Tore statt eines Termins.

**Die Umstellung.** 66 651 Zeilen, und der Nenner ist kein Argument für sich: entscheidend ist,
dass jedes umgestellte Modul seinen Differenztest mitbringt.

**Die Gegenrechnung, die zuerst zu machen ist:** die Klasse S (36) und die Klasse M (36) sind heute
**nicht unadressiert**. Rust-heute hat `Parked` gefunden. Verus kann Ressourcen-Invarianten über
lineare Ghost-Permissions. Loom fand die abgeschwächte Ordnung, sobald die Zelle im Modell war.
**Für jede Stufe gehört beantwortet: was kann Rust+Verus+Loom heute schon, und was bleibt übrig?**
Nur der Rest rechtfertigt eine Sprache.

## 7. Abbruchbedingungen dieses Zweigs

1. **V−1 fängt weniger als 5 der 33 Fallen rückwirkend.** Dann ist `check` — das einzige Konstrukt
   ohne Vorbild — Ergonomie, und mit ihm fällt die einzige originelle Begründung.
2. **Rust + Verus + Loom decken eine Stufe bereits ab.** Dann wird diese Stufe nicht gebaut.
3. **Das Spezifikationsverhältnis nach Protokoll 0b verfehlt seine Schwellen** (2 : 1 bester,
   5 : 1 schlechtester Fall).
4. **Eine Kernel-Logik lässt sich nicht ausdrücken, ohne die Axiomschicht zu vergrössern.** Die
   Ratsche über den Axiomen darf nur fallen. Wächst sie, um ein Sprachdefizit zu decken, ist die
   Zusage „speichersicher unter A1…An" jedes Mal etwas weniger wert — und niemand merkt es, weil
   die Zusage formal weiter gilt.
5. **Die Umstellung erzwingt einen grossen Schnitt.** Ein Vorhaben, das die Abnahmereihe abschaltet,
   um sich selbst zu bauen, hat keinen Prüfer mehr — und dieses Projekt hat gemessen, was dann
   passiert: zehn Tage rot, ohne dass es jemand sah.
