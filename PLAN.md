# Gabbro — der Plan

**Ein Plan, ein Ziel: ein Kernel in Gabbro, verifiziert bei 0,5 : 1.**

Was hier nicht steht, gibt es nicht. Frühere Fassungen führten einen engen Formaterzeuger als
Rückfall und den Kernel als Zweig „für später“ — beides ist gestrichen. Der Formaterzeuger ist die
Bibliotheksschicht der Sprache ([`SPRACHE.md`](SPRACHE.md)), kein eigener Weg.

Stand 2026-08-13. **Nichts davon ist gebaut.**

---

## Das Ziel ist der BODEN — und deshalb misst es den Abstand, statt zu urteilen

Die 20 : 1 von seL4 zerfallen in rund **0,5 : 1 abstrakte Spezifikation** und **19,5 : 1 Beweis**.
Nur der erste Posten ist unantastbar.

> **0,5 : 1 heisst deshalb nicht „wenig Beweis“, sondern: KEIN HANDGESCHRIEBENER BEWEIS.**
> Geschrieben wird die abstrakte Spezifikation — und sonst nichts.

**Das ist ein ZIEL, keine Schwelle.** Der Unterschied ist nicht kosmetisch: eine Schwelle, die man
treffen kann, sagt am Ende nur „bestanden“. Ein Ziel am theoretischen Boden macht die Kennzahl
**diagnostisch** — jede Zehntelstelle darüber ist ein **benennbarer Beweisposten, der noch von Hand
geschrieben wird**, und damit ein Arbeitsauftrag statt eines Urteils.

**Der Abbruch ist eine ganz andere Marke: > 3 : 1.** Dort ist der Beweis wieder der dominierende
Posten, und die Prämisse „billig“ ist widerlegt — selbst wenn 3 : 1 gegenüber seL4s 20 : 1 noch
eine Verbesserung wäre. Eine Sprache samt Übersetzer zu bauen, um den Beweis von *dominant* auf
*dominant* zu bringen, lohnt nicht; Verus gibt einen guten Teil davon umsonst. **Die Zahl 3 ist
gewählt, nicht hergeleitet** — sie steht hier, damit sie nicht später gewählt wird.

Die Rechnung zeigt, wie schnell der Abstand wächst: braucht **5 %** des Kernels handgeschriebene
funktionale Beweise zu 5 : 1, sind das allein **+0,25** — also 0,75 statt 0,5. Bei 10 % sind es 1,0,
bei **25 %** rund **1,75**.

> **DIE 10 %-ANNAHME WIDERSPRICHT DER EIGENEN MESSUNG, und sie trägt die ganze bedingte
> Ja-Antwort.** Gemessen sind **45 851 Zeilen algorithmischer Rest (68,8 %)**; die eigene Liste der
> Nicht-auf-null-Posten (IPC-Fastpath, Scheduler, `revoke`) plus **872 `Ordering::`-Fundstellen
> allein in `threads/mod.rs`** sagt: **in einem MIKROkernel ist der algorithmische Kern nicht ein
> Zehntel, er IST der Kernel.** Liegt der Anteil bei 25–30 %, steht das Mittel jenseits von 1,5.
> **Das ist die am wenigsten gestützte Zahl des Ordners**, und sie wird nicht durch `revoke`
> entschieden — s. P0.4.

**Daraus drei Bedingungen — sie sind der eigentliche Entwurfsauftrag:**

| | Bedingung | wenn sie fällt |
|---|---|---|
| **B1** | **Invarianten leben an der Struktur, nicht an der Schleife.** Erhält die *erzeugte* Mutation die Invariante, braucht die Schleife keine eigene | jede Schleife bekommt eine handgeschriebene Invariante — der grösste Einzelposten kehrt zurück |
| **B2** | **Algorithmische Rümpfe bestehen aus Traversierungen.** ~~Der Löser bekommt die Invariante geschenkt~~ — **das war Überschreibung Nr. 3**: geschenkt bekommt er die **Sicherheitshülle** (Bereich, Terminierung, Rahmen). **Funktionale** Schleifeninvarianten — Teilsummen, Sortiertheit, Baumform mitten in der Mutation — schreibt weiterhin jemand hin; das ist die gesamte Verus-/Dafny-Erfahrung. Was hilft, sind **Konstrukte, deren Nachbedingung ihre Abbruchbedingung IST** (s. `by consuming` in [`P0-1-REVOKE.md`](P0-1-REVOKE.md)) — und die gibt es je Fall oder nicht | Beweishinweise je Rumpf |
| **B3** | **Was sich so nicht schreiben lässt, muss verschwindend klein sein.** Kandidaten: IPC-Fastpath, `revoke`, die Warteschlangenchirurgie des Schedulers | jeder dieser Rümpfe kostet 5 : 1 auf seinem Anteil |

**Deshalb ist P0.1 (`revoke` auf Papier) nicht ein Tor unter vielen, sondern DAS Tor.** Braucht
`revoke` einen handgeschriebenen Beweis, ist 0,5 : 1 an diesem Tag verloren — unabhängig von allem
anderen.

- [ ] **Die seL4-Aufteilung nachprüfen.** Sie trägt diese ganze Herleitung und ist aus dem
      Gedächtnis zitiert.

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
| vormals *„lock, region, wirkung, einheit, grundmenge, absage, ableitung, stellentyp, arithmetik“* | je 2 |
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
steht in [`PLAN.md`](PLAN.md) als Messprotokoll.

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
spec fn cdt_wellformed(c: CapSpace) -> bool      -- mathematisch, nicht ausfuehrbar,
    = forall s: c.parent_chain(s) ends_at Root;    -- keine Ressourcengrenzen

impl fn delete_leaf(c: &mut CapSpace, s: SlotIdx)
    maintains cdt_wellformed                       -- die Verfeinerungspflicht wird ERZEUGT
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

> **Regel: Spezifikation ist, was in der GABBRO-QUELLE steht und vor der Codeerzeugung gelöscht
> wird.** Alles, was im erzeugten C ankommt, ist Code. **Was der Übersetzer ableitet, ist Ausgabe —
> und zählt in keinem der beiden Töpfe.**

> **ZWEIMAL BERICHTIGT am 2026-08-13.** Fassung 1 sagte nur „keine Laufzeitwirkung" — damit hätte
> die erzeugte Geistertheorie **in den Zähler** gezählt und **der Gold-Mechanismus die Kennzahl
> verschlechtert, je besser er wirkt** (gefunden von [`P0-1-REVOKE.md`](P0-1-REVOKE.md)).
> Fassung 2 sagte „was ein **Mensch** schreibt" — das lässt in einem Projekt mit KI-Koautor eine
> Lücke und, schlimmer, **einen Umweg: eine Makroschicht Quelltext erzeugen zu lassen, der dann als
> geschrieben zählt.** Die belastbare Fassung ist **Quelle gegen Abgeleitetes** — sie ist am
> Artefakt entscheidbar und braucht keine Aussage darüber, wer getippt hat.

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

---

## Der Zuschnitt ist ENTSCHIEDEN: (c)

**Er war lange offen. Mit dem Ziel 0,5 : 1 ist er es nicht mehr:** bleibt die Mutation
handgeschrieben, muss jemand zeigen, dass sie **jede** Invariante erhält — bei seL4 der grösste
Beweisposten überhaupt. **(c) ist damit keine Option, sondern eine Voraussetzung.** Was unten folgt,
ist die Herleitung; die Entscheidung ist gefallen.

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

---

## Was Gabbro wie SPARK könnte — und was besser

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

---

## 4. Was auch dann nicht besser wird — 28 %

| | | Beispiel |
|---|---|---|
| **W (18)** | Werkzeug, Bau, Prozess | `.git/info/exclude`; `grep -q` unter `pipefail`; ein CI-Gate im Format des falschen Servers; zwei Suiten, die dasselbe Gerät verschieden aufsetzen |
| **B (10)** | Bedeutung | „unten zuerst" war ein Zufall der Grössenrelation; der Lader meldet seinen eigenen Speicher als frei; eine Ablage je Rolle |

Dazu die Hardware: `assume`/`falsifier` macht Annahmen **zählbar**, nicht wahr.

**Ein Rewrite, der 100 % erwartet, rechnet mit 72 % — im besten Fall, bei perfekter Umsetzung
jeder Stufe.**

---

---

## AUSGELÖST 2026-08-13: Abbruchbedingung 2 hat für M2 gegriffen

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

---

# Der Weg — acht Phasen, jede mit einem Tor

## P0 — Papier. Drei Fragen, jede kann die These töten

Zusammen ein bis zwei Tage, kein Code. **Das ist der billigste Punkt des ganzen Vorhabens.**

### P0.1 — `revoke` in den Konstrukten ausdrücken

Das (inzwischen gestrichene) *„decrement requires“* war eine Vorbedingung **auf einem Feld**. Die Korrektheitsbedingung von
`revoke` ist **strukturell**: ein Teilbaum verschwindet, und dass danach `kind_zeigt_zurueck` und
die Kettenendlichkeit noch gelten, ist eine Aussage über Baumform.

> **Tor:** Geht es, ist Zuschnitt (c) tragfähig und die 0,8 : 1-Vorhersage hält ihre riskanteste
> Annahme. Geht es nicht, bleibt die **gefährlichste** Mutation handgeschrieben — dann kehrt die
> Invariantenerhaltung als Beweisposten zurück, **und die Kennzahl fällt mit ihr**.

### P0.2 — `vtd.rs` als `device`-Block

1 448 Zeilen Rust gegen eine Beschreibung derselben Einheit.

> **Tor:** Faktor ≥ 5 kleiner. Sonst ist die Knappheitsthese widerlegt, und mit ihr der
> Deklarationsgewinn an jeder Stelle.

### P0.3 — `space.rs` zweimal hinschreiben

Als Gabbro-Quelle **und** mit dem, was ein Beweiser darüber hinaus bräuchte. Der richtige Fall, weil
er beides enthält: beschreibende Struktur **und** algorithmisches `revoke`.

> **Tor:** die erste echte Zahl für die Kennzahl, nach dem Protokoll unten. Über 2 : 1 ⇒ Abbruch.

- [ ] **Dazu, unabhängig und ebenfalls Papier: die Basisrate zählen.** Wie viele Formate hat Caprock
      wirklich, wie oft ändern sie sich, wie viele Fehler dieser Klasse sind pro Jahr entstanden
      (aus `done.md` auszählbar)? Fällt sie klein aus, ist das ehrlichste Ergebnis nicht „es geht",
      sondern „die Falle ist zu selten für eine Sprache".

---

## P1 — `check` als Rust-Makrobibliothek, ohne Sprache

Das einzige Konstrukt ohne Vorbild, und es braucht **keinen Übersetzer**. Rückwirkend gegen die 33
Messdisziplin-Fallen gehalten, jede mit Mutation.

> **Tor:** **≥ 5 der 33** rückwirkend gefangen, mit Mutation belegt. Darunter ist `check` Ergonomie
> — und mit ihm fällt die einzige Begründung, die Gabbro allein gehört.

**Nützlich auch dann, wenn Gabbro nie entsteht.** Das ist der Grund, warum diese Phase vor allen
anderen steht.

---

## P2 — Der Kern als PRÜFER, ohne Codeerzeugung

M1 (Bereichstypen) + M2 (lineare, auch geisterhafte Werte) + M4 (kein ungeprüfter Index) als
Typprüfer über einer minimalen Sprache. Noch kein C.

> **Tor:** S1a und S1b sind **nicht formulierbar**, und zwar mit **0 Zeilen** Annotation. Braucht es
> welche, ist Gabbro an dieser Stelle nur ein umständlicheres Verus.

Zusätzlich hier zu zeigen, weil es der einzige Mechanismus ohne vorhandenes Werkzeug ist:

> **Tor 2:** die **Bootphasen-Marke** trägt — eine `roh`-Funktion nach `boot_ende` übersetzt nicht,
> und ein Versuch, die Marke zu kopieren oder herzustellen, ebenso wenig.

---

## P3 — Absenkung nach C, syntaxgesteuert

Ein Modul durch bis zum C, nicht optimierend, plus Differenztest gegen die Rust-Fassung.

> **Tor:** Differenztest grün (gleiche Eingaben, gleiche Ausgaben, gleiche **Absagecodes**) **und**
> Zyklen je Aufruf gegen die handgeschriebene Referenz gemessen. „Dauerhaft langsamer und die
> Ursache nicht behebbar" ist eine Abbruchbedingung.

---

## P4 — M3 und `device`

Adressräume und Zugriffsrechte am Zeiger; `vtd.rs` übersetzt.

> **Tor:** die DMA-Suite bleibt grün, **und vier Mutationen übersetzen NICHT** — die bezahlten
> Fallen 1 (`STE.S1STALLD`), 2 (CD ohne `R`), 4 (`GCMD` als RMW), 5 (x2APIC `EN`+`EXTD`).

---

## P5 — Axiomschicht und Eintritt

Je privilegiertem Befehl ein erklärter Effekt; ein Syscall-Eintritt ohne handgeschriebenen
Assembler.

> **Tor:** die Axiommenge ist **aufgezählt und beziffert** (Ratsche, darf nur fallen), jedes Axiom
> hat einen `falsifier` oder einen benannten Grund, warum keiner fahrbar ist. **Ohne die Zahl ist
> „speichersicher unter A1…An" eine Form ohne Inhalt.**

---

## P6 — `spec fn` / `impl fn` und die erzeugte Verfeinerungspflicht

Der Gold-Mechanismus.

> **Tor:** die Kennzahl an **zwei** Modulen gemessen, beide berichtet (bester und schlechtester
> Fall) — **samt Aufschlüsselung, welcher Posten den Abstand zu 0,5 : 1 erzeugt.** Eine Zahl ohne
> diese Aufschlüsselung ist wertlos, weil sie keinen Arbeitsauftrag enthält. Abbruch erst > 3 : 1.

---

## P7 — Rennfreiheit

Datenrennen aus M2/M3; **Protokollrennen** über lineare Phasen.

> **Tor:** die **D0-Form** ist nicht formulierbar — ein Thread, der lauffähig wird, bevor er seine
> Autorität hat, übersetzt nicht. Das ist der Fall, den jeder Datenrennen-Prüfer der Welt
> durchgelassen hätte.

---

## P8 — Umstellung nach Strangler-Muster

Modul für Modul, **beide Fassungen gleichzeitig lebendig**, Differenztest dazwischen. Nie ein
grosser Schnitt.

> **Abnahme, dreiteilig:** (A) die 14-Punkte-Reihe grün, beide Architekturen, alle RAM-Grössen ·
> (B) Differenztest gegen die Rust-Fassung, Modul für Modul · (C) Wiederholungsmessung mit
> Quervergleich, Nullbefunde mit Stichprobengrösse.
>
> **(B) ist nicht optional:** über die Behebungen von D8, D9 und D10 hinweg blieb die x86-Signatur
> **byte-identisch** (500 Läufe je Stand). Drei echte Kernfehler, keiner ausgelöst.

**Die Prüfsuite ist der LETZTE Umzug, nicht der erste.** Sie ist 15,7 % des Codes und besteht aus
`check`-Zusagen; sie bleibt in Rust, bis die Gabbro-Fassung **gegen sie** bewiesen ist. Wer sein
Messgerät zuerst umbaut, misst den Umbau mit dem Umbau.

---

## Später, ausdrücklich nicht jetzt

* **Binärverifikation** (seL4-Art, erzeugtes C gegen Maschinencode). Der Weg existiert, ist aber ein
  eigenes Projekt — und er ist der einzige, der die Absenkung aus der Vertrauensbasis nimmt.
* **Wiederverwendbare Spezifikationstheorien** (Fähigkeitssystem, Seitentabellen). Sie helfen dem
  **zweiten** Projekt, nicht dem ersten — deshalb dürfen sie in keiner Kostenrechnung mitgezählt
  werden, solange es nur einen Kernel gibt.
* **~~Rust-Ausgabe~~, ~~Ada-Ausgabe~~** — gestrichen am 2026-08-13. Sie waren nur nötig, solange ein
  *fremder* Beweiser den Beweis führen sollte.
* **Seitentabellen-Beschreiber.** Verlockend (das fehlende `US` auf der Zwischenebene wäre nicht
  formulierbar gewesen), aber Seitentabellen sind Hardwareverträge; ein falscher Beschreiber erzeugt
  einen beweisbar korrekten falschen Kernel.

---

## Die Abbruchbedingungen — hier, damit sie nicht verhandelt werden

Gabbro endet, wenn **eines** davon eintritt:

1. **Die Basisrate ist zu klein** (P0) — zu wenige Formate, zu wenige Fehler dieser Klasse.
2. **`check` fängt rückwirkend weniger als 5 der 33 Fallen** (P1). Dann fällt die einzige
   Begründung, die Gabbro allein gehört.
3. **Rust + Verus + Loom decken einen Mechanismus bereits ab.** Für M2 am Sperrbeleg und für M1
   ist das am 2026-08-13 **eingetreten**; übrig bleibt echte Linearität. Tritt es für die auch ein,
   ist der Kern leer.
4. **Die Kennzahl liegt über 3 : 1** (P6). *Nicht* „sie verfehlt 0,5 : 1“ — das ist das **Ziel**,
   an dem der Abstand gemessen wird, keine Schwelle. Abgebrochen wird erst, wenn der Beweis wieder
   der dominierende Posten ist.
5. **Der erzeugte Code ist dauerhaft langsamer** als die handgeschriebene Referenz und die Ursache
   ist nicht behebbar (P3).
6. **Eine Kernel-Logik lässt sich nur ausdrücken, indem die Axiomschicht wächst.** Die Ratsche darf
   nur fallen. Wächst sie, um ein Sprachdefizit zu decken, wird „speichersicher unter A1…An" jedes
   Mal etwas weniger wert — und niemand merkt es, weil die Zusage formal weiter gilt.
7. **Die Umstellung erzwingt einen grossen Schnitt** (P8). Ein Vorhaben, das die Abnahmereihe
   abschaltet, um sich selbst zu bauen, hat keinen Prüfer mehr — und dieses Projekt hat gemessen,
   was dann passiert: zehn Tage rot, ohne dass es jemand sah.

Ein Ordner, der seine eigenen Abbruchbedingungen nicht nennt, wird nie beendet — nur vergessen.

---

## Das Messprotokoll zur Kennzahl — vorab, weil es sonst die Wunschzahl liefert

Die Regeln stehen hier **vor** der Messung, aus demselben Grund, aus dem die IPC-Schwelle von
2000 Zyklen vorab feststeht: eine Schwelle, die man nach dem Ergebnis wählt, ist keine.

**1. Zwei Module, beide berichtet — die Wahl entscheidet sonst das Ergebnis.**

| | Modul | erwartet |
|---|---|---|
| **bester Fall** | der **Manifest-Leser** (`format`) | nahe am Ziel — hier *ist* der Beschreiber die Spezifikation |
| **schlechtester Fall** | ein **(c)-Mutationsmodul** am Cap-Space | deutlich darüber — Schleifeninvarianten, Ghost-Code, Hilfslemmata |

**Nur den ersten zu berichten ist die Manipulation**, und sie braucht keine Absicht: man misst das
Modul, das fertig ist.

**2. Zählregel für den Zähler — Beweiscode IST Spezifikation.** Was der nachgelagerte Beweiser
zusätzlich braucht, zählt mit: **Schleifeninvarianten, Ghost-Code, Hilfslemmata, `assert`-Ketten,
ACSL-Annotationen**. Wer nur den Gabbro-Beschreiber zählt, misst die halbe Last — und genau die
Hälfte, die bei (c) explodiert.

**3. Zählregel für den Nenner — GABBRO-CODE.** Nicht die handgeschriebene Rust-Referenz: gemessen
wird, ob ein **in Gabbro geschriebener** Kernel billig zu verifizieren ist; Rust kommt darin nicht
vor. **Die Trennlinie ist die Laufzeitwirkung:** was der Übersetzer vor der Codeerzeugung löscht,
ist Spezifikation; was im erzeugten C ankommt, ist Code. Gezählt wird in **Anweisungen**, nicht in
Zeilen — sonst gewinnt geschwätziger Code. Und wer eine Eigenschaft zur Laufzeit **prüft** statt
sie zu beweisen, verschiebt Zeilen nach unten: erlaubt, aber die Laufzeitmessung gehört daneben.

**4. Die Stufe steht dabei.** Ob Sicherheitshülle, deklarierte Invarianten oder funktionale
Korrektheit gemessen wurde, gehört neben die Zahl — die 20 : 1 von seL4 ist eine Zahl für die
**stärkste** Stufe. Ein Verhältnis ohne Stufe vergleicht über eine Kluft.

**5. Der Beweisweg IST entschieden** (2026-08-13): Gabbro prüft selbst, Ausgabe ist C + iasm, kein
nachgelagerter Beweiser. Damit fällt die ACSL-Last aus dem Zähler und die Entsprechungspflicht weg.
**Was stattdessen in den Zähler gehört:** `spec fn`-Zeilen und die Verfeinerungsannotationen — und
das ist bei einem Kernel der Boden, der die 1 : 1 unerreichbar macht (§3c dort).

**Ziel und Abbruch sind zwei verschiedene Dinge, und die Verwechslung war ein eigener Fehler:**
**Ziel ist 0,5 : 1**, der theoretische Boden — er wird nicht „bestanden“, sondern der **Abstand**
dazu wird aufgeschlüsselt. **Abgebrochen** wird bei **> 3 : 1**, wo der Beweis wieder dominiert.
Die 3 ist gewählt, nicht hergeleitet; sie steht vorab, damit sie nicht später gewählt wird.

---

## Das Abnahmekriterium: Caprock vollständig in Gabbro, Suite grün

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

---

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
