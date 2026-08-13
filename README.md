# Gabbro

Eine Sprache für Formate, Tabellen — und, als ausgesprochenes Fernziel, für Kernelcode selbst.
Ziel ist **C**. Übersetzer in **sicherem Rust** (`forbid(unsafe_code)`).

> **BERICHTIGUNG, und sie steht bewusst in Zeile 3.** Die erste Fassung schrieb hier „per
> Konstruktion **beweisbar**". Das war eine Überschreibung: **Gabbro beweist nichts.** Es erzeugt
> nach Regeln, und die Korrektheit des Erzeugnisses hängt an einem **unverifizierten Übersetzer**.
> EverParse beweist seine Parser tatsächlich, in F\*. Gabbro liefert *„korrekt unter Vertrauen in
> den Erzeuger, plus Differenztest"* — ein legitimer Handel, derselbe wie bei jedem Übersetzer,
> aber er ist zu benennen und nicht zu verschweigen. Der Satz „ein Beweis, der die Wunschform
> beweist, ist schlechter als keiner" gilt auch für Wörter in Überschriften.

Stand dieser Notiz: 2026-08-13. Nichts davon ist gebaut — das hier ist der Entwurf, nicht ein
Bericht. Was gemessen ist, steht als gemessen da; alles andere ist ausdrücklich Absicht.

---

## Warum der Name

**Gabbro ist der plutonische Zwilling des Basalts**: dieselbe Zusammensetzung, aber langsam
abgekühlt — deshalb grosse, regelmässige Kristalle statt feinem Gefüge. Genau das tut ein
verifizierender Erzeuger: derselbe Stoff wie handgeschriebener Code, nur langsam und absichtlich
auskristallisiert.

Das Wort ist in Deutsch und Englisch identisch. Es passt zu Caprock (beides magmatisch), und
anders als *Basalt* — der erste Vorschlag — ist es nach heutigem Stand nicht von einem Übersetzer
belegt.

- [ ] **Nachprüfen, nicht glauben.** Von dieser Maschine aus ist die Namensfreiheit nicht zu
      belegen; „ich habe nichts gefunden" ist ein Nullbefund ohne Grösse. Vor der ersten
      Veröffentlichung gehört eine Suche über Paketregister (crates.io, PyPI, npm), GitHub und
      Sprachlisten — mitsamt dem, was gefunden wurde.

---

## Was Gabbro ist — und was ausdrücklich nicht

**Gabbro beschreibt Formate und Tabellen und erzeugt daraus Leser, Schreiber und Prüfer.**
Es ist **keine** Allzwecksprache. Kein Kernel wird darin geschrieben, kein Treiber, kein Dienst.

Der Grund ist eine Erfahrung, keine Vorliebe: **funktionale Korrektheit (»Gold«) ist teuer, weil
die Spezifikation teuer ist** — bei seL4 rund 200 000 Zeilen Isabelle auf 10 000 Zeilen C, ein
Verhältnis von 20:1. Keine Sprachgestaltung nimmt einem das ab, solange die Domäne offen ist.

**Für eine enge Domäne kippt die Rechnung**, weil die Invarianten im *Sprachentwurf* stecken statt
in einer Spezifikation je Funktion. Der Beschreiber **ist** die Spezifikation. Man beweist nicht,
dass der Parser dem Format entspricht — man erzeugt ihn daraus.

### Der Riss: `format` und `table` sind NICHT dieselbe Kategorie

Die erste Fassung behandelte beide gleich. Das ist falsch, und der Unterschied entscheidet über
den Wert des ganzen Ordners.

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

> **Damit gilt: wer Invarianten im heissen Pfad will, hat den Zuschnitt (c) bereits gewählt — ob
> er es aufgeschrieben hat oder nicht.**

- [ ] **Diese Entscheidung gehört VOR Phase 0**, nicht nach Phase 3. Denn sie ändert, was Phase 0
      überhaupt töten kann: **EverParse macht ausschliesslich die `format`-Hälfte.** Liegt der
      eigentliche Wert bei `table` — und dafür spricht viel, denn verifizierte Drahtparser sind
      ein gelöstes Problem, erzeugte Invarianten-Infrastruktur für kernelinterne Tabellen nicht —,
      dann kann EverParse Gabbro **gar nicht erledigen**, sondern nur die halbe
      Daseinsberechtigung streichen.

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
      wahrscheinlich **billiger** als ein Übersetzer, den man baut *und wartet* — parallel zu A4,
      Z24 und den A3-Folgeposten.
      **Fällt die Zählung klein aus, ist das ehrlichste Ergebnis dieses Ordners nicht
      „EverParse trägt", sondern „die Falle ist zu selten für eine Sprache".**

---

## Die vier Entwurfsregeln

Jede ist als Antwort auf einen bezahlten Fehler formuliert.

### 1. Total per Konstruktion

Es gibt **keine unbegrenzte Schleife**. Jede Iteration läuft über eine Länge, die entweder eine
Konstante ist oder ein Feld, das **vorher** gelesen und geprüft wurde. Terminierung ist damit
keine Beweispflicht, sondern eine Eigenschaft der Grammatik.

> *Fundstelle:* `migration_candidate` läuft eine Kette `while i != NIL` **ohne Schrittgrenze**,
> während der Prüfer über derselben Kette eine führt. Unter dem Kern-Lock ist ein Zyklus dort ein
> stehender Kern.

#### Nachschärfung: „endlich" ist das SCHWÄCHSTE Versprechen

Terminierung allein kauft wenig. Eine Schleife mit Schrittgrenze **terminiert** und kann trotzdem
ausserhalb der Tabelle indizieren — genau das ist **S1a**: die Schrittgrenze aus B-5.5 schützt
gegen **Zyklen**, nicht gegen einen Index **ausserhalb** der Tabelle.

**Statt `while` mit Schranke gibt es deshalb nur TRAVERSIERUNGEN, und jede nennt drei Dinge:**

| | was es nennt | welche Fehlerklasse es tötet |
|---|---|---|
| **Bereich** (`over`) | die Menge, über die gelaufen wird — `over slots`, `over chain(first_child, next_sibling) in slots` | **S1a**: ein Index ausserhalb der Menge ist **nicht formulierbar**, nicht bloss geprüft |
| **Fortschritt** (`by`) | was streng abnimmt — die Restmenge, ein Zähler, ein Rang | Terminierung; **und Zyklen**, wenn der Fortschritt „noch nicht besucht" ist |
| **Wirkungsraum** (`touches`) | was gelesen und was geschrieben werden darf | fremde Schreibzugriffe; `restrict` **an den Parametergrenzen** der erzeugten Funktionen |

> **`restrict` ist enger, als die Zeile klingt.** Es trägt an den **Parametergrenzen** erzeugter
> Funktionen. **Innerhalb** eines Traversierungskörpers, der im Zuschnitt (c) beliebige Slots
> anfasst, sagt es nichts. Das ist mit der Grenze „beisst nur in (c)" konsistent — aber die
> Tabellenzeile klang allgemeiner, als sie ist.

#### `by unbesucht` hat ein eigenes Kostenmodell — und Regel 3 erzwingt die teure Fassung

Dieselbe Fehlerklasse wie bei den Invarianten, eine Ebene tiefer, und sie war im ersten Entwurf
wieder unbenannt.

„Die Restmenge nimmt streng ab" setzt voraus, dass jemand die **besuchte Menge führt**. Über
80 256 Slots heisst das entweder eine **Bitmap** (~10 KB — *wo lebt die?* Stack unter dem
Kern-Lock, statisch, je Kern?) mit **O(n)-Löschung vor jedem Lauf**, oder **Generationsstempel je
Slot**, die den Slot verbreitern.

**Und der Preis ist nicht optional:** Regel 3 („abweisen, nie deuten") **erzwingt** `unbesucht`
gegenüber der billigen Alternative. Ein blosser Schrittzähler terminiert nur — ein Zyklus würde
dann **stillschweigend abgeschnitten** statt als benannte Absage `Zyklus` gemeldet, und das wäre
Deutung. **Die Sprache zwingt also in die teure Variante, ohne dass der Beschreiber den Preis
nennt.**

- [ ] **Kostenangabe an `by unbesucht` selbst**, genau wie bei den Invarianten: *welche Struktur,
      wer setzt sie zurück, was kostet der Reset* — und ob sie unter dem Kern-Lock leben darf.

```gabbro
traverse geschwister of p
    over  chain(first_child, next_sibling) in slots
    by    unbesucht                    -- die Restmenge nimmt streng ab
    touches read slots                 -- schreibt nichts
{
    if it == s { found }
}
```

Der erzeugte Code kann `it` gar nicht als rohe Zahl behandeln — es ist ein Element des genannten
Bereichs. **Die Bereichsprüfung entfällt nicht, sie wird unnötig.**

### Dieselbe Form für alles andere, was heute still schiefgehen kann

**Arithmetik:** `refcount -= 1` gibt es nicht. Es gibt `decrement refcount requires refcount > 0`
— oder ausgesprochenes `wrapping`. Damit ist **S1b** unformulierbar statt hinterher auffindbar.

**Zustandsübergänge:** ein `state`-Konstrukt nennt die **erlaubten** Übergänge. Das Fenster aus
**I9** (`used = false` bei `refcount = 1`) wäre dann kein Zufall der Reihenfolge, sondern ein
nicht existierender Übergang.

**Wirkungen:** jede Operation nennt, was sie anfasst — SPARKs `Global`/`Depends`. Dafür gibt es
**eine Messung am Mechanismus**: im Scheduler wurden damit **63 von 63** Datenabhängigkeiten
bewiesen, und „der Rust-Code liest überall genau einmal in eine Kopie" ging von *gelesen* zu
*bewiesen*. **Die Übertragbarkeit auf Gabbros `touches` ist damit aber nicht gemessen, sondern
angenommen** — SPARK prüft vorhandenen Code, Gabbro erzeugt ihn. Der frühere Satz „kein Entwurf,
sondern gemessen" war eine halbe Stufe zu stark.

### Wo diese Idee aufhört zu tragen — zwei Grenzen

**Erstens: sie beisst nur im Zuschnitt (c).** Ein Wirkungsraum an einer Traversierung, die der
Kernel **nicht aufruft**, kauft nichts. Solange die Mutation handgeschrieben bleibt, ist auch die
schärfste Schleifenform nur eine Empfehlung — dieselbe Ableitung wie beim Kostenmodell.

**Zweitens: jede Vorgabe verengt.** Eine Sprache, die nur Traversierungen kennt, kann Dinge nicht
ausdrücken, die eine freie Schleife brauchen. Und je mehr Konstrukte ihren Vertrag mittragen,
desto näher rückt Gabbro an einen **Beweisassistenten mit Syntax** — und damit an die
Spezifikationslast, der es ausweichen soll. **Die Linie gehört ausgesprochen:**

- [ ] **Wo hört es auf?** Vorschlag zur Entscheidung: Bereich, Fortschritt, Wirkungsraum,
      Arithmetik-Vorbedingung und Zustandsübergänge — **mehr nicht**. Keine allgemeinen
      Vor-/Nachbedingungen, keine Quantoren über Rechenausdrücke. Wer die braucht, braucht Verus
      oder F\*, und das ist eine ehrlichere Antwort als eine halbe Beweissprache.

#### **Die Linie bricht nicht an `insert` — sie bricht an `revoke`. Und das ist auf Papier prüfbar.**

`decrement refcount requires refcount > 0` ist eine **arithmetische Vorbedingung auf einem Feld**;
die trägt die Linie. Die Korrektheitsbedingung von `revoke` ist dagegen **strukturell**: ein
Teilbaum verschwindet, und dass danach `kind_zeigt_zurueck` **und** die Kettenendlichkeit noch
gelten, ist eine Aussage über **Baumform** — strukturelle Induktion, also genau die „Quantoren
über Rechenausdrücke", die die Linie ausschliesst.

**Die ehrliche Vorhersage: `insert` und `remove` passen in die fünf Konstrukte, `revoke` nicht.**
Dann gibt es zwei Ausgänge, und beide sind unbequem:

* **`revoke` bleibt handgeschrieben** — dann steht die **gefährlichste** Mutation ausserhalb der
  Garantie, und die Wertfrage von Zuschnitt (c) stellt sich neu.
* **Die Linie wandert** — dann ist Gabbro der Beweisassistent mit Syntax, dem es ausweichen wollte.

- [ ] **DER BILLIGSTE NÄCHSTE SCHRITT DES GANZEN ORDNERS: `revoke` in den fünf Konstrukten auf
      Papier ausdrücken — vor jeder anderen Entscheidung.** Kostet einen Abend und entscheidet,
      ob Zuschnitt (c) überhaupt hält, was Phase 4 von ihm verlangt. Er steht damit **vor**
      Phase −1, weil er billiger ist als das Auszählen der Basisrate und eine schärfere Frage
      beantwortet.

### 2. Keine Zeiger — nur Versätze, und jeder gegen eine Länge im Geltungsbereich

Ein Versatz ohne die Länge, gegen die er gilt, ist in Gabbro nicht schreibbar. Die Bereichsprüfung
entsteht nicht durch Sorgfalt, sondern weil es keine andere Formulierung gibt.

> *Fundstelle:* `audit_cdt` prüft `parent` gegen `nslots`, liest dann aber `first_child` und die
> Geschwisterkette **ungeprüft**. Mit `panic = "abort"` reißt der Prüfer den Knoten mit — bei
> genau der Anomalie, die er melden soll.

### 3. Abweisen, nie deuten

Eine unbekannte Version, ein gesetztes reserviertes Feld, eine krumme Länge: **benannte Absage**.
Es gibt keine Vorgabe, kein Aufrunden, kein »wird schon passen«. Der erzeugte Code hat für jeden
Abweisungsgrund einen eigenen Code — nicht einen gemeinsamen Formfehler.

> *Fundstelle:* Eine Prüfung las **ein Byte** des Kernel-Hashes statt 512 Byte zu vergleichen:
> Falsch-Alarm bei 1 von 256 Bauten, **blind bei 255 von 256** echten Überschreibungen.

### 4. Feste Breiten, ausgesprochene Bytereihenfolge

Kein `usize`, kein Wirtslayout, kein `#[repr]`-Vertrauen. Was auf dem Draht steht, steht im
Beschreiber.

> *Fundstelle:* `MASK_BITS` war nicht die Farbanzahl — auf x86 (256 Farben) zufällig richtig, auf
> aarch64 (16) falsch. Bei 16 Farben bekam Streifen 0 **alle** Farben und die übrigen keine, und
> weil leere Mengen sich nicht schneiden, meldete der Selbsttest »disjunkt«.

---

## Syntax — der Entwurf

Nichts davon ist übersetzt worden. Die Beispiele sind so gewählt, dass sie echte Caprock-Formate
treffen.

### Ein Format

```gabbro
format ManifestEintrag @version 3 endian little {
    program_id  : u32
    entry_len   : u32   where == sizeof(Self)
    iface       : u32
    domain      : u8    in { Trusted = 0, Hardware = 1, User = 2 }
    _pad        : [u8; 3]  reserved          -- muss 0 sein, sonst Absage
    code_hash   : [u8; 32]
    selector    : GeraeteSelektor
}

format GeraeteSelektor endian little {
    vendor : u16
    device : u16
    class  : u8
    _pad   : [u8; 3] reserved
}
```

Erzeugt wird daraus:

* `gabbro_manifest_lesen(const uint8_t *p, size_t n, ManifestEintrag *out) -> GabbroErr`
* `gabbro_manifest_schreiben(const ManifestEintrag *in, uint8_t *p, size_t n) -> GabbroErr`
* je Abweisungsgrund ein eigener Code (`GABBRO_VERSION_FREMD`, `GABBRO_RESERVIERT_GESETZT`,
  `GABBRO_ZU_KURZ`, `GABBRO_FELD_AUSSERHALB`)
* eine C-`struct` mit **festen** Breiten, kein Padding-Vertrauen

`where`-Klauseln sind Teil des Formats, nicht ein nachgelagerter Test: der Leser gibt eine Absage
zurück, wenn sie nicht gelten — er liefert **niemals** eine Struktur, die sie verletzt.

### Eine Tabelle mit Invarianten

```gabbro
table CapSpace {
    kapazitaet : const 80256

    slot {
        used   : bool
        object : index into objects        -- Bereichsprüfung erzwungen
        parent : option index into slot    -- Option, kein Sentinel
        first_child, next_sibling : option index into slot
        gen    : u32  wrapping             -- Umlauf ist ABSICHT, s. u.
    }

    invariant kind_kette_endlich:
        chain(first_child, next_sibling) bounded by kapazitaet

    invariant kind_zeigt_zurueck:
        forall s where s.parent = Some(p) => s in chain(p.first_child, next_sibling)

    invariant refcount_stimmt:
        forall o: o.refcount == count(s where s.object == o)
}
```

Daraus entstehen der Prüfer (`gabbro_capspace_audit`), die Zugriffshelfer und — das ist der Punkt —
die **Bereichsprüfung an jeder Indizierung, ohne dass jemand sie schreibt**.

`wrapping` ist ausdrücklich zu schreiben. Ein Umlauf, den niemand ausgesprochen hat, ist ein
Fehler; einer, der ausgesprochen ist, ist ein Entwurf.

> *Fundstelle:* `refcount -= 1` ohne Bedingung, und `overflow-checks` ist im Release nicht gesetzt
> — also kein Absturz, sondern **stiller Umlauf auf `0xFFFF_FFFF`**: Objekt nie finalisiert,
> Region nie freigegeben.

### Eine Aufzählung mit Absagen

```gabbro
reason MangelGrund {
    Keiner            = 0  "keine Ressource -- der Fehlschlag lag nicht an einem Vorrat"
    KernelStack       = 2  "EL0-Kernel-Stack"
    Seitentabelle     = 6  "Speicher fuer eine Seitentabelle"
    GuardTabelle      = 13 "aufgeteilte Seitentabelle fuer die Guard-Page"

    exhaustive                 -- kein `_ => unbekannt`
}
```

`exhaustive` heißt: der erzeugte C-`switch` hat keinen `default`, und ein neuer Wert bricht die
Übersetzung. Eine Aufzählung mit Auffangzweig sammelt ungeprüfte Werte an.

---

## Warum C als Ziel

* **Zwei Verbraucher ohne Umweg**: Rust bindet C über FFI, SPARK ebenso — Gabbro-Erzeugnisse
  passen in beide möglichen Zukünfte dieses Kernels.
* **Binärverifikation existiert als Weg**: seL4 beweist den *übersetzten* Code gegen das C. Über
  Zig oder direkt LLVM-IR gäbe es diesen Präzedenzfall nicht.
* **Vorhersagbarer Codegen** — geradliniger Code, keine Halde, keine versteckte Kontrolle.

### Leistung ist ein Entwurfsziel, kein Nachgedanke

* **Keine Allokation.** Der erzeugte Leser arbeitet auf `(ptr, len)` und schreibt in eine
  vom Aufrufer gestellte Struktur.
* **Bereichsprüfungen, die der Übersetzer entfernen kann.** Weil jeder Versatz gegen eine Länge
  im Geltungsbereich steht, sieht LLVM den Beweis und streicht die Prüfung — nicht der Mensch.
* **`restrict`, wo der Beschreiber Nichtüberlappung zeigt.** Aus der Struktur, nicht als Zusage.
* **Geradlinig statt schleifend**, wo die Länge konstant ist: ein 32-Byte-Hash wird kopiert, nicht
  gezählt.
* **Messbar, nicht behauptet**: jedes erzeugte Format bringt eine Messzeile mit (Zyklen je
  Aufruf, gegen eine handgeschriebene Referenz). Ohne die Gegenzahl ist »schnell« ein Gefühl.

---

## Der Übersetzer

**In sicherem Rust**, `#![forbid(unsafe_code)]`, ohne Abhängigkeiten außerhalb einer benannten
Liste. Das ist dieselbe Regel, die Caprock für seine Handler-Module durchsetzt — ein Erzeuger, der
selbst ausbrechen kann, macht die Eigenschaft seines Erzeugnisses wertlos.

SPARK wäre die Alternative und ist **verworfen**, aus einem gemessenen Grund: der Übersetzer ist
ein Textwerkzeug mit Halde und Zeichenketten; SPARKs Stärke (Bereichs- und Überlaufbeweise auf
festen Daten) zahlt sich dort kaum aus, während seine Schwäche (dynamische Datenstrukturen)
voll durchschlägt. Beim *Erzeugnis* liegt es umgekehrt — und dort steht am Ende C.

---

## Was im Entwurf noch fehlt

Der Syntaxteil oben zeigt **ausschliesslich Strukturen fester Grösse** — die Domänentabelle nennt
aber GPT und FAT, und FAT hat **Ketten**, virtio-Ringe haben **Producer/Consumer-Indizes**.

- [ ] **Variable Längen** sind die harten 20 % jedes Parser-Erzeugers. Die Totalitätsregel deckt
      sie im Prinzip ab (eine Länge, die vorher gelesen und geprüft wurde) — **eine Syntax dafür
      gibt es nicht.**
- [ ] **Versionsevolution.** Im Beispiel steht `@version 3`. Liest der Erzeuger auch v2 —
      **Absage oder Migration?** Beides ist vertretbar, keins ist entschieden, und ein Format ohne
      Antwort darauf ist bei der ersten Änderung eine Baustelle.
- [ ] **Die Roundtrip-Eigenschaft** `lesen(schreiben(x)) == x` gehört in den Differenztest. Ein
      Schreiber, der eine ungültige Struktur ausgeben kann, entwertet den Leser.
- [ ] **Kostenangabe je Invariante** — sie steht jetzt beim Zuschnitt oben, weil sie ihn
      **mitentscheidet**. Was hier bleibt: jede einzelne Invariante braucht ihre Zahl und die
      Aussage, wo sie laufen darf.

## Das Fernziel: ein Kernel in Gabbro — und was es mit der These macht

Gewünscht ist ausdrücklich, dass man darin am Ende einen **sicheren und schnellen Kernel**
schreiben kann, und dass die **Syntax dafür schwer sein darf**.

**Das ist eine andere These als die oben, und der Widerspruch gehört ausgesprochen:** die
Rechnung, die Gabbro billig macht, ist die **geschlossene Domäne**. Eine Sprache, in der man einen
Kernel schreibt, hat keine geschlossene Domäne — die Spezifikationslast kehrt zurück, und man
steht im Gebiet von **F\*/Low\***, das dort seit Jahren ausgeliefert wird (HACL\*, EverCrypt).

**Es gibt einen Entwurf, der beides trägt**, und er hängt an dem Zugeständnis „die Syntax darf
schwer sein":

> **Ein kleiner Kern mit linearen/affinen Typen, Regionen und Totalität als Vorgabe** — und
> `format`/`table` sind **Bibliotheken darüber**, keine zweite Sprache daneben.

Dann ist der Formaterzeuger ein Sonderfall des allgemeinen Mechanismus statt eines Anhängsels, und
`Parked` („dieser Wert muss verbraucht werden") wäre ein **Typ** statt einer abschaltbaren
Warnung — gemessen: SPARK meldet dort „leak **proved**", Rust nur `#[must_use]`.

**Der Preis ist ehrlich zu nennen:** das ist nicht mehr ein Erzeuger von Wochen, sondern die
ATS-/Low\*-Klasse von Aufwand.

### Und der Vergleichsgegner war falsch gewählt

Die erste Fassung mass den Zweig an **Low\***. Für die Behauptung „`Parked` wäre ein **Typ** statt
einer abschaltbaren Warnung" sind aber **zwei billigere Gegner** näher, und gegen die ist der
Mehrwert zu belegen:

* **Rust, heute, in Caprock.** Ein Newtype ohne `Drop`, ohne `Copy`, mit versiegeltem Konsumpfad
  erzwingt für **diese eine Ressource** lineares Verhalten zu **null Sprachkosten**. Das ist keine
  vollständige Linearität — Rust ist affin, Wegwerfen bleibt möglich, `#[must_use]` ist nur eine
  Warnung —, aber `mem::forget`-Disziplin plus ein Konsum-Token, das der **einzige** Weg aus dem
  Zustand ist, deckt den `Parked`-Fall konkret ab. **Genau so ist `Parked` gebaut**, und es hat
  eine fünfte Stelle gefunden, die das Gegenlesen übersah.
  **Diese Evidenz zählt GEGEN den Kernel-Zweig, nicht für ihn:** Rust-heute hat den Fehler
  gefunden, **ohne dass es Gabbro gab**. Wer sie als Argument für eine neue Sprache anführt, führt
  den Erfolg der Baseline als Grund an, sie zu ersetzen.
* **Verus.** Steht in der Verwandtschaftstabelle unten und wird dort mit „beweist, was jemand
  modelliert hat" abgetan — **für den Kernel-Zweig kehrt sich das um**: Beweise direkt auf Rust,
  SMT **ohne** F\*-Kette, keine C-Extraktion nötig, solange der Kernel Rust bleibt. Das sind
  **zwei der drei** geforderten Belege bei einem **vorhandenen** Werkzeug. Und Verus kann
  Ressourcen-Invarianten über lineare Ghost-Permissions ausdrücken.

- [ ] **Verus an `Parked` ausprobieren, bevor der Zweig ein eigener Entwurf wird.** Das ist die
      Phase-0-Logik für den Zweig: *der nächste Verwandte ist gebaut, der Ordner nicht.*

### Der Zweig gehört unter „Später" — und zwar aus einem Strukturgrund

**Er ist der verführerischste Teil dieses Ordners**: der einzige, der das ausgesprochene „keine
Allzwecksprache, kein Kernel darin" aufweicht — und zugleich der, der **am weitesten von einer
Kennzahl entfernt** ist. Die Disziplin dieses Ordners besteht darin, dass **jede Phase eine Zahl
liefert**. Der Zweig hat keine.

**Solange er keine hat, steht er formal unter „Später, ausdrücklich nicht jetzt", mit eigenem
Tor.** Sonst ist er der Weg, auf dem ein Formaterzeuger unbemerkt zur Sprachfamilie wird, während
A4 und die A3-Folgeposten warten.

- [ ] **Sein Tor:** eine belegte Antwort auf „was über **Rust-heute** und **Verus** hinaus?" —
      nicht über Low\*, das ist der übernächste Gegner. Ohne diese Antwort wird nichts gebaut.
- [ ] Erst danach: **ein Kern mit zwei Bibliotheken, oder zwei Projekte.** Beides ist vertretbar;
      unentschieden ist es die teuerste Variante.

## Was Gabbro **nicht** löst

Diese Liste steht hier, damit sie nicht später als Enttäuschung entdeckt wird.

* **Falsche Formate.** Gabbro beweist, dass der Leser dem Beschreiber entspricht — nicht, dass der
  Beschreiber der Wirklichkeit entspricht. Wer die Bytereihenfolge falsch aufschreibt, bekommt
  einen beweisbar korrekten falschen Leser.
* **Hardware-Zusagen.** Dass eine IOMMU-Einheit `TE=1` ehrt, steht in keinem Formalismus.
* **Nebenläufigkeit.** Gabbro beschreibt Daten, nicht Abläufe. Wer den Beschreiber unter einer
  Sperre liest, muss das weiterhin selbst wissen — auch SPARK kann »der Aufrufer hält den
  Spinlock« nicht ausdrücken.
* **Die Klasse Fehler, die diese Woche wehtat.** Ein fehlendes `US`-Bit auf der Zwischenebene,
  ein Index über den Slot statt über die Identität, eine Wachseite, die einen Farbstreifen
  sprengt: **Fehler über Bedeutung, nicht über Form.** Gefunden hat die alle die Messdisziplin,
  und daran ändert Gabbro nichts.

---

## Verwandtschaft, und warum trotzdem etwas Eigenes

| Projekt | was es kann | warum es hier nicht reicht |
|---|---|---|
| **F\*/Low\*** | Gold, extrahiert nach C, in HACL\* ausgeliefert | Allzwecksprache — die Spezifikationslast bleibt |
| **Kaitai Struct** | Formate deklarativ, viele Zielsprachen | keine Beweise, keine Absage-Disziplin, kein `no_std`-C |
| **P4, Nail, EverParse** | verifizierte Parser aus Beschreibern | **EverParse ist der nächste Verwandte** und ernsthaft zu prüfen, bevor hier eine Zeile entsteht |
| **Verus / GNATprove** | Beweise auf vorhandenem Code | beweisen, was jemand modelliert hat — Gabbro erzeugt, was niemand modellieren muss |

**Vor dem ersten Übersetzerlauf gehört EverParse gelesen und gemessen.** Wenn es trägt, ist Gabbro
überflüssig, und das wäre das beste Ergebnis dieses Ordners.

---

## Wo was steht

| Datei | Inhalt |
|---|---|
| `README.md` | dies — Zweck, Regeln, Syntaxentwurf |
| `TODO.md` | **ausschließlich Offenes** |
| `ROADMAP.md` | Phasen mit **Entscheidungstoren**: jede Phase liefert eine Zahl, die über die nächste entscheidet |

---

# Was fehlt für einen KOMPLETTEN Kernel — und für Syscalls ohne Assembler

Die Frage gehört beantwortet, bevor der Kernel-Zweig sein Tor bekommt, weil die Antwort seine
Grössenordnung bestimmt. Sie steht hier als **Liste**, nicht als Zusage.

## Syscalls ohne Assembler — was die Sprache dafür können muss

Der Eintritt ist heute Assembler aus **einem** Grund: die CPU übergibt die Kontrolle in einem
Maschinenzustand, den keine Hochsprache zusichert. Register müssen gerettet werden, **bevor**
irgendein übersetzter Prolog läuft. Ohne Assembler braucht es vier Dinge im Sprachkern:

1. **Eintrittsfunktionen mit erklärtem Registerabdruck** — „diese Funktion beginnt im Zustand X
   und darf Register Y nicht anfassen, bevor Z geschehen ist". (Rust: `naked_asm!`,
   Zig: `callconv(.Naked)` — beide reichen den Assembler nur durch.)
2. **Registergebundene Werte** — „diese Grösse *ist* `rdi`", damit der Übersetzer nichts spillen
   muss, um sie zu benennen.
3. **Eine eigene Aufrufkonvention** — die Interrupt-Frame-ABI, nicht die der Plattform.
4. **`iretq`/`eret` als Sprachkonstrukt**: ein **typisierter Übergang in einen gespeicherten
   Kontext**. Bemerkenswert — das ist kein neues Konzept, sondern der `state`-Übergang von oben,
   angewandt auf den Maschinenzustand.

Das ist die Klasse **typisierter Assemblersprachen** (TAL) und keine Erfindung.

> **Aber es entfernt das Vertrauen nicht, es VERLAGERT es.** Die Instruktionsfolge muss weiterhin
> jemand erzeugen — dann der Übersetzer statt der Mensch. Der Gewinn ist trotzdem echt und derselbe
> wie bei der Axiomschicht, eine Ebene tiefer: **eine Implementierung, einmal geprüft, statt 153
> Fundstellen, die nie jemand einzeln prüft.** Wer „ohne Assembler" als „ohne unbewiesene Fläche"
> liest, hat die Verlagerung mit einer Beseitigung verwechselt.

## Was darüber hinaus fehlt, gemessen an Caprock

| Was | warum es nicht nebenbei geht |
|---|---|
| **Nebenläufigkeit** | Atomics, Barrieren — und die Eigenschaft „der Aufrufer hält den Lock", die **weder SPARK noch Rust** ausdrücken kann. Gabbro bräuchte Regionen + Fähigkeiten im Typsystem. Der grösste Einzelposten |
| **Volatile/MMIO** | vier Geschmacksrichtungen wie in SPARK (`Async_Readers`/`Writers`, `Effective_Reads`/`Writes`). Machbar, aber Sprachkern |
| **Zwei Adressachsen** | `Pa` und `Iova` getrennt, Arithmetik darauf — `index into` verallgemeinert dorthin, ist aber nicht dasselbe |
| **Bau und ABI** | Multiboot-Kopf, Sektionen, Ausrichtung, ELF32-Abstieg. Kein Sprachthema, muss aber existieren — und hat diese Woche einen halben Tag gekostet |
| **Kein Laufzeitsystem** | kein Allokator, kein Panik-Apparat, kein Abwickeln |
| **FFI** | für HACL\*/EverCrypt — und jede FFI-Grenze **bricht die Garantie** |
| **Beobachtbarkeit** | dieses Projekt lebt von Berichtszeilen. Eine Sprache, in der Formatierung teuer oder unmöglich ist, ist hier unbrauchbar |

**Die ehrliche Summe: das ist eine Allzweck-Systemsprache.** Damit ist der Kernel-Zweig kein
Anhängsel des Formaterzeugers, sondern ein zweites Projekt — und die Kernthese dieses Ordners
(geschlossene Domäne ⇒ Spezifikation billig) gilt für ihn **nicht**.

- [ ] **Vor dem Tor des Zweigs zu entscheiden:** Wird das eine Sprache mit zwei Bibliotheken, oder
      zwei Sprachen? Unentschieden ist die teuerste Variante — und diese Liste ist das Argument
      dafür, dass die Entscheidung nicht vertagt werden kann, weil sie die Grössenordnung ändert.
