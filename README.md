# Basalt

Eine **enge** Sprache für Formate und Tabellen, die nach **C** übersetzt und deren erzeugter Code
**per Konstruktion** beweisbar ist. Übersetzer in **sicherem Rust** (`forbid(unsafe_code)`).

Stand dieser Notiz: 2026-08-13. Nichts davon ist gebaut — das hier ist der Entwurf, nicht ein
Bericht. Was gemessen ist, steht als gemessen da; alles andere ist ausdrücklich Absicht.

---

## Warum der Name

Caprock ist die harte Deckschicht über weicherem Gestein — und sie besteht oft buchstäblich aus
**Basalt**. Basalt kühlt in regelmäßigen Säulen aus: dieselbe Struktur, viele Male, ohne dass
jemand sie einzeln entwirft. Genau das ist der Anspruch dieser Sprache.

Das Wort ist in Deutsch und Englisch identisch und mit keiner verbreiteten Sprache belegt.

---

## Was Basalt ist — und was ausdrücklich nicht

**Basalt beschreibt Formate und Tabellen und erzeugt daraus Leser, Schreiber und Prüfer.**
Es ist **keine** Allzwecksprache. Kein Kernel wird darin geschrieben, kein Treiber, kein Dienst.

Der Grund ist eine Erfahrung, keine Vorliebe: **funktionale Korrektheit (»Gold«) ist teuer, weil
die Spezifikation teuer ist** — bei seL4 rund 200 000 Zeilen Isabelle auf 10 000 Zeilen C, ein
Verhältnis von 20:1. Keine Sprachgestaltung nimmt einem das ab, solange die Domäne offen ist.

**Für eine enge Domäne kippt die Rechnung**, weil die Invarianten im *Sprachentwurf* stecken statt
in einer Spezifikation je Funktion. Der Beschreiber **ist** die Spezifikation. Man beweist nicht,
dass der Parser dem Format entspricht — man erzeugt ihn daraus.

### Die Domäne, aus echten Fundstellen

| Muster | wo es in Caprock vorkommt |
|---|---|
| Drahtformat mit Versionskopf | Manifest, Checkpoint, Sidecar, virtio-Deskriptoren, GPT, FAT |
| Tabelle mit Invarianten | Cap-Space + CDT, Seitentabellen, IRTE, DMAR |
| Aufzählung mit Absage | Fehlercodes, `MANGEL_*`, `LocalReason` |

Fünfmal dasselbe Muster von Hand ist fünfmal dieselbe Falle.

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

### 2. Keine Zeiger — nur Versätze, und jeder gegen eine Länge im Geltungsbereich

Ein Versatz ohne die Länge, gegen die er gilt, ist in Basalt nicht schreibbar. Die Bereichsprüfung
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

```basalt
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

* `basalt_manifest_lesen(const uint8_t *p, size_t n, ManifestEintrag *out) -> BasaltErr`
* `basalt_manifest_schreiben(const ManifestEintrag *in, uint8_t *p, size_t n) -> BasaltErr`
* je Abweisungsgrund ein eigener Code (`BASALT_VERSION_FREMD`, `BASALT_RESERVIERT_GESETZT`,
  `BASALT_ZU_KURZ`, `BASALT_FELD_AUSSERHALB`)
* eine C-`struct` mit **festen** Breiten, kein Padding-Vertrauen

`where`-Klauseln sind Teil des Formats, nicht ein nachgelagerter Test: der Leser gibt eine Absage
zurück, wenn sie nicht gelten — er liefert **niemals** eine Struktur, die sie verletzt.

### Eine Tabelle mit Invarianten

```basalt
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

Daraus entstehen der Prüfer (`basalt_capspace_audit`), die Zugriffshelfer und — das ist der Punkt —
die **Bereichsprüfung an jeder Indizierung, ohne dass jemand sie schreibt**.

`wrapping` ist ausdrücklich zu schreiben. Ein Umlauf, den niemand ausgesprochen hat, ist ein
Fehler; einer, der ausgesprochen ist, ist ein Entwurf.

> *Fundstelle:* `refcount -= 1` ohne Bedingung, und `overflow-checks` ist im Release nicht gesetzt
> — also kein Absturz, sondern **stiller Umlauf auf `0xFFFF_FFFF`**: Objekt nie finalisiert,
> Region nie freigegeben.

### Eine Aufzählung mit Absagen

```basalt
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

* **Zwei Verbraucher ohne Umweg**: Rust bindet C über FFI, SPARK ebenso — Basalt-Erzeugnisse
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

## Was Basalt **nicht** löst

Diese Liste steht hier, damit sie nicht später als Enttäuschung entdeckt wird.

* **Falsche Formate.** Basalt beweist, dass der Leser dem Beschreiber entspricht — nicht, dass der
  Beschreiber der Wirklichkeit entspricht. Wer die Bytereihenfolge falsch aufschreibt, bekommt
  einen beweisbar korrekten falschen Leser.
* **Hardware-Zusagen.** Dass eine IOMMU-Einheit `TE=1` ehrt, steht in keinem Formalismus.
* **Nebenläufigkeit.** Basalt beschreibt Daten, nicht Abläufe. Wer den Beschreiber unter einer
  Sperre liest, muss das weiterhin selbst wissen — auch SPARK kann »der Aufrufer hält den
  Spinlock« nicht ausdrücken.
* **Die Klasse Fehler, die diese Woche wehtat.** Ein fehlendes `US`-Bit auf der Zwischenebene,
  ein Index über den Slot statt über die Identität, eine Wachseite, die einen Farbstreifen
  sprengt: **Fehler über Bedeutung, nicht über Form.** Gefunden hat die alle die Messdisziplin,
  und daran ändert Basalt nichts.

---

## Verwandtschaft, und warum trotzdem etwas Eigenes

| Projekt | was es kann | warum es hier nicht reicht |
|---|---|---|
| **F\*/Low\*** | Gold, extrahiert nach C, in HACL\* ausgeliefert | Allzwecksprache — die Spezifikationslast bleibt |
| **Kaitai Struct** | Formate deklarativ, viele Zielsprachen | keine Beweise, keine Absage-Disziplin, kein `no_std`-C |
| **P4, Nail, EverParse** | verifizierte Parser aus Beschreibern | **EverParse ist der nächste Verwandte** und ernsthaft zu prüfen, bevor hier eine Zeile entsteht |
| **Verus / GNATprove** | Beweise auf vorhandenem Code | beweisen, was jemand modelliert hat — Basalt erzeugt, was niemand modellieren muss |

**Vor dem ersten Übersetzerlauf gehört EverParse gelesen und gemessen.** Wenn es trägt, ist Basalt
überflüssig, und das wäre das beste Ergebnis dieses Ordners.

---

## Wo was steht

| Datei | Inhalt |
|---|---|
| `README.md` | dies — Zweck, Regeln, Syntaxentwurf |
| `TODO.md` | **ausschließlich Offenes** |
| `ROADMAP.md` | Phasen mit **Entscheidungstoren**: jede Phase liefert eine Zahl, die über die nächste entscheidet |
