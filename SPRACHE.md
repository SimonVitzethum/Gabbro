# Gabbro — die Sprache

**Vier Mechanismen, zwei Deklarationsregeln, eine Bibliotheksschicht — und die Konstrukte, die
Kernel, Treiber und Programme vollstaendig ausdrueckbar machen.**

Die **Schreibweise** steht in [`SYNTAX.md`](SYNTAX.md) (119 EBNF-Regeln, geschlossen, erreichbar,
Wortschatz deckt jedes Terminal). Die **Beweisarchitektur** in [`BEWEIS.md`](BEWEIS.md), der Weg in
[`PLAN.md`](PLAN.md).

> **Diese Datei ist am 2026-08-14 zusammengezogen worden.** Sie enthielt vorher nur die
> Mechanismen; die Festlegung und die drei Ergaenzungen lagen als eigene Dateien daneben. **Das war
> falsch abgelegt: sie sind zentrale Bestandteile der Sprache, kein Anhang.** Der Text ist
> unveraendert uebernommen, samt der Berichtigungen, die beim Eintragen entstanden sind —
> **strukturell zusammengefuehrt, nicht redaktionell geglaettet.**

---


## 3. Der Kern — vier Mechanismen und zwei Deklarationsregeln

### M1 — Bereichstypen

Ganzzahlen tragen ihren **Wertebereich**, und jede Operation muss darin bleiben. Das ist Adas
Trick, und **genau er** hat S1a/S1b gefunden — nicht „Ada ist sicherer".

```gabbro
type SlotIdx  = u32 in 0 .. NSLOTS-1
type Refcount = u32 in 0 .. u32::max
type Zyklen   = u64 in 1 .. u64'max      -- Null ist ein Befund, kein Messwert
```

### M2 — Lineare Werte, auch geisterhafte

Ein linearer Wert **muss** verbraucht werden; ein geisterhafter existiert nur im Beweis und wird
vor der Codeerzeugung gelöscht (**kein Byte, keine Halde** — an Verus gemessen).

```gabbro
linear type Parked                 -- muss zugelassen werden
linear ghost type Held(CAPS)             -- Sperrbeleg, kostenlos
linear ghost type Duty(check)         -- eine unerfuellte Pruefzusage
```

### M3 — Adressräume und Zugriffsrechte am Zeiger

Ein Zeiger trägt **wohin** er zeigt und **was** man damit darf. C hat das als Erweiterung; hier
ist es die Voreinstellung.

```gabbro
ptr<mmio, w>  gcmd            -- ein Lesen zum Zurueckschreiben ist nicht schreibbar
ptr<dma,  rw> puffer
ptr<code, x@ring3> sonde
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

---

## 3b. Die zwanzig fallen heraus — als Bibliothek, nicht als Syntax

**Das ist der Test der Reduktion.** Bleibt eine Zeile ohne Ableitung, fehlt ein Mechanismus.

| vormals „Konstrukt" | folgt aus | wie |
|---|---|---|
| vormals *„einheit“* (Pa/Iova/Farben) | **D1** | undurchsichtiger Neutyp |
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
| vormals *„wirkung“* (Global/Depends) | **M2** | Wirkungen **sind** geisterhafte Fähigkeiten im Parameter |
| `traverse` (S1a) | **M4** | Schreibweise, kein Mechanismus |
| `format` / `table` | Bibliothek | Deklarationen über M1/M3/D2 |
| **`check`** | **M2** | **s. u. — die schönste Ableitung** |

### Die vier alten Entwurfsregeln — sie sind jetzt ABLEITUNGEN, keine Regeln

Regel 1 ist **M4**, Regel 2 ist **M1 + M4**, Regel 3 ist **D2**, Regel 4 ist **D1 + D2**. Sie
stehen hier weiter, weil ihre **Fundstellen** die Evidenz sind — jede ist ein bezahlter Fehler.

Jede ist als Antwort auf einen bezahlten Fehler formuliert. Die Konstrukte selbst stehen in
der Bibliotheksschicht unten; hier stehen die Regeln und ihre Fundstellen.

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
Sprache zwingt damit in die teure Fassung (Bitmap oder Generationsstempel), s. `traverse` unten.

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

---

## Unsicherer Bootcode — mit BEWEIS, dass er danach nie wieder läuft

Ein Kernel braucht ihn: rohe Physadressen, bevor die MMU steht; Multiboot-Strukturen; die
Kern-Übergabe. Die Forderung ist nicht „möglichst wenig `unsafe`", sondern **„`unsafe`, aber
nachweislich abgelaufen"** — und das ist strikt stärker als alles, was Rust heute kann.

**Es fällt aus M2 heraus, ohne neuen Mechanismus:**

```gabbro
linear ghost type BootPhase              -- genau EINE Instanz, beim Eintritt erzeugt

raw fn phys_write(p: Pa, w: u64) requires &BootPhase
raw fn mb_info_read(p: Pa) -> Info      requires &BootPhase

fn boot_end(t: BootPhase)               -- VERBRAUCHT die Marke; es gibt keine zweite
    effects { drops code<boot> }                  -- ... und bildet .boot im selben Zug ab
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

---

## Rennfreiheit — jetzt einzuplanen, sonst nie

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

---

## Was Kernel-Logik ausserdem verlangt — und wo das Vertrauen sich sammelt

„Alle Kernel-Logik ausdrückbar" ist eine Vollständigkeitsforderung, und sie hat eine Liste. M1–M4
decken sie **nicht** allein.

| Was | Antwort | ehrlich dazu |
|---|---|---|
| **Absichtliche Nichtterminierung** (Leerlauf-, Hauptschleife) | `divergent fn` — **ausgesprochen**, nie versehentlich | M4 verlangt sonst ein Abstiegsmass; die Ausnahme muss benannt sein, nicht erschlichen |
| **Unterbrechbarkeit** | eine **Wirkung**: `masks irqs` bzw. deren Abwesenheit. Ein Handler ist kein Aufruf — er kann zwischen zwei beliebigen Anweisungen laufen | fällt aus M2, wenn die IRQ-Maske ein linearer Beleg ist. Falle 93 (Guard über den Rumpf) ist genau das |
| **Kontextwechsel** | Sprachprimitiv `switch_to(from: &mut Context, to: &Context)` mit Vertrag über den Maschinenzustand | Stapelwechsel ist in **keiner** strukturierten Sprache ausdrückbar. Das ist der `state`-Übergang auf Maschinenebene — und er wird **emittiert**, nicht geschrieben |
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

> **Die ehrliche Summe: M1–M4 + Axiomschicht + drei Primitive** (`divergent`, `switch_to`, Prüftor).
> Die Axiomschicht ist die grösste unbewiesene Fläche der ganzen Sprache — grösser als der
> Übersetzer —, und sie ist **zählbar**: eine Ratsche über der Menge der Axiome, die nur fallen darf.

### Was NICHT herausfällt — und darum ehrlich danebensteht

| | |
|---|---|
| **Verträge** (`requires`/`ensures` über deklarierte Prädikate) | nötig für Falle 1/2 (Bedingung über Registergrenzen). Damit ist die Linie gewandert, wie `README.md` vorhergesagt hat — und **allgemeine Quantoren über Rechenausdrücke bleiben trotzdem draussen** |
| **Der Eintritt (Assembler)** | M1–M4 sagen nichts über Registerabdrücke. **Neu seit der Zielsetzung „C + iasm": er ist Teil der AUSGABE**, also aus einer Beschreibung emittiert statt je Fundstelle geschrieben — vertrauenswürdige Fläche **eine Emissionsstelle statt 161**. Bewiesen ist er weiterhin nicht, und er tötet **0** bezahlte Fallen |
| **Fortschritt** (Aushungern, D8) | kein Mechanismus adressiert ihn |

---

# Die Bibliotheksschicht — was ein Anwender schreibt

### 1. `format` — Drahtformate

Reine Funktion an einer Grenze: Bytes rein, Struktur **oder benannte Absage** raus.

```gabbro
format ManifestEintrag @version 3 endian little {
    program_id  : u32
    entry_len   : u32   where == sizeof(Self)
    iface       : u32
    domain      : u8    in { Trusted = 0, Hardware = 1, User = 2 }
    _pad        : [u8; 3]  reserved
    code_hash   : [u8; 32]
    selector    : GeraeteSelektor
}
```

**Erzeugt:** Leser, Schreiber, C-`struct` mit festen Breiten, **je Abweisungsgrund ein eigener
Code**. `where` ist Teil des Formats: der Leser liefert **niemals** eine Struktur, die es verletzt.

**Offen:** variable Längen (die harten 20 % jedes Parser-Erzeugers, Syntax fehlt) ·
Versionsevolution (liest v3 auch v2 — Absage oder Migration?) · Roundtrip `lesen(schreiben(x)) == x`
im Differenztest.

---

### 2. `table` — Tabellen mit Invarianten

**Achtung: andere Kategorie als `format`.** Ein Format ist eine Funktion, eine Tabelle ist
**mutierter Zustand**. Was Gabbro hier erzeugt, ist eine offene Entscheidung — s. `README`,
Zuschnitt (a)/(b)/(c) — und **sie entscheidet den Wert des ganzen Ordners.**

```gabbro
table CapSpace {
    kapazitaet : const 80256

    slot {
        used   : bool
        object : index into objects
        parent : option index into slot
        first_child, next_sibling : option index into slot
        gen    : u32  wrapping        -- Umlauf ist AUSGESPROCHEN, s. Konstrukt 5
    }

    invariant kind_zeigt_zurueck cost O(n * kette) runs offline:
        forall s where s.parent = Some(p) => s in chain(p.first_child, next_sibling)
}
```

**`cost` und `runs` sind Pflicht, nicht Schmuck.** Eine Invariante ohne Kostenangabe ist
unter dem Kern-Lock kein Audit, sondern ein Ausfall — `colors.rs` hält heute **42 Ticks** und gilt
deshalb als Schuldposten. Und **inkrementelle** Prüfung setzt voraus, dass der Prüfer das Delta
kennt, das **nur der Mutator** kennt: **wer Invarianten im heissen Pfad will, hat Zuschnitt (c)
bereits gewählt.**

---

### 3. `traverse` — Schleifen gibt es nicht

„Endlich" ist das **schwächste** Versprechen: eine Schleife mit Schrittgrenze terminiert und kann
trotzdem ausserhalb der Tabelle indizieren. Genau das ist **S1a**.

```gabbro
traverse geschwister of p
    over  chain(first_child, next_sibling) in slots
    by    unvisited                  -- Kosten: s. u.
    touches reads slots
{ if it == s { found } }
```

| Angabe | tötet |
|---|---|
| `over` | ein Index **ausserhalb der Menge ist nicht formulierbar** (S1a) |
| `by` | Terminierung — und **Zyklen**, wenn der Fortschritt „noch nicht besucht" ist |
| `touches` | fremde Schreibzugriffe; `restrict` **nur an den Parametergrenzen** erzeugter Funktionen |

**`by unbesucht` hat einen Preis, und Regel 3 erzwingt ihn:** ein blosser Schrittzähler
terminiert nur — ein Zyklus würde **stillschweigend abgeschnitten** statt als Absage `Zyklus`
gemeldet, und das wäre Deutung. Also Bitmap (~10 KB über 80 256 Slots, O(n)-Reset) oder
Generationsstempel je Slot. **Die Kostenangabe gehört an `by` selbst:** welche Struktur, wer setzt
sie zurück, was kostet der Reset, darf sie unter dem Lock leben.

---

### 4. `state` — erlaubte Übergänge

Nennt die **zulässigen** Übergänge; alles andere ist nicht formulierbar. Das I9-Fenster
(`used = false` bei `refcount = 1`) wäre damit kein Zufall der Reihenfolge mehr, sondern ein
nicht existierender Übergang.

**Und derselbe Mechanismus trägt eine Ebene tiefer:** `iretq`/`eret` ist ein **typisierter
Übergang in einen gespeicherten Maschinenzustand** — dasselbe Konstrukt, angewandt auf Register
statt auf Felder. Das ist der Grund, warum „Syscalls ohne Assembler" kein Fremdkörper wäre.

---

### 5. Arithmetik mit Vorbedingung

`refcount -= 1` braucht **kein eigenes Konstrukt** — das ist beim Aufschreiben der Grammatik
aufgefallen und hat den Wortschatz um ein Wort verkleinert. **M1 erledigt es:**

```gabbro
type Refcount = u32 in 0 .. u32::max;    -- und dann genuegt:
c.objects[obj].refcount -= 1;            -- unter 0 ist NICHT TYPISIERBAR
```

Der Bereichstyp **ist** die Vorbedingung; ein Unterlauf verlässt ihn und ist damit nicht
typisierbar. Ein früher hier stehendes `decrement … requires …` war ein Schlüsselwort für etwas,
das M1 schon kann. **S1b ist unformulierbar statt hinterher auffindbar. Ein Umlauf, den niemand
ausgesprochen hat, ist ein Fehler; einer, der `wrapping` trägt, ein Entwurf** — genau der
Unterschied zwischen S1b und den Generationen, auf deren absichtlichem Umlauf `resolve` ruht.

---

### 6. `assume` / `falsifier` — Hardware-Annahmen

Kein Formalismus deckt „die VT-d-Einheit ehrt `TE=1`". Die Annahme lässt sich aber **benennen**
und **testbar** machen:

```gabbro
assume vtd_te_wirkt
    "GCMD.TE schaltet die Uebersetzung scharf; DMA ohne Kontexteintrag wird danach
     als Fault gemeldet und nicht durchgelassen."
    falsifier probe_vtd_te
```

Das Muster stammt aus Caprock: **ein Wächter prüft die EXISTENZ eines Grundes, nie seine
WAHRHEIT** — deshalb tragen die Identitätsgründe dort einen Falsifikator.

**Drei Klassen, nicht zwei** — die dritte darf nie wie die erste aussehen:

| Klasse | heisst |
|---|---|
| **falsifiziert** | Sonde lief und hielt — eine **Stichprobe**, kein Beweis |
| **nicht falsifizierbar** | keine Sonde möglich, **mit Grund** (`pprobe` meldet unter KVM grundsätzlich `SKIP`) |
| **nicht gefahren** | offen |

**CPU-Errata sind genau Annahmen, die fast immer halten.** Eine bestandene Sonde prüft *diese*
Maschine, *diese* Konfiguration, *diesen* Augenblick — dieselbe Klasse wie „0 Treffer in
114 Läufen". Der Gewinn ist trotzdem real: **Annahmen werden zählbar und ratschenfähig**, und ein
Beweis, dessen Annahmenmenge niemand kennt, ist ein Beweis ohne Reichweite.

- [ ] Der Falsifikator ist Code wie jeder andere und braucht seine **eigene Sprechprobe**:
      *kann er überhaupt fehlschlagen?*

#### Die Annahmenmenge gehört INS ERZEUGNIS, nicht nur in die Quelle

„Zählbar und ratschenfähig" lebt bisher nur dort, wo der Beschreiber liegt. **Der Verbraucher des
Beweises kennt dessen Reichweite damit nicht.** Also emittiert der Übersetzer sie mit — maschinen-
lesbar, neben dem C:

```
bewiesen unter: vtd_te_wirkt (falsifiziert 2026-08-13)
                x2apic_zweischritt (nicht falsifizierbar: kein x2APIC unter qemu64)
                smmu_stall_model (NICHT GEFAHREN)
```

Zwei Bedingungen, beide aus bezahlten Fehlern:

* **Eine Menge von Namen, keine Zahl.** Eine Ratsche über einer Kardinalzahl greift gegen Zuwachs,
  nicht gegen **Austausch** — und Austausch fühlt sich beim Umbauen wie Fortschritt an. Genau so
  ging `IDENTITY_DEBTS` einmal daneben.
* **Die Klasse steht dabei.** Eine nicht gefahrene Annahme darf im Erzeugnis nicht aussehen wie eine
  falsifizierte; das ist die dritte Klasse von oben, eine Ebene weiter nach aussen getragen.

---

### 7. Wirkungen (`Global`/`Depends`-Form)

Jede Operation nennt, was sie liest und schreibt. Dafür gibt es **eine Messung am Mechanismus**:
im Caprock-Scheduler wurden mit SPARKs `Depends` **63 von 63** Datenabhängigkeiten bewiesen, und
„der Rust-Code liest überall genau einmal in eine Kopie" ging von *gelesen* zu *bewiesen*.
**Die Übertragbarkeit auf Gabbro ist damit angenommen, nicht gemessen** — SPARK prüft vorhandenen
Code, Gabbro erzeugt ihn.

---

### Anhang: `reason` — Regel 3, syntaktisch

Kein achtes Konstrukt, sondern „abweisen, nie deuten" in Schreibweise. Es steht hier, weil die
Domänentabelle „Aufzählung mit Absage" als eigenes Muster führt.

```gabbro
reason MangelGrund {
    Keiner        = 0  "keine Ressource -- der Fehlschlag lag nicht an einem Vorrat"
    KernelStack   = 2  "EL0-Kernel-Stack"
    Seitentabelle = 6  "Speicher fuer eine Seitentabelle"
    GuardTabelle  = 13 "aufgeteilte Seitentabelle fuer die Guard-Page"

    exhaustive                 -- kein `_ => unbekannt`
}
```

`exhaustive` heisst: der erzeugte C-`switch` hat **keinen** `default`, und ein neuer Wert bricht die
Übersetzung. Eine Aufzählung mit Auffangzweig sammelt ungeprüfte Werte an — dieselbe Falle wie ein
Manifestfeld, das nie eingelöst wird und am Tag der Einlösung lauter falsche Werte trägt.

---

---

## Der Erzeuger emittiert auch die ANNOTATIONEN — und das ist ein eigener Kanal

In dieser Architektur gibt der unverifizierte Erzeuger nicht nur Code aus, sondern auch die
Verträge, die der Beweiser prüft. Ein Erzeuger, der versehentlich **abgeschwächte** Verträge
emittiert, liefert einen **grünen Beweis über eine schwächere Aussage** — wörtlich „ein Beweis, der
die Wunschform beweist".

| Mutation im Erzeuger | wer fängt sie |
|---|---|
| **Code** abgeschwächt, Vertrag bleibt | der nachgelagerte **Beweis** fällt |
| **Vertrag** abgeschwächt, Code bleibt | Beweis bleibt grün — nur eine **Mutationsprobe auf der Annotationsemission** |
| **beide** stimmig abgeschwächt | **kein Beweis** — nur der **Differenztest gegen die Handschrift** |

**Jedes Konstrukt unten muss deshalb zweierlei mitbringen:** seine Emission *und* die Mutation, die
zeigt, dass die Emission gattert. Ein Konstrukt ohne diese Mutation ist eine grüne Zeile, die nichts
gattert — dieselbe Klasse wie ein Negativtest über einer Funktion, die niemand ruft.

---


---

# Teil I — Die Festlegung

## FESTLEGUNG — Gabbro, vollständig

**Dritte Fassung der Oberfläche, erste vollständige Festlegung.** Dieses Dokument legt Syntax und
die tragenden Teile dahinter (Typregeln, Beweisarchitektur, C-Absenkung) so fest, dass ein Kernel,
Treiber und Programme — namentlich Caprock — **vollständig** in Gabbro schreibbar sind. Es
**entscheidet** die neun offenen Entwurfsfragen aus `SYNTAX.md` und nimmt die **19 hängenden
Klempnerei-Pflichten in 11 Klassen** aus `MESSUNGEN.md` je mit einem Konstrukt ab.

> **EINGETRAGEN 2026-08-14.** Die Grammatik in [`SYNTAX.md`](SYNTAX.md) ist auf diese Festlegung
> nachgezogen — **112 Regeln, 0 offen, jede von `program` aus erreichbar, 170 Terminale gegen 170
> Wortschatzwörter**, Wächter grün. **Eine Korrektur beim Eintragen:** `obligation` war als
> dreizehntes Wort gezählt, ist aber **kein Quellwort** — es steht im Manifest, also im Erzeugnis.
> Zwölf.

Stand 2026-08-14. **Kein Übersetzer liest das.** Abnahme dieses Dokuments ist nicht Zustimmung,
sondern die **Wiederholung der 74-Pflichten-Messung** gegen diese Fassung: hängende Klempnerei
muss von 19 auf 0 fallen, sonst ist die Festlegung an den verbleibenden Stellen widerlegt.

---

### 0. Die Zusage — und die Nichtzusage

**Gabbro beweist alles außer Logik.**

| | wer | wie |
|---|---|---|
| **Klempnerei** — Index, Überlauf, Alias, Rahmen, Sperre, Rennen, Terminierung, Phase, Blattheit, Publikation | **Gabbro selbst** | Typregeln M1–M4 und erzeugte Schemata. **Kein SMT, kein Löser, keine Heuristik** — „übersetzt es" ist eine Funktion der Quelle, nicht des Löserglücks |
| **Logik** — *diese* Funktion tut *das Richtige* (`ensures` jenseits der Konstruktion) | **der Programmierer**, in jeder Sprache | Gabbro **emittiert** jede offene Logik-Pflicht in ein maschinenlesbares **Pflichtenmanifest** (§15). Nichts geht stillschweigend verloren |
| **Klempnerei, getragen von Logik** (dritte Klasse, §8.3) | gemischt | fällt durch Konstruktion, **wird aber als Logik gebucht**, weil ihre Grundlage eine Logik-Invariante ist |

Die Zusage ist **relativ**: *speichersicher unter A1…An* — die Annahmenmenge (Axiomschicht §12)
steht **im Erzeugnis**, nicht in einer Fußnote. Der Prüfer ist **unverifiziert**; das Vertrauen
sitzt an drei benannten Stellen: Prüfer, syntaxgesteuerte Absenkung, eine `iasm`-Emissionsstelle.

---

### 1. Grundsatz

Gabbro ist **C ohne seine Löcher, plus zwei Dinge**: Bereichstypen (M1) und lineare Werte, auch
geisterhafte (M2). Dazu Adressräume und Rechte am Zeiger (M3), kein ungeprüftes Indizieren und
keine unbeschriebene Schleife (M4), undurchsichtige Neutypen ohne implizite Umwandlung (D1),
vollständige Layouts ohne Auffangzweig (D2). Alles Weitere ist **Einschränkung** von C, nicht
Erweiterung.

Die fünf Entscheidungen **E1–E5** gelten unverändert: englische Schlüsselwörter bei deutschem
Fließtext; anweisungsorientiert, Zuweisung ist kein Ausdruck; nichts ist implizit; Verträge vor dem
Rumpf in fester Reihenfolge; jede Deklaration an genau einer Stelle vollständig.

---

### 2. Lexik und Wortschatz

Lexik unverändert (Bezeichner, Zahlen mit `_`, `--`-Kommentare, kein Gleitkomma im Kern,
Zeichenketten nur in `claim`, `reason`, `assume`, `section`, `unfalsifiable`).

**Der Wortschatz ist geschlossen. Diese Festlegung fügt genau zwölf Quellwörter hinzu** — jedes an
einer Pflicht aus der Messung, keines aus Vorrat:

```
  embeds scale aligned          -- §5.3: PTE ist Zeiger UND Bitfeld (Wurzelproblem)
  walk levels leaf mappings     -- §5.4/§6: Seitentabellen und die achte Domäne
  held                          -- §11.2: Sperrhaltezeit als Zahl (repariert per_pass)
  next                          -- §8: continue; leave gab es schon
  accumulates merge             -- §11.4: Sammelwerte ohne CAS-Schleife
  -- obligation                 -- §15: KEIN Quellwort, es steht im MANIFEST (Erzeugnis)
  extern                        -- §14.4: C-Randfunktionen mit Vertrag
```

Gestrichen wird **nichts**; jedes Wort der zweiten Fassung behält seine Bedeutung, drei bekommen
schärfere Pflichten (`forever`, `publishes`, `breaking`).

---

### 3. Typen und Bereiche — M1, jetzt mit drei Flussregeln

#### 3.1 Deklarationen (unverändert)

```ebnf
typedecl = [ "pub" ] [ "opaque" ] [ "linear" [ "ghost" ] ] [ "tagged" ]
           "type" ident [ "(" typelist ")" ] [ "=" typeexpr ] ";" ;
intty    = ( "u8"|"u16"|"u32"|"u64"|"i8"|"i16"|"i32"|"i64" ) [ "in" range ] ;
range    = expr ".." expr | expr "..<" expr ;
```

Jede Operation muss im Bereich ihres Ergebnistyps bleiben; passt `a + b` nicht ins Ziel, ist das
ein **Übersetzungsfehler, keine Laufzeitprüfung**. Division und Rest verlangen einen Nenner, dessen
Bereich die Null ausschließt.

#### 3.2 Die drei Flussregeln — geschlossen, lokal, vorhersagbar

Die Gegenmessung (`MESSUNGEN.md` überholt: **255 Subtraktionen, 102 flusssensitiv**) hat
gezeigt, dass *eine* Regel nicht reicht und `narrow` allein zum Ritual würde. Es gibt jetzt **genau
drei** Regeln. Sie sind **syntaxgesteuert, ohne Fixpunkt, ohne Löser**: der Prüfer führt je Block
eine **Faktenmenge**, die nur an den drei benannten Stellen wächst und bei **jedem Schreiben auf
eine beteiligte Stelle stirbt**. Schleifen tragen keine Fakten hinein (die Invariante der
Traversierung tut das, §9).

| | Regel | Beispiel |
|---|---|---|
| **V1** | eine geprüfte **Bereichsbedingung** verengt den Bereich der geprüften Stelle im Zweig danach | `if x >= 1 { … }` → `x : u32 in 1..max` |
| **V2** | eine geprüfte **Beziehung zweier Stellen** wird zum Zweigfakt; unter dem Fakt `a >= b` hat `a - b` den Typ `0 .. a.max − b.min`, unter `a > b` den Typ `1 .. a.max − b.min`. Ausschließlich Vergleichsfakten, ausschließlich direkt geprüfte Stellen | `if a >= b { let d = a - b; }` — die **102 Fundstellen** fallen sämtlich unter diese Form |
| **V3** | ein `match` auf einen `tagged`-Typ verengt im Zweig auf die Variante samt Nutzlast | erschöpfend, kein Auffangzweig |

Was **nicht** unter V1–V3 fällt, braucht `narrow place to range else { … }` — eine Anweisung mit
benanntem Ausgang, keine Beweiszeile. **Messlatte bleibt:** wächst `narrow` über die Restmenge der
Gegenmessung hinaus (**≤ 24 Fundstellen** im heutigen Baum), ist die Regelmenge zu klein gewählt
und *das* die Widerlegung — nicht ein weiteres Regelwachstum in Stille.

#### 3.3 Neutypen und Summen (unverändert)

`opaque` verbietet die Umwandlung in beide Richtungen; `tagged` ist der Summentyp und senkt sich
auf C-Union mit Marke ab; `match` darüber ist erschöpfend.

---

### 4. Lineare und geisterhafte Werte — M2

```gabbro
linear type Parked;                      -- echte Ressource: Bytes im Erzeugnis
linear ghost type Held(Lock);            -- Beleg: vor der Codeerzeugung gelöscht
linear ghost type BootPhase;
linear ghost type MayWrite(ThreadId, Pa);
linear ghost type Duty(check);
linear ghost type Member(domain);        -- Zugehörigkeitszeuge, nur erzeugt (§9.2)
```

**Linear heißt linear, nicht affin:** ein linearer Wert wird genau einmal verbraucht. Fallenlassen
ist ein Übersetzungsfehler; `leave`/`return` aus einem Bereich, der lineare Werte hält, verlangt
deren Nennung (`leaves`). Kopieren gibt es nicht (E3). Geisterwerte haben **keine Absenkung**:
kein Byte, keine Halde, kein Zyklus.

**Wer Zeugen erzeugen darf, ist geschlossen:** `Held` nur der `locks`-Block, `Member` nur die
Domänenaufzählung des Übersetzers, `MayWrite` nur die erzeugte Cap-Auflösung, `Duty` nur `check`,
`BootPhase` nur der Eintrittspfad. Ein von Hand gebauter Beleg ist damit ein **Typfehler** — das
ist das an Verus gemessene Ergebnis („selbstgebauter Beleg: Typfehler"), als Sprachregel.

---

### 5. Zeiger, Adressräume, eingebettete Zeiger — M3

#### 5.1 Räume und Rechte (unverändert)

```ebnf
ptrty  = "ptr" "<" space "," rights ">" typeexpr ;
space  = "normal" | "mmio" | "dma" | "code" | "boot" | ident ;
rights = right { "+" right } ;
right  = "r" | "w" | "rw" | "x" | "own" [ "@" ident ] ;
```

Die Barriere folgt aus dem **Raum**: ein Store nach `dma` emittiert die Publikationsbarriere der
Zielarchitektur, ein `mmio`-Zugriff ist volatil und nicht umsortierbar. `own` ist das
Eigentumsrecht (Freigabe), damit ist `Finalized` ohne Lebenszeiten ausdrückbar.

#### 5.2 Zeigerarithmetik hat genau eine Form

`place[expr]` mit M1-beschränktem Index und `offset_into` in Formaten. Sonst keine.

#### 5.3 `embeds` — **das Wurzelproblem: ein PTE ist zugleich Zeiger und Bitfeld**

```ebnf
field    = ident ":" fieldty [ "@" bitpos ] [ "offset_into" ident ]
           [ "where" pred ] [ "reserved" ] "," ;
fieldty  = typeexpr
         | typeexpr "embeds" "[" int ":" int "]" [ "scale" constexpr ] ;
```

Ein `embeds`-Feld **trägt einen typisierten Wert in einem Bitbereich**, skaliert:

```gabbro
format Pte endian little {
    present  : bool @0,
    writable : bool @1,
    user     : bool @2,
    nx       : bool @63,
    pfn      : Pa embeds [51:12] scale 4096 where aligned(it, 4096),
}
```

Lesen von `pfn` liefert `Pa` (Bits `[51:12] << 12`); Schreiben verlangt die `where`-Bedingung —
`aligned(it, 4096)` ist ein eingebautes Prädikat über M1 (die unteren Bits des Bereichs sind
null), **kein Löser**. Die Absenkung ist Maske-und-Schiebung, zur Übersetzungszeit ausgerechnet.
Damit ist die 13-Mehrbitfelder-Klasse aus `vtd.rs` **und** die PTE-Klasse **ein** Konstrukt.

#### 5.4 `walk` — selbstbeschreibende, mehrstufige Tabellen

```ebnf
walkdecl = "walk" ident "levels" constexpr "{"
             "node" ":" array ","
             "down" ":" ident "when" pred ","
             "leaf" ":" pred ","
             { invariant }
           "}" ;
```

```gabbro
walk PageTable levels 4 {
    node : [Pte; 512],
    down : pfn when it.present && !leaf(it),
    leaf : it.present && (level == 0 || it.large),

    invariant wx_disjoint cost O(n) runs online :
        forall m in mappings of Self: !(m.writable && !m.nx);
}
```

`down` nennt das **eingebettete** Feld, über das abgestiegen wird; `levels` ist eine Konstante,
also ist die Tiefe M1-beschränkt und **die Terminierung des Abstiegs fällt durch Konstruktion** —
kein Variant, kein Lemma. Der Übersetzer erzeugt aus der Deklaration die Aufzählung, die
Traversierung, das Induktionsschema (§6) — und die Mutationsoperationen im Zuschnitt (c) (§10.2).

---

### 6. Prädikate — die Linie, mit der achten Domäne

```ebnf
quant  = ( "forall" | "exists" ) ident "in" domain ":" pred ;
domain = "slots" "of" place | "chain" "(" ident "," ident ")" "in" place
       | "descendants" "of" place | "queue" place | "fields" "of" path
       | "elems" "of" place | "threads"
       | "mappings" "of" place ;              (* NEU — erzeugt aus einer walk-Deklaration *)
```

**Acht Domänen, geschlossen. Schachtelung höchstens zwei. `old(place)` nur in `ensures`.**

`mappings of` quantifiziert über alle erreichbaren Blatt-Einträge einer `walk`-Struktur, samt
virtueller Adresse und Ebene — damit ist **W^X über die zweistufige Seitentabelle**
(`mmu.rs:1283`, die eine unformulierbare Pflicht der Messung) formulierbar. Die Domäne ist
**erzeugt aus der Deklaration**, nicht benutzerdefiniert: die Linie steht.

Unverändert: keine benutzerdefinierten Quantorendomänen, keine Rekursion in `spec fn`, keine
handgeschriebenen Lemmata. Die eine Ausnahme bleibt `by induction over <domain>` — sie **nennt**
das erzeugte Schema (Vorhersagbarkeit), sie beweist nicht. Fällt eine Eigenschaft aus den acht
Domänen heraus, ist sie **nicht formulierbar** — sie wandert als benannte `obligation` ins
Manifest (§15), nicht in einen Kommentar.

---

### 7. Funktionen, Verträge, Kosten — E4

```ebnf
fndecl = [ "pub" ] [ "spec" | "impl" | "raw" | "divergent" | "prim" | "extern" ]
         "fn" ident "(" [ params ] ")" [ "->" typeexpr ]
         [ "requires"  predlist ]
         [ "ensures"   predlist ]
         [ "maintains" identlist ]
         [ "effects"   "{" efflist "}" ]        (* PFLICHT ausser bei spec fn *)
         [ "costs"     "<=" expr "ops" ]
         [ "by"        inductlist ]
         [ "section" string ] [ "arch" ident ] [ "when" constexpr ]
         ( block | "=" pred ";" | ";" ) ;
```

**`effects` ist Pflicht und nicht fail-open**; wer nichts anfasst, schreibt `effects { pure }`,
und das wird geprüft.

**`costs` zählt Operationen, und die Einheit ist definiert:** 1 op = eine Gabbro-Primitive
(Zuweisung, arithmetische Operation, Laden, Speichern; ein Aufruf zählt die deklarierten `costs`
des Gerufenen; eine Traversierung zählt Rumpfkosten × Domänenschranke; Zweige zählen das Maximum).
Das ist eine **Eigenschaft des Programms** (D10), statisch ausgerechnet, keine Zeitmessung — und
sie ist die Größe, in der `per_pass`, `held` und `bounded` sprechen. Zyklen gibt es in der Sprache
nicht.

---

### 8. Anweisungen

#### 8.1 Bestand

`let` (mit `else (e) { … }` als einziger Fehlerfortpflanzung: der Zweig divergiert oder kehrt
zurück), Zuweisung (kein Ausdruck), `if`, erschöpfendes `match`, `narrow … else`, `locks`-Block,
`return`.

#### 8.2 `leave` und `next`

```ebnf
leavestmt = "leave" ident ";" ;
nextstmt  = "next"  ident ";" ;
```

Beide zielen auf eine **benannte** Schleifenform. `leave` aus `forever` ist erlaubt und ist die
geordnete Abschaltung: die `leaves`-Klausel nennt die linearen Werte, die den Ausgang verlassen.
`break`/`continue` ohne Namen gibt es nicht — bei geschachtelten Schleifen ist das Ziel sonst
Konvention statt Syntax.

#### 8.3 `breaking` — mit Buchungsregel

```ebnf
breakstmt = "breaking" identlist block ;
```

Im Block ist die Invariante **als Prämisse nicht verfügbar**: Funktionen mit `requires I` oder
`maintains I` sind nicht aufrufbar (Effekt-geprüft). Am Blockende ist I wiederherzustellen —
**durch Konstruktion nur, wenn der Block mit einer erzeugten Operation der Struktur schließt**;
sonst ist die Wiederherstellung eine **`obligation`** im Manifest. Das ist die dritte Klasse
„Klempnerei, getragen von Logik", als Regel: *fällt eine Klempnerei-Pflicht nur über eine
Logik-Invariante, wird sie als Logik gebucht.* Ohne diese Regel wird „fällt durch Konstruktion"
zur bequemen Buchung — der `depleted_count`-Streitfall ist damit entschieden.

---

### 9. Schleifen — drei Formen, alle repariert

#### 9.1 Grammatik

```ebnf
loopform = traverse | retry | forever ;

traverse = "traverse" ident [ "of" expr ]
           "over" domain
           "by" ( "unvisited" | "consuming" | "decreasing" expr )
           [ "touches" efflist ]
           block ;

retry    = "retry" [ ident ] [ "until" pred ]
           "bounded" expr "ops"
           [ "progress" ident ]
           "on_exceeded" ident
           [ "effects" "{" efflist "}" ]
           block ;

forever  = "forever" [ ident ]
           "per_pass" "bounded" expr "ops"
           "on_exceeded" ident                   (* JETZT PFLICHT — D11 *)
           "effects" "{" efflist "}"
           [ "progress" ident ]
           [ "leaves" identlist ]
           block ;
```

#### 9.2 `by consuming` — mit der Zeugenordnung, die der vierte Papierversuch verlangt hat

Die Laufvariable ist ein `linear ghost Member(domain)`, den der Rumpf verbrauchen **muss** (M2).
**Die Ordnung ist Teil der Domäne, nicht des Aufrufs:** eine Domäne, die `by consuming` anbietet,
liefert ihre Zeugen in der **von der Struktur erzeugten wohlfundierten Ordnung** — für
`descendants of` ist das *tiefenfallend* (Kinder vor Eltern), für `chain` die Kettenfolge, für
`mappings of` blattaufwärts. Der Zeuge trägt dadurch nicht nur Zugehörigkeit, sondern die Zusage
*„alle Nachfolger in der Ordnung sind bereits verbraucht"* — und **genau das ist Blattheit zum
Verbrauchszeitpunkt**. `delete_leaf(it)` verlangt diese Zusage als `requires`; sie kommt aus der
Ordnung, nicht aus einer Laufzeitprüfung.

**Buchung, ehrlich:** die Entsprechung „Zeugenmenge leer ⇒ Menge leer" und die Ordnungserhaltung
unter der erzeugten Mutation fallen **einmal je Konstrukt in der Schablone des Erzeugers** an —
amortisiert, nicht beseitigt. Die Schablone gehört zur vertrauenskritischen Fläche (§0) und steht
im Pflichtenmanifest als geschlossener Posten mit Fundstelle.

#### 9.3 `forever` — Sperrwartezeit, entschieden

**Sperrwartezeit zählt nicht in `per_pass` — und darf trotzdem nicht unbeschränkt sein.** Die
Auflösung ist kompositional statt im Schleifenkonstrukt:

1. Jede Sperre deklariert `held <= K ops` (§11.2). Ein `locks`-Block, dessen Rumpfkosten K
   übersteigen, ist ein Übersetzungsfehler.
2. In `forever`/`retry` ist nur eine Sperre **mit** `held`-Angabe nehmbar. Der Ticket-Spinlock
   ohne Schranke (`caprock-sync:821`) ist damit in einer Dienstschleife **nicht schreibbar** — das
   Konstrukt nimmt die Pflicht ab, statt sie zu behaupten.
3. `per_pass bounded` zählt die eigenen ops des Durchgangs; die Schranke **darf von
   Durchgangs-Eingaben abhängen** (`per_pass bounded 64 + 12 * lenof(msg) ops`) — damit ist
   Ed25519 über ein Manifest ehrlich beschreibbar statt falsch beschränkt.
4. Die Latenzaussage je Wartestelle ist damit ableitbar (Ranghöhere halten ≤ ihrer `held`-Summe)
   und wird als Zahl ins Erzeugnis emittiert — eine **abgeleitete** Größe, die niemand parallel
   zur Wahrheit führt.

`progress` bleibt: es nennt, **wer** die Schleife beendet — eine Annahme mit Falsifikator; der
Watchdog ist der Falsifikator.

---

### 10. `format`, `table`, `walk` — die Bibliotheksschicht mit erzeugten Mutationen

#### 10.1 `format` (Bestand, plus `embeds`)

Fester Satz: Felder mit Bereichen, `where`-Bedingungen, `offset_into` gegen `lenof(Self)`,
`endian`, Versionen mit **Absage statt Migration** (gemessen: 0 von 11 Formatwechseln waren
Migrationen). Der Leser prüft **einmal am Eintritt** die Pufferlänge; alles Weitere sind bewiesene
Zugriffe ohne Laufzeitprüfung. Der Schreiber ist die Umkehrung; `lesen(schreiben(x)) == x` ist
Pflicht im Differenztest.

#### 10.2 `table` — Zuschnitt (c) ist festgelegt

```ebnf
table    = "table" ident "{" { constdecl | slotdecl | invariant | opdecl } "}" ;
opdecl   = "ops" identlist ";" ;
```

`ops insert, remove, relabel, delete_leaf;` nennt die **erzeugten Mutationen**. Der Erzeuger zeigt
je Operation **einmal über der Deklaration**, dass jede `online`-Invariante erhalten bleibt —
nicht je Aufrufstelle. Handgeschriebene Mutation an einer `table` mit `ops` ist ein
Übersetzungsfehler; eine `table` **ohne** `ops` ist reine Beschreibung mit erzeugtem Prüfer
(Zuschnitt (a)) — beides ist dieselbe Syntax, der Unterschied ist eine Zeile und damit **sichtbar
gewählt** statt schleichend.

Invarianten tragen `cost O(…)` und `runs online | offline` (Bestand): `online` läuft im erzeugten
Mutationspfad und muss in dessen `costs` passen; `offline` ist Diagnostik und läuft im
Prüfgerüst.

#### 10.3 `device` (Bestand)

`class r|w|rw|w1c|rc`, `fields` mit Bitbereichen, `bank … at expr stride … count …` (M1-beschränkt),
`mirrors … from …` einmal je Gerät, `transition` über dem **ganzen geschriebenen Wort** samt
`keeping` — RMW auf `w`-Registern bleibt unformulierbar. Neu: `transition … publishes { place }`
(§11.3) für die Gerätepublikation.

---

### 11. Nebenläufigkeit — vier Reparaturen

#### 11.1 `atomic` — Deklaration schlank, Nutzlast am Store

```ebnf
atomicdecl = [ "pub" ] "atomic" ident ":" typeexpr
             [ "acquire" | "release" | "seq" | "relaxed" ] ";" ;
```

#### 11.2 `lock` — mit Haltezeit

```ebnf
lockdecl = "lock" ident "protects" "{" placelist "}"
           "rank" constexpr [ "held" "<=" constexpr "ops" ] [ "masks" ident ] ";" ;
```

`rank`: Nehmen verlangt echt kleineren Rang (Bestand). `held` ist die deklarierte Haltezeit in
ops; jeder `locks`-Block wird dagegen geprüft. Ohne `held` ist die Sperre in Dienstschleifen
nicht nehmbar (§9.3).

#### 11.3 `publish` — die Publikation steht am Store

```ebnf
publishstmt = place "=" expr "publishes" ( placelist | "nothing" ) ";" ;
```

**Jeder Store an ein `atomic` und jeder Store in einen `dma`-Raum ist ein `publishstmt`** — die
Nutzlast wird dort genannt, wo sie entsteht, mit den dort sichtbaren Indizes
(`FP_OWNER[core] = tid publishes { FP_STATES[tid] };` — der selbstbezügliche Fall ist schreibbar).
Eine **Aussage** als Nutzlast wird als `ghost static` reifiziert und veröffentlicht wie ein Platz
(`STALE_STEP = 2 publishes { ghost dead_in_senders };`). Reine Zähler schreiben
`publishes nothing`, und das ist ein Wort, kein leeres Listenloch. Die Gerätepublikation
(virtio-`avail`) steht an der `transition` des Geräts — die sicherheitskritischste
Veröffentlichung im Baum ist damit erstmals im Modell.

Die Deklaration darf zusätzlich eine **Obermenge** nennen; dann prüft der Übersetzer jede
Store-Nutzlast dagegen. Sie muss es nicht — die Pflicht sitzt am Store.

#### 11.4 `accumulates` — ohne die verbotene Schleife

```ebnf
accdecl = "accumulates" ident ":" typeexpr "merge" ( "max"|"min"|"add"|"or"|"and" ) ";" ;
```

Absenkung: **je Kern eine Zelle** (`relaxed`), Zusammenführung beim Lesen über die
NCORES-beschränkte Schleife. **Kein CAS, keine unbegrenzte Schleife** — der Widerspruch
„der Übersetzer emittiert, was die Sprache verbietet" ist damit aufgelöst, und die Absenkung ist
schneller als die, die sie ersetzt. Die Merge-Menge ist geschlossen (kommutative Monoide).

---

### 12. Boot, Maschine, Axiome (Bestand, präzisiert)

`linear ghost BootPhase`; `raw fn` verlangt sie geliehen; `boot_end` verbraucht sie **und** bildet
`code<boot>` ab — ein Ereignis, die Sonde auf eine `.boot`-Adresse ist der Falsifikator.
`prim fn … -> never` für `switch_to`/`resume` (Kontextwechsel als Primitiv, Stapelwechsel ist in
keiner strukturierten Sprache ausdrückbar); `divergent fn` für ausgesprochene Nichtterminierung.

`assume`/`axiom` mit den drei Klassen (falsifiziert / mit Grund nicht falsifizierbar / **nicht
gefahren = Übersetzungsfehler**). Die Axiomschicht ist die größte unbewiesene Fläche der Sprache
und **ratschenfähig**: wächst sie, um ein Sprachdefizit zu decken, greift Abbruchbedingung 5.

**`iasm`** hat genau eine Emissionsstelle im Übersetzer. Der Eintrittspfad (Registerabdruck,
`iretq`/`eret` als Übergang über dem Maschinenzustand) hat **keinen nachgelagerten Beweiser** —
das Vertrauen schrumpft von 161 Fundstellen auf eine Stelle, es verschwindet nicht. So steht es
im Manifest.

---

### 13. `check` (Bestand)

Unverändert: `claim`, `measures` (die Liste **ist** die Berichtszeile), `gates`, `can_fail`,
`floor`, `counterprobe … expects`. Der Übersetzer erzeugt `linear ghost Duty(check)`; die vier
Übersetzungsfehler fallen aus M1/M2/M3. `check`-Rümpfe und `offline`-Invarianten übersetzen nur
unter `when TESTBUILD` — im Auslieferungs-C existieren sie nicht.

---

### 14. Absenkung nach C — hochperformant, weil beweisend statt prüfend

#### 14.1 Der Grundsatz

**Syntaxgesteuert, nicht optimierend.** Jede Konstruktion hat genau eine C-Form; Optimierung ist
Sache des C-Übersetzers, dem die Absenkung dafür das Beste mitgibt, was sie weiß: `restrict` aus
`effects`, `_Noreturn` aus `never`, konstante Masken aus `embeds`/`fields`, `switch` aus `match`.

#### 14.2 Die Kostenwahrheit, prüfbar

**Was bewiesen ist, wird nicht geprüft.** Bereiche, Indizes, Blattheit, Phasen, Beleg­e — alles
M1/M2-Material ist im C **abwesend**, nicht abgeschaltet. Laufzeitprüfungen existieren an genau
zwei Stellen: am `format`-Eintritt (eine Längenprüfung je Puffer) und in `narrow` (ein Zweig).
Geisterwerte, `progress`, `costs`, Verträge: **null Bytes**.

| Konstrukt | C-Form | Mehrkosten gegen Handschrift |
|---|---|---|
| `intty in range` | nackter C-Typ | **0** — der Bereich ist Beweis, nicht Prüfung |
| `narrow … else` | ein `if` | 0 gegen den `if`, den Handschrift auch braucht |
| `tagged` + `match` | Union+Tag, `switch` | 0 |
| `traverse` | `for` ohne Bound-Checks | 0; `by consuming` erzeugt **keinen** Besucht-Speicher — die Ordnung ist statisch |
| `format`-Leser | Zugriffe nach einer Längenprüfung | 0 gegen korrekte Handschrift |
| `device`/`transition` | ein volatiler Store, Maske konstant | 0 |
| `walk`-Abstieg | Schleife über `levels` (konstant, entrollbar) | 0 |
| `accumulates` | Zelle je Kern, relaxed | **negativ** gegen die CAS-Fassung |
| `lock`/`locks` | die vorhandene Sperrprimitive | 0 |
| Geister, Verträge, `check` (Auslieferung) | — | **0 Bytes** |

**Prüfbar als Abnahme:** je Modul erzeugtes C gegen handgeschriebenes C im Differenz-Benchmark;
Auslösung, wenn erzeugt langsamer als Handschrift + Messrauschen. Das ist die Phase-1-Schwelle,
jetzt als Absenkungseigenschaft formuliert.

#### 14.3 Ausgabeform

Ein Ziel: **C11 (freestanding) + `iasm`**, `-ffreestanding`-tauglich, keine libc-Abhängigkeit im
Kern. Deterministisch: gleiche Quelle, gleiches C, byteweise. Namen stabil aus `path`, damit das
Erzeugnis diffbar ist.

#### 14.4 Der Rand: `extern fn`

```gabbro
extern fn memcpy_fast(dst: ptr<normal, w> u8, src: ptr<normal, r> u8, n: usize)
    effects { writes dst, reads src }
    requires n <= lenof(dst), n <= lenof(src);
```

Ein `extern fn` ist eine C-Randfunktion: ihr Vertrag ist ein **`assume` je Deklaration** und zählt
in die Axiomschicht — der Rand ist damit sichtbar und ratschenfähig statt still.

---

### 15. Das Pflichtenmanifest — Logik geht nicht verloren

Der Übersetzer emittiert je Übersetzungseinheit ein Manifest:

```
obligation revoke.functional      "ensures !exists k in descendants of s: k.used"   offen
obligation breaking.cdt_repair    "Wiederherstellung nach breaking in move_cap"      offen
assumption vtd_te_effective       falsifiziert(probe_vtd_te)
assumption x2apic_two_step        unfalsifizierbar("qemu64 hat kein x2APIC")
closed     consuming.schablone    "Ordnungserhaltung descendants, Erzeuger-Schablone" Fundstelle
```

**Drei Klassen:** offene Logik-Pflichten (der Programmierer oder ein externes Werkzeug), die
Annahmenmenge (Namen mit Klasse, keine Kardinalzahl), geschlossene amortisierte Posten mit
Fundstelle. „Speichersicher unter A1…An, funktional offen an O1…Ok" ist damit ein **Satz im
Erzeugnis**. Die Ratsche läuft über Namen; Austausch ist sichtbar.

---

### 16. Caprock-Vollständigkeit — die Landkarte

| Bereich | trägt | über |
|---|---|---|
| Formate (part, fat, ELF, DTB, ABI, ACPI-dmar, virtio-Deskriptoren) | `format` + `embeds` + `offset_into` + `chain` | §10.1 |
| CapSpace/CDT samt revoke | `table … ops` + `by consuming` + `by induction over` | §10.2, §9.2 |
| Seitentabellen, W^X, IOMMU-Wurzeln | `walk` + `mappings of` + `embeds` | §5.4, §6 |
| Gerätetreiber (VT-d, SMMUv3, virtio, x2APIC) | `device` + `transition publishes` + `bank` | §10.3, §11.3 |
| Scheduler/SMP (Sperren, Phasen, FP-Besitz) | `lock rank held` + `linear ghost` (Held, Parked→admit, MayWrite) + V2 | §11.2, §4, §3.2 |
| Dienstschleifen (virtio-blk, Server) | `forever` mit `on_exceeded`, eingabeabhängigem `per_pass`, `held`-Pflicht | §9.3 |
| Boot, Eintritt, Kontextwechsel | `BootPhase`, `prim`, `iasm`, Axiomschicht | §12 |
| Prüfgerüst (15,7 %) | `check` unter `when TESTBUILD` | §13 |
| Rand (memcpy, Krypto-Kerne) | `extern fn` mit Vertrag als Annahme | §14.4 |
| Bedingte Übersetzung (335 `cfg`) | `when` | Bestand |

**Was bleibt, ist Logik** — `ensures` der algorithmischen Rümpfe (IPC-Fastpath, Scheduler-Wahl,
revoke-Funktionalität), sichtbar im Manifest. Das ist die Zusage aus §0, wörtlich.

---

### 17. Was es absichtlich nicht gibt (ergänzt)

Bestand (`while`, `for`, `goto`, Präprozessor, implizite Umwandlung, `void*`, Auffangzweig,
Ausnahmen, Vererbung, Reflexion, GC, Gleitkomma im Kern, Zuweisung als Ausdruck,
Vorwärtsdeklaration, Selbst-Hosting, benutzerdefinierte Quantorendomänen, Rekursion in `spec fn`,
handgeschriebene Lemmata) — **plus, jetzt genannt statt vergessen:** `break`/`continue` ohne Ziel
(ersetzt durch `leave`/`next` mit Namen), unbenannte Sperrhaltezeit in Dienstschleifen,
CAS-Schleifen als Absenkungsdetail, Migration in Formatversionen, Zyklen als Zeiteinheit.

---

### 18. Die neun Entscheidungen, nummeriert

| # | Frage | Entscheidung |
|---|---|---|
| F1 | 102 relationale Vorbedingungen | **V2**, geschlossene Flussregel; `narrow`-Messlatte ≤ 24 |
| F2 | PTE = Zeiger UND Bitfeld | **`embeds [hi:lo] scale`**; Wurzel gelöst, nicht die Domäne |
| F3 | achte Domäne (W^X) | **`mappings of`**, erzeugt aus `walk` |
| F4 | `per_pass`-Ritual | ops statt Zyklen, `on_exceeded` Pflicht, Wartezeit über **`held`** kompositional, eingabeabhängige Schranke |
| F5 | `publishes` an der falschen Stelle | **Store-Pflicht** (`publishstmt`), Deklaration optional als Obermenge; Geräte über `transition publishes`; Aussagen als `ghost static` |
| F6 | `accumulates`-Widerspruch | **Zelle je Kern + merge**, kein CAS |
| F7 | `break`/`continue` | **`leave`/`next`** mit Zielname; in der Verbotsliste genannt |
| F8 | `breaking` | Invariante als Prämisse gesperrt; Wiederherstellung durch erzeugte Op **oder** `obligation` — Buchungsregel „getragen von Logik" |
| F9 | `depleted_count`-Streitfall | dritte Klasse, Buchung als Logik (§8.3) |

---

### 19. Abnahme dieser Festlegung

1. **Die 74-Pflichten-Messung wiederholen** gegen diese Fassung: hängende Klempnerei 19 → 0,
   sonst Widerlegung an den Reststellen (mit Klasse und Fundstelle).
2. **Die zehn Fragmente** aus dem Scratchpad in den Ordner, auf diese Syntax gezogen, Wächter
   grün (Erreichbarkeit, Terminaldeckung, Sprechprobe in beide Richtungen).
3. **`narrow`-Zählung** am Baum: ≤ 24, sonst ist V1–V3 zu klein.
4. **Kostenwahrheit** (§14.2) je übersetztem Modul im Differenz-Benchmark.
5. Die Zählregel bleibt: Spezifikation ist, **was in der Quelle steht** und vor der Codeerzeugung
   gelöscht wird; Erzeugtes ist Ausgabe. Ziel 0,5:1 für Kernelcode, 1:1 nie überschritten für
   `format`; Abbruch > 3:1 unverändert.


---

# Teil II — Ordering, Eintritt, Boot

## ERGÄNZUNG zur Festlegung — der Rest bis „nur noch Logik"

**Nachtrag zu [`SPRACHE.md`](SPRACHE.md).** Die Bilanz der Festlegung nannte drei Löcher:
die **zwölfte Klasse** (Ordering-Paarung, 2 231 Fundstellen deklariert statt bewiesen), den
**Eintrittspfad** (Syscalls/IRQs ohne Konstrukt) und den **Boot-Unerreichbarkeitsbeweis** (bisher
eine Typregel plus ein Satz Prosa). Dieses Dokument schließt sie und zieht danach die ehrliche
Restliste: was nach allem noch zu beweisen bleibt — und in welcher Klasse.

Stand 2026-08-14. **Neue Wörter (geschlossen, neun):**
`awaits entry regs out preserves clobbers stack dispatch vector`

> **BERICHTIGT beim Eintragen (2026-08-14):** das `timer`-Beispiel schrieb `preserves { all }`.
> **`all` ist kein Wort des Wortschatzes** — ERGAENZUNG 2 §7.1 verlangt die Aufzaehlung, weil D2
> vollstaendig heisst und nicht bequem. Die sechzehn Register stehen jetzt da.

---

### 1. Die zwölfte Klasse: Ordering wird gepaart, nicht deklariert

**Der Fehlbestand:** `atomic … release` legt eine Ordnung fest, aber dass ein `release`-Store und
der zugehörige `acquire`-Load ein **Paar** bilden und die Ordnung für die Nutzlast **reicht**,
prüfte nichts. Nach dem eigenen Kriterium ist das Klempnerei (erwähnt nur die Maschine) — und mit
2 231 Fundstellen der größte ungedeckte Posten des Baums.

#### 1.1 `awaits` — die Gegenseite von `publishes`

```ebnf
awaitload = "let" ident "=" place "awaits" "{" placelist "}" ";" ;
```

Die Festlegung setzte die Publikation an den Store (`FP_OWNER[core] = tid publishes
{ FP_STATES[tid] };`). **Die Ergänzung setzt den Empfang an den Load:**

```gabbro
let owner = FP_OWNER[core] awaits { FP_STATES[owner] };
if owner == my_tid {
    -- HIER ist FP_STATES[owner] lesbar: der Load hat die Sichtbarkeit erworben
}
```

**Drei Regeln, alle Typregeln, kein Speichermodell-Löser:**

1. **Paarungspflicht.** Jeder `awaits`-Load auf ein Atomic verlangt, dass es einen
   `publishes`-Store auf **dasselbe** Atomic mit **denselben** Plätzen gibt (statisch abgeglichen,
   Namensgleichheit nach Indexsubstitution). Ein `awaits` ohne Gegenstück, ein `publishes` ohne
   Empfänger: Übersetzungsfehler — verwaiste Hälften sind genau die Fehlerklasse der 872
   Fundstellen in `threads/mod.rs`.
2. **Sichtbarkeit ist ein Zweigfakt** (V-Regel-Familie aus der Festlegung): erst der geprüfte
   Zweig, der den geladenen Wert bestätigt, macht die erwarteten Plätze lesbar. Ein Lesen
   fremd-publizierter Plätze **ohne** erworbene Sichtbarkeit ist ein Übersetzungsfehler.
3. **Ordnung folgt aus der Paarung, nicht umgekehrt.** `publishes { … }` erzwingt mindestens
   `release` am Store, `awaits` mindestens `acquire` am Load — die Ordnungswörter an der
   Deklaration werden **abgeleitet und geprüft** statt gewählt. `relaxed` ist nur mit
   `publishes nothing`/ohne `awaits` schreibbar (Zähler). `seq` bleibt für Algorithmen, die eine
   **globale** Ordnung brauchen — und genau die fallen nicht unter die Paarung:

> **Grenze, benannt:** Die Paarung deckt Nachrichtenübergabe (Erzeuger→Verbraucher, Besitzwechsel,
> Flaggen mit Nutzlast) — nach der Fundstellenstruktur des Baums die dominante Form. Algorithmen,
> deren Korrektheit an einer globalen seq-Ordnung über **mehrere** Atomics hängt, sind mit `seq`
> schreibbar, aber ihre Korrektheit ist **Logik** und steht als `obligation` im Manifest. Die
> Wiederholungsmessung zählt, wie viele das sind; die Vermutung ist „einstellig", und sie ist als
> Vermutung markiert.

**Absenkung:** exakt die C11-Atomics, die heute dastehen — Mehrkosten 0. Der Gewinn ist nicht im
Erzeugnis, sondern darin, dass ein fehlendes `acquire` **nicht mehr schreibbar** ist.

---

### 2. Der Eintrittspfad: `entry` — Syscalls und IRQs aus einer Deklaration

#### 2.1 Das Konstrukt

```ebnf
entrydecl = "entry" ident [ "vector" constexpr ] "arch" ident "{"
              "regs" "in"  "{" { ident ":" ident "," } "}"
              "regs" "out" "{" { ident ":" ident "," } "}"
              "preserves" "{" identlist "}"
              "clobbers"  "{" identlist "}"
              "stack" ident
              "dispatch" path ";"
            "}" ;
```

```gabbro
entry syscall arch x86_64 {
    regs in  { nr: rax, a0: rdi, a1: rsi, a2: rdx, a3: r10 }
    regs out { ret: rax }
    preserves { rbx, rbp, r12, r13, r14, r15, rsp_user }
    clobbers  { rcx, r11 }                      -- syscall/sysret-Realitaet
    stack KernelStack
    dispatch caprock::syscall::dispatch;
}

entry timer vector 0x20 arch x86_64 {
    regs in {} regs out {}
    preserves { rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp,
                r8, r9, r10, r11, r12, r13, r14, r15 }
    clobbers  {}
    stack IrqStack
    dispatch caprock::irq::timer_tick;
}
```

**Was durch Konstruktion fällt:** Die Registerabdrücke sind **vollständig** — jedes
Architekturregister ist genau einer der drei Mengen zugeordnet, sonst Übersetzungsfehler (D2 auf
Registern). Der Stapelwechsel ist das Primitiv, das keine strukturierte Sprache ausdrückt, hier
als deklarierte Zeile. `dispatch` zeigt auf eine **gewöhnliche Gabbro-Funktion** mit `tagged`
Syscall-Nummer, M1-beschränkt, erschöpfendem `match` — ab der ersten Gabbro-Zeile gelten M1–M4,
und die Grenze Assembler/Sprache ist **eine** Deklaration breit. `resume`/`iretq` ist der
typisierte Rückweg (Bestand §12).

**Was nicht fällt, unverändert ehrlich:** Der Eintrittspfad hat **keinen nachgelagerten
Beweiser**. Die Emission kommt aus der einen `iasm`-Stelle; je `entry` und Architektur gehört eine
**Sonde** in die Abnahmereihe (Benutzerregister nach Rückkehr byteidentisch, `clobbers` wirklich
und ausschließlich verändert, Kernelstack-Kanarienvogel). Deklariert, einmal emittiert,
falsifiziert — nicht bewiesen. So steht es im Manifest, Klasse „Eintritt".

#### 2.2 Ein Ursprung, zwei Erzeugnisse: die Stub-Regel

Aus **derselben** `entry`- und `dispatch`-Deklaration erzeugt der Übersetzer **auch die
Userspace-Stubs** (die Aufrufseite: Register laden, `syscall`, Ergebnis typisieren). ABI-Drift
zwischen Kernel und `programs/` — bisher eine reine Disziplinfrage — wird damit **unschreibbar**:
es gibt nur eine Quelle. Die Treiber- und Programmseite (virtio-blk-Dienstschleife) ruft typisierte
Stubs mit denselben Verträgen, die der Kernel prüft.

#### 2.3 FP-/SIMD-Zustand

Der Kernel behandelt FP-Zustand als **undurchsichtigen Sicherungsbereich**: `opaque type FpArea`
mit deklarierter Größe/Ausrichtung je Architektur; `xsave`/`xrstor` (bzw. FPSIMD-Sicherung auf
aarch64) sind **Axiome** mit Effekt auf `FpArea` und fahrbarem Falsifikator — die
CVE-2018-3665-Klasse (lazy-FP-Leck) ist damit eine `MayWrite`-artige Besitzfrage über `FpArea`
plus ein Axiom, nicht ein Sonderpfad.

---

### 3. Boot-Unerreichbarkeit — ein Satz in drei Schichten

**Zu zeigen:** *Nach `boot_end` ist kein `raw`-Code erreichbar.* Bisher trug das eine Typregel und
ein Falsifikator-Satz. Jetzt ist es ein benannter Satz mit drei Schichten, jede mit ihrer
Vertrauensklasse — weil „statisch heißt nur: kein Aufrufer" (Falle 47) und eine Schicht allein
eine Bitte wäre.

| Schicht | Regel | deckt | Vertrauensklasse |
|---|---|---|---|
| **S1 — Typen** | jede `raw fn` verlangt `&BootPhase`; `BootPhase` ist linear, entsteht genau einmal im Boot-`entry`, wird von `boot_end` verbraucht. Danach **typisiert kein Aufruf** | jede statische Aufrufkette | Prüfer (M2) |
| **S2 — Verweise** | `raw fn` liegt erzwungen in `section ".boot"`; **Adressnahme einer `raw fn` ist nicht schreibbar** (kein `fnptr` auf `raw`, keine Sprungtabelle mit `.boot`-Zielen, kein `ptr<code>`-Literal dorthin). Nicht-`raw`-Code in `.boot` ist ein Übersetzungsfehler | jede dynamische Erreichbarkeit über Zeiger | Prüfer (M3/D2) |
| **S3 — Hardware** | `boot_end` verbraucht die Marke **und** hebt die Abbildung von `.boot` auf, **ein Ereignis**; die Nachbedingung ist als `walk`-Fakt formulierbar: `!exists m in mappings of kernel_root: m.section == boot`. Sonde: Zugriff auf eine `.boot`-Adresse nach `boot_end` **muss faulten** | Sprünge, die S1/S2 nicht sieht (Fehlspekulation ausgenommen, ROP auf tote, aber abgebildete Bytes) | Axiomschicht + Falsifikator |

**Damit ist der Satz nicht „bewiesen im Prüfer", sondern sauber zerlegt:** S1+S2 sind Typregeln
des unverifizierten Prüfers, S3 ist eine Hardware-Annahme mit fahrbarer Sonde. Das Manifest führt
ihn als einen Eintrag mit drei Teilzusagen — stärker als Rusts `#[deprecated]`-Disziplin, stärker
als Verus' affines `tracked` (die Marke ist **linear**: wiederherstellen und kopieren sind
Typfehler), und ohne dass irgendwo „unsafe, aber vorsichtig" steht.

---

### 4. Die Restliste — was nach allem übrig bleibt

Nach Festlegung + Ergänzung gilt: **Caprock, Treiber und Systemprogramme sind vollständig
schreibbar** (Bereichskatalog §16 der Festlegung, plus Eintritt, Stubs, FP, Ordering). Für die
formale Verifikation bleibt, nach Klassen getrennt — denn „nur noch Logik" ist nur ehrlich, wenn
die Vertrauensposten daneben stehen:

#### 4.1 Zu beweisen (die eigentliche Logik-Arbeit)

| # | Posten | Ort |
|---|---|---|
| L1 | `ensures` der algorithmischen Rümpfe: IPC-Fastpath, Scheduler-Wahl, revoke-**Funktionalität** | Manifest, je Funktion |
| L2 | seq-Ordnungs-Algorithmen jenseits der Paarung (§1, vermutet einstellig — zu zählen) | Manifest |
| L3 | `breaking`-Wiederherstellungen ohne erzeugte Schlussoperation | Manifest (Buchungsregel F8/F9) |
| L4 | die eine bekannte unformulierbare Pflicht | Manifest, mit Fundstelle |

**Das — und nur das — muss ein Mensch oder ein externes Werkzeug beweisen.**

#### 4.2 Vertrauen statt Beweis (benannt, ratschenfähig, kein Arbeitsposten)

Der unverifizierte Prüfer; die syntaxgesteuerte Absenkung; die eine `iasm`-Emissionsstelle samt
`entry`-Sonden; die Axiomschicht (privilegierte Befehle, MMU-Modell, `xsave`, `extern fn`); die
amortisierten Erzeuger-Schablonen (`by consuming`-Ordnung, `table ops`-Invariantenerhaltung).
Alles im Manifest mit Namen und Klasse — die Ratsche läuft über Namen.

#### 4.3 Ohne Mechanismus (offen, kein Konstrukt behauptet)

**D8 — Fortschritt und Aushungern.** `progress` benennt Annahmen, beweist keine Lebendigkeit.
Kein Konstrukt dieser beiden Dokumente ändert das, und es steht hier, damit es nicht als erledigt
gelesen wird.

---

### 5. Abnahme dieser Ergänzung

1. **Wiederholungsmessung auf 12 Klassen erweitern:** die 74 Pflichten plus eine
   Ordering-Stichprobe (≥ 30 der 2 231 Fundstellen, geschichtet nach Datei) gegen §1 — jede
   Fundstelle ist Paarung, Zähler oder benannter seq-Fall; ein vierter Ausgang widerlegt §1.
2. **Ein `entry` je Architektur als Fragment** in den Ordner, gegen die reale
   syscall/sysret- bzw. SVC-Konvention gehalten (die `clobbers`-Zeile ist der Prüfstein).
3. **Der Boot-Satz als drei Prüfzeilen** in der Abnahmereihe: S1/S2 als Prüfer-Sprechprobe
   (ein Aufruf nach `boot_end` muss die Übersetzung brechen), S3 als Sonde im Testkernel.
4. **Grammatikvereinigung**: Festlegung + Ergänzung in die EBNF eingehängt, beide Wächter
   (Erreichbarkeit von `program`, Terminaldeckung) grün — diese Fehlerklasse ist zweimal bezahlt.
5. Danach der Widerspruchslauf über den ganzen Ordner, wie nach den sechs Umbauten.


---

# Teil III — RMW, Sichtbarkeit, Eintrittsnachtraege

## ERGÄNZUNG 2 — die offenen Posten der Ergänzung, und der Prüfer als Plan

**Nachtrag zu [`SPRACHE.md`](SPRACHE.md) und [`SPRACHE.md`](SPRACHE.md).** Die erste
Ergänzung hat vier offene Ebenen hinterlassen: Löcher in den eigenen Konstrukten (das größte: RMW),
ungelaufene Messungen, grundsätzlich Unbehauptetes, und die Tatsache, dass keine Zeile Prüfer
existiert. Dieses Dokument schließt die erste Ebene, benennt die zweite und dritte als
Arbeitsliste mit Reihenfolge — und legt für den Prüfer einen **Plan mit Stufen und Toren** fest
statt einer Absichtserklärung.

> **EINGETRAGEN und ABGELEITET (2026-08-14).** Abnahmepunkt 2 dieses Dokuments verlangt, die
> Wortzählung **von der vereinigten Wortschatztabelle** zu nehmen statt von Hand (Falle 80). Der
> Terminaldeckungs-Wächter hat gezählt: **17 neue Wörter** über beide Ergänzungen —
> `awaits entry regs out preserves clobbers stack dispatch vector` (9, die Zählung von
> ERGAENZUNG.md war **richtig**) plus
> `exchange update returns nested ist per cpu masked` (**8**, nicht 5).
> §3.2 nannte selbst schon sieben und liess die Drift absichtlich stehen; **es fehlte zusätzlich
> `masked`.** Damit ist der Punkt geschlossen: **die Zahl kommt jetzt aus der Tabelle, nicht aus
> einem Kopf.**

Stand 2026-08-14. **Neue Wörter (abgeleitet, acht):** `exchange update returns nested ist per cpu masked`
**Berichtigung an ERGAENZUNG.md:** `preserves { all }` benutzte ein Wort außerhalb des
Wortschatzes — das eigene Dokument verletzte die eigene Regel, und der Terminaldeckungs-Wächter
hätte es gefunden, wenn er gelaufen wäre. `all` wird **nicht** aufgenommen; ein Eintritt zählt
seine Register auf (D2 heißt vollständig, nicht bequem). Das Timer-Beispiel ist entsprechend zu
korrigieren.

---

### 1. RMW — die dritte Form der Paarung

**Das Loch:** `publishes` sitzt am Store, `awaits` am Load; `fetch_add`, `compare_exchange`,
Ticket-Nehmen sind **beides in einem Befehl**. Ohne dritte Form zählt die Ordering-Stichprobe
einen vierten Ausgang und widerlegt §1 der Ergänzung an der eigenen Abnahme.

```ebnf
exchstmt = "let" ident "=" place "exchange" xform
           [ "publishes" ( placelist | "nothing" ) ]
           [ "awaits"    "{" placelist "}" ] ";" ;
xform    = "update" "(" ident ")" block          (* der Rumpf rechnet alt -> neu; rein, M1 *)
         | expr "when" pred "returns" ident ;    (* compare-exchange: neu when alt-Bedingung *)
```

```gabbro
-- Ticket nehmen: publiziert nichts, erwartet nichts — reiner Zaehler
let my = NEXT_TICKET exchange update(t) { t + 1 } publishes nothing;

-- Besitzuebernahme: CAS, der bei Erfolg Sichtbarkeit erwirbt UND weitergibt
let won = FP_OWNER[core] exchange my_tid when old == NOBODY returns old
          publishes { FP_STATES[my_tid] }
          awaits    { FP_STATES[old] };
if won == NOBODY { -- Erfolgzweig: awaits-Plaetze lesbar, publishes-Zusage aktiv
}
```

**Regeln, alle Typregeln:**

1. Der `update`-Rumpf ist rein (`effects { pure }` impliziert), M1-typisiert — ein Überlauf im
   RMW ist damit ein Übersetzungsfehler, kein 2-Uhr-nachts-Fund.
2. `publishes` am `exchange` erzwingt mindestens release, `awaits` mindestens acquire, beides
   zusammen acq_rel — **abgeleitet**, wie in Ergänzung §1.3.
3. Sichtbarkeit aus `awaits` entsteht **nur im Erfolgzweig** (V3-artig über das `returns`-Ergebnis).
4. Die Paarungspflicht gilt über alle drei Formen gemeinsam: ein `publishes` kann von einem Load
   **oder** einem `exchange` empfangen werden; abgeglichen wird die vereinigte Menge.

**Absenkung:** `atomic_fetch_*` wo der `update`-Rumpf einem Primitiv entspricht (Abgleich über
eine geschlossene Mustertabelle: `t+1`, `t-1`, `t|m`, `t&m`, `max` via `accumulates`), sonst die
**beschränkte** CAS-Schleife — beschränkt, weil sie im Übersetzer als `retry bounded NCORES *
K ops on_exceeded contention` emittiert wird, mit K aus der `held`-Rechnung: die Sprache emittiert
nichts, was sie verbietet (die `accumulates`-Lektion, verallgemeinert).

---

### 2. Sichtbarkeit über Funktionsgrenzen: `Vis` wird reichbar

**Das Loch:** Sichtbarkeit war ein Zweigfakt und starb an der Funktionsgrenze — prüft eine
Funktion die Flagge und liest eine andere die Nutzlast (der übliche Schnitt), war das korrekte
Programm nicht schreibbar.

**Die Lösung ist kein neues Konstrukt, sondern die konsequente Anwendung von M2:** der
Erfolgzweig eines `awaits`-Loads/-`exchange` **erzeugt** `linear ghost Vis(P)` je erwartetem
Platz. `Vis` ist reichbar wie jeder Geisterwert (Parameter, Rückgabe), das Lesen eines
fremd-publizierten Platzes verlangt `&Vis(P)` geliehen, und die Erzeugerliste aus Festlegung §4
wird um `Vis` ergänzt: **nur** der Erfolgzweig erzeugt es, ein von Hand gebauter Beleg ist ein
Typfehler. Verbrauch ist nicht nötig (Sichtbarkeit erlischt nicht) — `Vis` ist der eine
**affine** Geisterwert der Sprache, und dass er affin statt linear ist, steht hier als
Entscheidung mit Grund, nicht als Versehen.

---

### 3. Eintritt — die fünf Nachträge

#### 3.1 Der Syscall, der nicht zurückkehrt (der Normalfall des Mikrokernels)

`regs out` beschreibt den Rückweg **in denselben Thread**. `dispatch` darf stattdessen in
`switch_to`/`resume` enden — dann gilt: der Eintritt hat **zwei typisierte Ausgänge**, `returns`
(regs out an den Rufer) und `resume k` (voller Kontext aus `k`, der `regs out`-Vertrag ist
gegenstandslos, weil der komplette Registersatz aus dem Zielkontext kommt). Die `entry`-Deklaration
nennt beide:

```gabbro
entry syscall arch x86_64 {
    regs in  { nr: rax, a0: rdi, a1: rsi, a2: rdx, a3: r10 }
    regs out { ret: rax }                  -- Ausgang 1: returns
    preserves { rbx, rbp, r12, r13, r14, r15, rsp_user }
    clobbers  { rcx, r11 }
    stack KernelStack
    dispatch caprock::syscall::dispatch;   -- -> Result | never (resume)
}
```

Der Dispatch-Rückgabetyp `Result | never` macht die zwei Ausgänge im Typ sichtbar: `return`
nimmt Ausgang 1, `resume` Ausgang 2. Der gesicherte Rufer-Kontext ist dabei ein gewöhnlicher
`Context`-Wert — wer ihn fallen ließe, verlöre einen Thread, also ist `Context` **linear**:
`return` verbraucht ihn in den Rückweg, `resume` legt ihn in die Ablage des Schedulers. Ein
vergessener Thread ist damit ein Typfehler — dieselbe Klasse wie `Parked`.

#### 3.2 Stapel je CPU, Verschachtelung, NMI

```ebnf
entryextra = [ "stack" ident [ "per" "cpu" ] [ "ist" constexpr ] ]
             [ "nested" ( "never" | "masked" | "bounded" constexpr ) ] ;
```

`stack KernelStack per cpu` macht den Per-CPU-Stapel zur Deklaration (die Auswahl emittiert die
eine `iasm`-Stelle aus `gs`/`tpidr`). `nested never` (Syscall), `nested masked` (IRQ läuft mit
maskierten Interrupts), `nested bounded 1` (ein Ebenenwechsel erlaubt) — die
Verschachtelungstiefe ist damit M1-Material statt Konvention. NMI und Doppelfehler nehmen
`ist n` (eigener Stapel aus der Interrupt-Stack-Table) und **dürfen nur `raw`-freien, sperrenlosen
Code rufen** (`effects` des Dispatch-Ziels: kein `locks`) — der klassische NMI-Deadlock ist
nicht schreibbar.

Neue Wörter dafür: `nested`, `ist`; `per` und `cpu` — Moment: **vier**, plus `exchange update
returns` aus §1 sind sieben. Die Kopfzeile nennt fünf; das ist genau die Drift, die der
Terminaldeckungs-Wächter fängt, und sie bleibt hier absichtlich stehen als Erinnerung, dass die
**Grammatikvereinigung vor allem anderen** laufen muss (§6, Stufe P1).

#### 3.3 `Result`-Kodierung

Ein `regs out`-Register trägt einen `tagged`-Wert nur über eine deklarierte Kodierung:
`ret: rax = Result { Ok(v) -> v in 0 .. 0x7FFF_FFFF_FFFF_FFFF, Err(e) -> -(e as i64) }` — die
Kodierung steht an der `entry`-Deklaration, Stubs und Dispatcher erzeugen beide Seiten daraus.
Eine Kodierung, die die Wertebereiche überlappen ließe, ist ein Übersetzungsfehler (D2).

#### 3.4 FP-Besitz, entworfen statt skizziert

`FpArea` ist je Thread, **eager** gesichert im `switch_to`-Primitiv (die lazy-Variante ist die
CVE-2018-3665-Falle und wird nicht angeboten — eine Entscheidung, keine Lücke). `MayUseFp(tid)`
ist ein linearer Geisterwert am Thread; `xsave`/`xrstor`-Axiome verlangen ihn geliehen. Damit ist
FP-Zustand Besitz wie jeder andere, und der Sonderpfad verschwindet.

#### 3.5 Der Rand des Boot-Satzes, benannt

S2 deckt die Gabbro-Ebene. **Außerhalb der Sprache liegen:** die frühe Trampolinstrecke
(physisch→virtuell, vor der ersten Gabbro-Zeile) und das Linkerskript (Sektionsgrenzen,
`.boot`-Platzierung). Beide wandern als **benannte Annahmen** in die Axiomschicht
(`assume linker_boot_disjoint … falsifier probe_sections;` — die Sonde liest die Linker-Map im
Prüfgerüst), damit der Boot-Satz keinen stillen Rand hat.

---

### 4. Das Speichermodell als Axiom — bisher stillschweigend

`publishes`/`awaits`/`exchange` versprechen Sichtbarkeit **unter der Annahme**, dass die
C11-Abbildung auf der Zielarchitektur trägt. Das stand nirgends. Jetzt:

```gabbro
assume c11_release_acquire_x86
    "release-Store / acquire-Load auf x86-64 (TSO): Absenkung auf mov genuegt"
    falsifier probe_mp_x86;          -- Message-Passing-Litmus, im Pruefgeruest gefahren
assume c11_release_acquire_aarch64
    "stlr/ldar tragen release/acquire auf aarch64"
    falsifier probe_mp_aarch64;
```

Die Litmus-Sonden (MP, SB, LB — die klassischen drei) laufen im Prüfgerüst als `check` mit
`counterprobe`. Damit ist das Speichermodell **zählbar** Teil der Axiomschicht statt implizit —
und die Zusage aus Ergänzung §1 heißt vollständig: *Paarung korrekt unter c11_*-Annahmen.*

---

### 5. Grundsätzlich offen — unverändert, damit es niemand als erledigt liest

**D8** (Fortschritt/Aushungern): kein Mechanismus, kein Konstrukt behauptet einen. **L4**: die
eine unformulierbare Pflicht. **Die Erzeuger-Schablonen** (`by consuming`-Ordnung, `table ops`):
benannt, nicht entworfen — sie sind Teil des Prüferplans (P4), nicht dieses Dokuments.

---

### 6. Der Prüfer — ein Plan mit Stufen und Toren, keine Absichtserklärung

**Grundsatzentscheidungen, vorab und mit Grund:**

| | Entscheidung | Grund |
|---|---|---|
| Wirtssprache | **Rust, `forbid(unsafe_code)`**, keine Beweiswerkzeug-Abhängigkeit | der Prüfer ist Typregeln, kein Löser; die CSolver/Miri-Disziplin ist vorhanden |
| Architektur | Lexer → Parser (aus der **vereinigten** EBNF, handgeschrieben, kein Generator) → ein Kernbaum → **Prüfpässe in fester Reihenfolge** (Namen, D1/D2, M1+V1–V3, M3, M2, M4/Schleifen, Paarung, effects, costs) → C-Emission | jede Regel dieser drei Dokumente ist genau **ein** Pass oder ein benannter Teil eines Passes — die Spezifikation ist die Passliste |
| Absenkung | syntaxgesteuert, ein Konstrukt → eine C-Form, deterministisch byteweise | Festlegung §14, unverändert |
| Selbstanwendung | **nie** — der Prüfer bleibt Rust (Verbotsliste: Selbst-Hosting) | ein Vorhaben, das seinen Prüfer umbaut, hat keinen |
| Prüfstrategie | jeder Pass mit Sprechprobe in beide Richtungen (Gift fällt, Sauberes passiert) **plus Mutationsprobe auf die Emission** (Code UND Annotation) | die Wunschform-Beweis-Lektion |

**Die Stufen — jede mit Tor, jede kann das Vorhaben beenden:**

| Stufe | Inhalt | Tor (vorab, zweiseitig) |
|---|---|---|
| **P0** | **Wiederholungsmessung auf Papier** gegen Festlegung+Ergänzungen: 74 Pflichten + Ordering-Stichprobe (≥ 30, geschichtet) + `narrow`-Zählung | hängende Klempnerei **0**, Ordering-Stichprobe ohne vierten Ausgang, `narrow` ≤ 24. **Jede Verfehlung: erst Konstrukt nachziehen, KEIN Prüfercode vorher** |
| **P1** | **Grammatikvereinigung** (Festlegung + beide Ergänzungen in die EBNF), beide Wächter, Widerspruchslauf über den Ordner | Wächter grün; Widersprüche 0 offen. Die zweimal bezahlte Fehlerklasse — deshalb **vor** der ersten Prüferzeile |
| **P2** | **Lexer+Parser** über alle Fragmente des Ordners | 100 % der Fragmente parsen; drei Gift-Fragmente scheitern mit benannter Absage |
| **P3** | **M1+V1–V3 als erster Prüfpass**, gegen `space.rs`-Fragment und die 102-Fundstellen-Stichprobe | die Stichprobe typisiert ohne `narrow`-Inflation; Sprechprobe: `refcount -= 1` ohne V-Fakt **fällt** |
| **P4** | **M2 (linear/ghost) + Erzeuger-Schablone** für `table ops`/`by consuming` — hier wird der benannte Posten entworfen und die Schablonen-Beweise werden als geschlossene Manifesteinträge geführt | S1a/S1b/Parked/D0-Klasse als Sprechproben fallen; Mutationsprobe auf die Schablone fängt eine stimmig abgeschwächte Mutation **nicht** — also läuft der Differenztest gegen `space.rs` (Rust) daneben, wie in der Festlegung gebucht |
| **P5** | **C-Emission** für das `space.rs`-Fragment, Differenztest + Differenz-Benchmark gegen die Rust-Fassung | byteidentische Wiederholung; erzeugt ≤ Handschrift + Rauschen; `lesen(schreiben(x)) == x` für die beteiligten Formate |
| **P6** | Paarungs-Pass + `entry`-Emission für **eine** Architektur, Litmus- und `entry`-Sonden im Prüfgerüst | Sonden grün auf echter Hardware oder KVM; die drei Boot-Prüfzeilen laufen |
| **P7** | **Ein Caprock-Modul end-to-end** in Produktion (Kandidat: `caprock-part` — klein, format-lastig, echter Verbraucher), Strangler-Muster, Rust-Fassung bleibt daneben | Abnahmereihe grün, Kennzahl des Moduls gemessen und berichtet (Ziel 0,5:1, Abbruch > 3:1) |

**Reihenfolgeregel, die den ganzen Plan trägt:** P0 und P1 kosten Papier und Skripte, kein
Übersetzerbau — und sie können V2, `awaits`, `embeds` und die Grammatik **einzeln** widerlegen.
Deshalb gilt: **keine Prüferzeile vor Tor P1.** Der Korrekturkreislauf hat in diesem Ordner
mehrfach schneller gelaufen als der Messkreislauf; dieser Plan ist so gebaut, dass das strukturell
nicht mehr geht — jede Stufe verbraucht das Ergebnis der vorigen, wie eine `Duty`.

**Aufwand:** keine Schätzung — eine erfundene wäre schlimmer als keine (die VOLLDECKUNG-Regel).
Stattdessen die Tore; und neben dem Plan steht die Caprock-Frage, die kein Gabbro-Dokument
beantwortet: A4, Z24 und die A3-Folgeposten warten, und dieser Plan ist erst dann mehr als
Papier, wenn P0 gefahren ist.

---

### 7. Abnahme dieser zweiten Ergänzung

1. Das `preserves { all }`-Beispiel in ERGAENZUNG.md berichtigt (Register aufgezählt).
2. Die Wortzählung der Kopfzeile gegen §3.2 aufgelöst — von der vereinigten Wortschatztabelle,
   nicht von Hand (Falle 80: eine Zahl, die ein Mensch parallel zur Wahrheit führt).
3. P0 gefahren, **bevor** irgendetwas anderes aus §6 beginnt.


---

# Teil IV — Hardware-Annahmen und der Bootpfad

## ERGÄNZUNG 3 — Hardware-Annahmen vollständig, und der Bootpfad als Sprache

**Nachtrag zu [`SPRACHE.md`](SPRACHE.md), [`SPRACHE.md`](SPRACHE.md),
[`SPRACHE.md`](SPRACHE.md).** Die Axiomschicht war ein System mit Beispielen; hier wird
sie **ausgezählt** — nicht aus Vorstellung, sondern **gemessen am Zweig `arch/x86_64` von
Caprock** (`kernel/src/arch/x86_64/`, `crates/caprock-hal/src/x86_64/`). Und der unsichere
Bootcode, bisher ein Satz in drei Schichten über einer Prosastrecke, wird zur Sprache: das echte
Trampolin (`mod.rs`, `_start` bis `x86_rust_entry`) ist die Vorlage, Zeile für Zeile.

> **EINGETRAGEN 2026-08-14, mit vier nachgeprueften Zahlen und einer Namensberichtigung.**
> Grammatik: **119 Regeln, 0 offen, 189 Terminale gegen 189 Wortschatzwoerter**, beide Waechter
> gruen. Der Waechter zaehlt **zwei** neue Woerter — die Kopfzeile stimmt diesmal.
>
> **Nachgeprueft am Zweig, alle vier:**
> `int 0x80` steht woertlich in `crates/caprock-hal/src/x86_64/syscall.rs:23`, und der Kommentar
> bei `:4` stellt es ausdruecklich dem `syscall`/`sysret`-Weg gegenueber — **die Berichtigung an
> ERGAENZUNG §2 ist richtig.** `ABI_TO_GPR` ist `[usize; 7]` ab `RAX, RDI, RSI`
> (`exception.rs:73`). **Kein einziges `xsave`/`xrstor` im Baum** (7 `fxsave`, 6 `fxrstor`) — die
> `FpArea`-Praezisierung stimmt. Und der Port-Posten, den A12 aus der Axiomschicht holt, ist mit
> **70 Fundstellen** (52 `outb`/`outl`, 18 `inb`) **groesser** als die Zaehlung angibt.
>
> **Eine Namensberichtigung beim Eintragen:** `via int 0x80` ist nicht schreibbar, weil `int` in
> der Lexik die **Zahlenklasse** ist (`int = dec | hex | bin`). Der Mechanismus ist ein Bezeichner
> aus geschlossener Menge, der Vektor kommt aus dem vorhandenen `vector`:
> `entry syscall vector 0x80 via softint arch x86_64 { … }`. **Kein zusaetzliches Wort.**

Stand 2026-08-14. **Neue Wörter (geschlossen, zwei):** `port step`
(`via`, `boot`, `requires`, `ensures` werden wiederverwendet — eine Grammatikerweiterung ist
keine Wortschatzerweiterung.)

---

### 0. Die Zählung — was der Zweig wirklich anfasst

Privilegierte und geordnete Befehle im x86_64-Teil, dedupliziert (Fundstellen, nicht Aufrufe):

| Befehl | # | | Befehl | # | | Befehl | # |
|---|---|---|---|---|---|---|---|
| `outb`/`out` | 46+ | | `mov cr0` | 7 | | `sfence` | 2 |
| `hlt` | 35 | | `iretq` | 7 | | `rdtsc` | 2 |
| `cpuid` | 26 | | `lfence` | 7 | | `invlpg` | 2 |
| `inb` | 17 | | `mov cr3` | 6 | | `sysret` | 1 |
| `wrmsr` | 12 | | `lgdt` | 4 | | `swapgs` | 1 |
| `cli` | 12 | | `fxsave` | 4 | | `sti` | 1 |
| `rdmsr` | 11 | | `mov cr4` | 3 | | `pause`/`mfence`/`lidt`/`fxrstor` | je 1 |
| `ltr` | 10 | | `rdtscp` | 3 | | | |

MSRs: `EFER (0xC000_0080)`, `IA32_APIC_BASE`, `IA32_ARCH_CAPABILITIES`. CPUID-Blätter: 0, 1, 7.
Noch nicht auf x86 (laut `bringup.rs`): SMP (INIT-SIPI-SIPI), PCID/per-VSpace, Ring-3-PDs im
Kern, Loader, IOMMU-Aktivierung — deren Axiome stehen unten als **vorgemerkt**, nicht als gezählt.

**Zwei Berichtigungen an den eigenen Ergänzungen, aus dem echten Code:**

1. **Der Syscall-Mechanismus ist `int 0x80`, nicht `syscall`/`sysret`.** Kernel-Threads lösen
   `int 0x80` aus (IDT-Gate, DPL 3), weil es denselben Trap-Frame legt wie jeder Interrupt — der
   Dispatch bleibt einheitlich, und `rcx`/`r11` überleben. ERGAENZUNG §2 nahm die
   `syscall`-Konvention als gegeben. Das `entry`-Konstrukt bekommt deshalb die
   Mechanismenwahl: `entry syscall via int 0x80 …` | `via syscall` | `via svc` (aarch64) —
   **die `clobbers`-Menge folgt aus dem Mechanismus** und wird geprüft statt abgeschrieben
   (int: keine; syscall: `rcx, r11`). Die echte ABI aus `syscall.rs`/`exception::ABI_TO_GPR`:
   `nr: rax, ep: rdi, m0: rsi, m1: rdx, m2: r10, m3: r8, tag: r9`, Rückgabe in denselben sechs.
2. **FP ist `fxsave`/`fxrstor` (512-Byte-Bereich), nicht `xsave`.** ERGAENZUNG-2 §3.4 wird
   präzisiert: `FpArea` ist auf diesem Zweig der FXSAVE-Bereich; `xsave` ist die Erweiterung
   **hinter einem Feature-Zeugen** (§2).

---

### 1. Der sechste Adressraum: `port`

Die Zählung zeigt, was das MMIO-Modell übersah: **Port-IO ist auf x86 ein eigener Adressraum**
(Konsole `0x3F8`, PCI-Konfiguration `0xCF8`/`0xCFC`, PIC, PIT) — mit eigener Befehlsform
(`in`/`out`), eigener Breitenregel und ohne Abbildung im Seitenwerk.

```gabbro
device SerialCom1 at port {
    reg DATA : u8 @0x3F8 class rw
    reg LSR  : u8 @0x3FD class r fields { THRE @5, DR @0 }
}
device PciConfig at port {
    reg ADDR : u32 @0xCF8 class w
    reg DATA : u32 @0xCFC class rw
}
```

`at port` senkt Zugriffe auf `in`/`out` ab statt auf volatile Loads/Stores; `class`, `fields`,
`transition`, `keeping` gelten unverändert. Auf Architekturen ohne Port-Raum ist ein
`port`-Gerät nur unter `arch x86_64` deklarierbar (D2: kein stiller Auffang). Damit sind die
größten Fundstellenposten der Zählung (`outb`/`inb`) **Gerätesprache statt Axiome** — die
Axiomschicht schrumpft, wo ein Konstrukt trägt, und genau so herum soll die Ratsche laufen.

---

### 2. Feature-Zeugen: `Has(F)` — CPUID als Erzeuger

Laufzeit-Features (CPUID 0/1/7, `IA32_ARCH_CAPABILITIES`) sind keine `when`-Konstanten. Sie
werden **Zeugen**: die CPUID-Sonde ist der einzige Erzeuger von `ghost Has(Feature)` (affin, wie
`Vis` — Fähigkeit erlischt nicht), und jedes Axiom, dessen Befehl ein Feature voraussetzt,
verlangt den Zeugen geliehen:

```gabbro
axiom rdtscp() -> u64 requires Has(RDTSCP) effects { pure }  falsifier probe_tsc;
axiom xsave(a: ptr<normal, w> XsaveArea) requires Has(XSAVE), MayUseFp(tid)
      effects { writes a }                                    falsifier probe_fp_roundtrip;
```

Ein `rdtscp` ohne vorherige Erkennung ist damit **nicht schreibbar** — die #UD-Klasse
(Befehl auf alter CPU) wird Übersetzungsfehler. Die Erzeugerliste (Festlegung §4) wird um
`Has` ergänzt: nur die generierte CPUID-Sonde erzeugt es.

---

### 3. Der Annahmenkatalog x86_64 — vollständig gegen die Zählung

Jede Zeile: Effekt aufs Maschinenmodell, Zeugenfluss (M2-Token), Falsifikatorstatus.
**F** = Sonde fahrbar (QEMU/KVM, im Prüfgerüst), **U** = unfalsifizierbar mit Grund,
**V** = vorgemerkt (Code existiert noch nicht).

| # | Axiom | Effekt / Token | Status |
|---|---|---|---|
| A1 | `write_cr3(p)` | wechselt Wurzel, invalidiert Nicht-Global-TLB; `consumes/mints ActiveTable(p)` | F: Sonde mappt um, liest |
| A2 | `write_cr0(v)` | `PG`-Bit: `requires PaeSet, LmeSet, Cr3Set` → `mints Paging`; `WP`-Bit → `mints WriteProtect` | F: Ro-Schreibsonde muss faulten |
| A3 | `write_cr4(v)` | `PAE` → `mints PaeSet`; verbotene Übergänge als fehlende Token unformulierbar | F |
| A4 | `wrmsr_efer(v)` | `LME` → `mints LmeSet`; **`LME`-Setzen bei `PG=1` ist tokenlos unschreibbar** | F |
| A5 | `lgdt(d)` / `lidt(d)` / `ltr(s)` | lädt Deskriptortabellen; **Hardware schreibt Accessed-Bits IN die GDT** (s. §5.3) | F: Byte-Vergleich vor/nach |
| A6 | `invlpg(va)` | invalidiert einen TLB-Eintrag; Teil der Unmap-Quiesce-Folge | F: Stale-TLB-Sonde |
| A7 | `iretq(frame)` / `sysret` | typisierter Übergang (Bestand `resume`); `sysret` nur `via syscall` | F: `entry`-Sonden (E2 §5.2) |
| A8 | `int 0x80` | Gate DPL 3 legt vollständigen Trap-Frame; **keine** Clobber | F: Registerbild-Sonde |
| A9 | `cli`/`sti` | maskiert/demaskiert; `mints/consumes IrqsOff` — `sti` ohne Token unschreibbar | F |
| A10 | `hlt` | wartet auf Interrupt; nur mit `progress`-Annahme in `forever` | F: Watchdog |
| A11 | `pause` | Spin-Hinweis, semantikfrei | U: „kein beobachtbarer Effekt" |
| A12 | `in`/`out` (Raum `port`) | Geräteeffekt laut `device`-Deklaration; seriell abgesetzt | F je Gerät |
| A13 | `rdmsr`/`wrmsr` (APIC_BASE, ARCH_CAP) | je MSR ein deklarierter Effekt; unbekannte MSR-Nummer unschreibbar (D2) | F |
| A14 | `cpuid(leaf)` | rein; **einziger Erzeuger von `Has(F)`** | F: Kreuzvergleich Blatt 0/1/7 |
| A15 | `rdtsc`/`rdtscp` | monoton je Kern **nicht** garantiert — nur Messwert, nie Ordnung | U: „Invarianz ist Plattformlos" — Nutzung als Ordnung ist Übersetzungsfehler |
| A16 | `fxsave`/`fxrstor` | 512-B-Bereich, `requires MayUseFp` | F: Roundtrip-Sonde |
| A17 | `clflush` + `sfence` | Zeile ausgeschrieben; Teil der DMA-Publikationsfolge im `dma`-Raum | F: Geräte-Echo |
| A18 | `lfence`/`mfence` | Ordnungspunkte über TSO hinaus (rdtsc-Serialisierung, MMIO) | mit A19 |
| A19 | TSO / C11-Abbildung | `c11_release_acquire_x86` (Bestand E2 §4) | F: Litmus MP/SB/LB |
| A20 | `swapgs` | Kernel-GS-Basis; nur in `entry`-Emission, `requires` Eintrittskontext | F: GS-Sonde |
| A21 | Multiboot1-Vertrag | Protected Mode, `ebx` = Info-Zeiger, Header in ersten 8 KiB | F: der Boot **ist** die Sonde |
| A22 | Linker-Disjunktion | `.boot*` ⟂ `.text/.rodata`; `[__text_start,__rodata_end)` unveränderlich nach Boot | F: Linker-Map-Sonde (E2 §3.5) |
| A23 | INIT-SIPI-SIPI, ICR | SMP-Start | **V** (Zweig hat kein SMP) |
| A24 | PCID/`invpcid` | per-VSpace-TLB | **V** |
| A25 | VT-d-Aktivierung | `vtd.rs`/`dmar.rs` liegen im HAL; Übergänge sind `device`-Sprache, die Wirksamkeit (`vtd_te_effective`) bleibt Axiom | F, sobald aktiviert |

**Die Ratsche über diesem Katalog:** 22 gezählte + 3 vorgemerkte Einträge. Jeder neue Eintrag
braucht Fundstelle und Status; wächst der Katalog ohne neue Hardware-Fläche, greift
Abbruchbedingung 5. Und die Gegenrichtung ist der Erfolgsfall: A12 hat gerade die zwei größten
Befehlsposten aus der Axiomschicht in die Gerätesprache verschoben.

---

### 4. Die Mode-Leiter: verbotene Übergänge sind fehlende Token

Der Kern von §3, herausgehoben, weil er die x2APIC-Lektion verallgemeinert: **Die
Boot-Reihenfolge PAE → LME → CR3 → PG ist keine Prosa-Vorschrift, sondern ein
Token-Fluss** (M2). `write_cr0` mit PG-Bit *verlangt* `PaeSet`, `LmeSet`, `Cr3Set`; wer die
Reihenfolge bricht, hat den Token nicht und **übersetzt nicht**. Der 32-Bit-Teil des Trampolins
wird damit prüfbar, obwohl er vor der ersten „richtigen" Gabbro-Zeile liegt — weil er aus einer
Deklaration **erzeugt** wird:

---

### 5. Der Bootpfad als Sprache — gegen das echte Trampolin

Vorlage: `kernel/src/arch/x86_64/mod.rs` (`.multiboot`-Header, `_start` in `.code32`,
Seitentabellenbau, CR-Leiter, `retf` → `long_mode`, `.bss`-Nullung, `call x86_rust_entry`).

#### 5.1 Das `boot`-Konstrukt

```ebnf
bootdecl = "boot" ident "arch" ident "{"
             { "step" ( axiomcall | ident "=" constexpr ) ";" }
             "dispatch" path ";"
           "}" ;
```

```gabbro
boot multiboot1 arch x86_64 {
    step stack   = boot_stack_top;            -- esp laden
    step save_bootinfo(ebx);                   -- Multiboot-Zeiger retten
    step load_tables(BOOT_IDENTITY);           -- §5.2: VORBERECHNET, kein rep stosd
    step write_cr3(BOOT_IDENTITY.root);        -- mints Cr3Set
    step write_cr4(PAE);                       -- mints PaeSet
    step wrmsr_efer(LME);                      -- mints LmeSet
    step write_cr0(PG);                        -- requires alle drei -> mints Paging
    step load_gdt(GDT64); step far_return(CODE64);
    step zero_bss(__bss_start, __bss_end);     -- erzeugt, aus Linker-Symbolen
    dispatch caprock::x86_rust_entry;          -- erste Gabbro-Funktion; mints BootPhase
}
```

**Der Emittent ist dieselbe eine `iasm`-Stelle** wie bei `entry`; der Prüfer prüft den
Token-Fluss der Leiter (§4) **vor** der Emission. Nach `dispatch` gilt: `BootPhase` existiert,
jede `raw fn` ist erreichbar, und der Drei-Schichten-Satz (E1 §3) übernimmt. Der `hlt`-Fänger
nach der Rückkehr ist `divergent` und wird miterzeugt.

#### 5.2 Die Boot-Seitentabellen sind Daten, kein Code

Das echte Trampolin **baut** die Identitätsabbildung zur Laufzeit (`rep stosd`, Schleife über
512 PD-Einträge). Die Abbildung ist aber **konstant**: 1 GiB identisch, 2-MiB-Seiten,
`present|writable|PS`. In Gabbro ist sie ein `const` vom `walk`-Typ, **zur Übersetzungszeit
ausgerechnet** und nach `.boot.data` gelegt — `step load_tables` lädt nur noch. Weniger
Zone-0-Befehle, und die Abbildung selbst ist M1/`walk`-geprüft statt handgeschriebene
Bitarithmetik in 32-Bit-Assembler. (Die Verschiebung der physischen Basis ist Link-Zeit-Arbeit:
Linker-Symbole sind `extern`-Konstanten, A22.)

#### 5.3 Die GDT-Lektion aus dem echten Code — als Platzierungsregel

Der Zweig dokumentiert einen bezahlten Fund: **die CPU schreibt beim Laden eines
Segmentregisters das Accessed-Bit in den Deskriptor** — die GDT muss beschreibbar liegen, sonst
#PF unter `WP=1`, und ein Accessed-Bit in `.rodata` hätte den Code-Hash (A-1.3) lauffremd
gemacht. Das ist jetzt Axiom **A5** plus eine **Platzierungsregel**: die GDT/IDT/TSS-Deklaration
ist ein `format` im `normal`-Raum mit Pflichtrecht `w`; eine Platzierung in einem `r`-Abschnitt
ist ein **Übersetzungsfehler**. Die Falle ist damit unschreibbar statt gut kommentiert.

#### 5.4 Multiboot-Info ist ein `format`

Der gerettete `ebx`-Zeiger ist klassische **unvertraute Eingabe**: `format Multiboot1Info` mit
Flags-Feld, bedingtem Speicherplan (`mmap_length`/`mmap_addr` mit `offset_into`-Bindung) und
benannten Absagen (`reason MbAbsage { keine_mmap = 1 "…", … }`). Der Rückfall
`RAM_END_FALLBACK` aus `bringup.rs` wird ein benannter Absage-Zweig statt einer stillen
Konstante.

#### 5.5 Der vollständige Boot-Satz, erweitert

Zu den drei Schichten (S1 Typen, S2 Verweise, S3 Abbildung+Sonde) kommt die vierte Zeile, die
der echte Zweig verlangt: **S0 — die Zone vor der ersten Gabbro-Funktion ist erzeugt, nicht
geschrieben.** Ihr Inhalt ist die `boot`-Deklaration; ihr Vertrauen ist die eine Emissionsstelle
plus die Token-Leiter im Prüfer; ihr Falsifikator ist der Boot selbst (A21) plus die
Abschnittssonde (S3). **Und S3 wird um den Identitätsabbau ergänzt:** nach `mmu::init_primary`
muss auch die 1-GiB-Identitätsabbildung fallen, nicht nur `.boot` — die Nachbedingung heißt
vollständig: `!exists m in mappings of kernel_root: m.section == boot || m.identity`.

---

### 6. Abnahme dieser dritten Ergänzung

1. **Katalog gegen Zählung:** jedes Axiom A1–A22 hat eine Fundstelle im Zweig; jeder gezählte
   Befehl hat ein Axiom oder ein Konstrukt (A12!). Ein Befehl ohne Zeile oder eine Zeile ohne
   Befehl ist ein Fehler dieser Ergänzung.
2. **Die Mode-Leiter als Sprechprobe:** ein `boot`-Block mit vertauschtem `write_cr0(PG)` vor
   `wrmsr_efer(LME)` muss die Übersetzung brechen (fehlender Token), der echte muss durchgehen.
3. **`entry via int 0x80`** gegen `exception::ABI_TO_GPR` gehalten — Registerliste identisch,
   sonst ist §0.1 falsch abgeschrieben.
4. **Die vorberechneten Boot-Tabellen** byteidentisch gegen das, was das heutige Trampolin zur
   Laufzeit baut (einmalige Dump-Sonde in QEMU).
5. Aufnahme in die Wiederholungsmessung P0: die Bootstrecke und die Port-IO-Fundstellen zählen
   mit — die Klassen „Eintritt" und „Boot" dürfen danach keine hängende Klempnerei mehr führen.


---

# Teil V — Induktion

## Induktion — was sie braucht, und was sie am Nutzen kostet

**2026-08-14.** Anschluss an die Berichtigung in [`BEWEIS.md`](BEWEIS.md): Induktion ist nicht
unmoeglich, sondern durch drei Entwurfsregeln verboten. **Was braeuchte man, und was kostet es?**

---

### Drei Stufen, und nur die erste behaelt die Sprache

| | Stufe | der Anwender schreibt | die Linie |
|---|---|---|---|
| **A** | **Erzeugte Schemata** — das Induktionsprinzip folgt aus der `table`-Deklaration | **nichts Neues** (oder eine Zeile, s. u.) | **haelt** |
| **B** | **Rekursive `spec fn` mit `decreases`** | je rekursive Spezifikation ein Abstiegsmass | **wandert** — die Spezifikationssprache bekommt eigene Terminierungspflichten |
| **C** | **Handgeschriebene Lemmata** mit Beweisschritten | Beweise | **weg** — das ist Verus/Dafny, und dann waere die ehrliche Frage: warum nicht Verus |

---

### Was Stufe A technisch braucht — drei Dinge, zwei davon mechanisch

**1. Eine wohlfundierte Relation aus der Deklaration.** Eine `table` mit
`parent`/`first_child`/`next_sibling` legt „ist Abkoemmling von" nahe. **Aber sie ist nur
wohlfundiert, wenn die Struktur azyklisch ist — und das ist die Invariante, die man beweisen will.**

Aufloesung (Standard, nicht neu): die Induktion laeuft ueber ein **Mass** (Zahl der Abkoemmlinge),
und die Invariante ist **Voraussetzung**, nicht Ergebnis. Die Deklaration muss also **nennen**,
welche Invariante die Wohlfundiertheit traegt:

```gabbro
invariant acyclic cost O(n) runs offline: … ;
```

**2. Das Schema erzeugen.** Mechanisch, aus der Deklaration — **wie Isabelle und Coq es aus einer
Datentypdeklaration ableiten.** Es ist eine **Schablone** im Sinne von L3, geht also **einmal nach
Isabelle** und **verkleinert die Vertrauensbasis**, statt sie zu vergroessern. *(Das ist der Grund,
warum Stufe A in den vorhandenen Entwurf passt statt ihn zu sprengen.)*

**3. Das Schema ANWENDEN — und hier sitzt die ganze Schwierigkeit.** Welches Schema, an welcher
Variable, mit welcher Verallgemeinerung? **Das ist eine Heuristik**, und Heuristiken sind die
Stelle, an der Automatisierung ausfaellt.

---

### Der Preis ist nicht die Zeilenzahl, sondern die VORHERSAGBARKEIT

**Das ist die eigentliche Antwort auf „wieviel schwerer im Nutzen".**

Wenn der Uebersetzer das Schema **raet**, haengt „uebersetzt es" an Loeserglueck: **dasselbe
Programm geht heute durch und morgen nicht**, weil eine Zeitschranke anders faellt. Gabbros ganzer
Zuschnitt war das Gegenteil — **M1 bis M4 sind Typen, keine Loeser.**

> **Und der Riss ist schon da:** [`MESSUNGEN.md`](MESSUNGEN.md) hat gemessen, dass
> **M1 an vier Stellen ein Loeser ist**, und [`MESSUNGEN.md`](MESSUNGEN.md), dass
> **54 relationale Faelle** dazukommen. Induktion mit geratener Anwendung **verbreitert** ihn.

#### Die Aufloesung: das Schema wird GENANNT, nicht geraten

```gabbro
ensures  descendants(s) is empty
    by   induction on descendants(s)
```

| | |
|---|---|
| **kein Lemma** | keine Beweisschritte, kein Beweiskoerper |
| **keine rekursive `spec fn`** | die Linie bleibt, wo sie ist |
| **kein Raten** | der Uebersetzer waehlt nichts; er wendet an, was dasteht |
| **faellt vorhersagbar** | entlaedt das genannte Schema die Pflicht nicht, sagt der Fehler **welches** und **wo** — nicht „unklar" |

**Ein neues Wort** (`induction`), **eine Produktion**, **eine Zeile beim Anwender — und nur dort, wo
Induktion noetig ist.**

---

### Was es am Nutzen kostet, ehrlich beziffert

| | Stufe A mit `by induction on` |
|---|---|
| **Zeilen** | **1 je Beweispflicht, die Induktion braucht.** Wieviele das sind, ist **ungemessen** — die Zahl liefert dieselbe Messung, die als Falsifikator der L3-Entscheidung ohnehin ansteht (17 Logik-Pflichten einordnen) |
| **Begriffe, die ein Anwender lernen muss** | **einer**: ueber welche Struktur die Induktion laeuft. Er muss **nicht** wissen, was ein Induktionsprinzip ist — er nennt eine Domaene, die er ohnehin deklariert hat |
| **Vorhersagbarkeit** | **erhalten**, weil genannt statt geraten |
| **Vertrauensbasis** | **schrumpft** — das Schema ist eine Schablone, geht einmal nach Isabelle |
| **Was es NICHT gibt** | Induktion ueber irgendetwas, das nicht als Struktur deklariert ist; ueber benutzerdefinierte rekursive Funktionen; ueber Programmablaeufe |

**Stufe B kostet mehr als eine Zeile:** wer rekursive `spec fn` schreibt, schreibt Spezifikationen
**mit eigener Terminierungspflicht** — eine andere Faehigkeit, und die Fehlerbilder werden
haeufiger. **Stufe C kostet die Identitaet der Sprache.**

---

### Die Decke verschiebt sich damit — aber nicht bis Gold

Mit Stufe A ist erreichbar: **Sicherheitshuelle + deklarierte Invarianten + induktive Eigenschaften
ueber deklarierten Strukturen.** Das deckt den gemessenen Fall (`revoke`s Nachordnungslemma) und
vermutlich `cdt_wellformed`.

**Es deckt nicht** — und das ist die verbleibende Decke:

* Eigenschaften ueber Strukturen, die **nicht** deklariert sind (der Maschinenzustand, ein
  Zeiger-Bitfeld-PTE),
* alles, was **Ablaeufe** quantifiziert (Lebendigkeit),
* funktionale Korrektheit, deren Argument **nicht** die Form einer Induktion ueber eine deklarierte
  Struktur hat.

- [ ] **Die Zahl fehlt, und sie entscheidet alles:** wieviele der 17 gemessenen Logik-Pflichten
      braeuchten `by induction on`, wieviele kaemen ohne aus, wieviele braeuchten Stufe B oder C?
      **Ein einziger Fall in der letzten Spalte setzt die Decke wieder tiefer.**


---

# Teil VI — Harte Schrittzusagen

## Harte Zusagen im Code — und die eine Bedingung, an der alles haengt

**2026-08-14.** Die Frage: kann die Sprache dem Programmierer **Zusagen abverlangen**, so dass
Induktion nicht mehr geraten, sondern **zusammengesetzt** wird?

**Antwort: ja — aber nur, wenn die erzwungene Zusage eine Aussage ueber EINEN SCHRITT ist.**

---

### Warum Induktion heute Heuristik ist

Ein Loeser muss drei Dinge raten: **welches** Schema, an **welcher** Variablen, mit **welcher**
Verallgemeinerung. `by induction over <domain>` nimmt ihm das erste ab. Die anderen zwei bleiben —
und damit bleibt „uebersetzt es" teilweise Loeserglueck, was gegen den ganzen Zuschnitt steht
(M1–M4 sind Typen, keine Loeser).

---

### Die Zerlegung, die es aufloest

| | Aussage | braucht Induktion? | pruefbar? |
|---|---|---|---|
| **Schrittzusage** | *„`delete_leaf` entfernt genau einen Knoten und erhaelt die Verkettung der uebrigen"* | **nein** — eine Aussage ueber **eine** Operation | **ja**, gegen die **erzeugte** Mutation |
| **Gesamtaussage** | *„nach `revoke` gibt es keine Abkoemmlinge"* | **ja** | durch **Zusammensetzung** der Schrittzusagen |

> **Wenn der Code die Schrittzusage machen MUSS, setzt das Schema die Gesamtaussage zusammen,
> statt sie zu raten.** Die Verallgemeinerung ist dann die Invariante (schon da), die Variable ist
> das Mass (deklariert), das Schema kommt aus der Struktur. **Nichts bleibt zu erraten.**

---

### Die Form: eine Zeile je ERZEUGTER Operation, nicht je Aufrufstelle

```gabbro
table CapSpace {
    slot { … }
    invariant cdt_wellformed  cost O(n) runs online : … ;

    ops insert, remove, relabel, delete_leaf;

    op delete_leaf shrinks descendants by 1 maintains cdt_wellformed;
    op insert      grows   descendants by 1 maintains cdt_wellformed;
    op relabel     keeps   descendants      maintains cdt_wellformed;
}
```

**Vier Operationen, vier Zeilen.** Nicht vier je Beweispflicht, nicht vier je Aufrufstelle.

---

### Die Bedingung, an der alles haengt — und sie ist scharf

**Eine erzwungene Zusage ist entweder geprueft oder ein Axiom. Ein drittes gibt es nicht.**

| Fall | Folge |
|---|---|
| **geprueft** | dann ist sie eine **Pflicht**. Braeuchte ihre Pruefung selbst Induktion, waere die Sache **zirkulaer** |
| **ungeprueft** | dann ist sie ein **Axiom je Operation** — und die Axiomschicht waechst von ~130 auf eins-je-Operation. Das ist Abbruchbedingung 5 |

**Der Ausweg ist genau die Lokalitaet:** eine Schrittzusage ist ueber **einer** Operation
formuliert, und die Operation ist **erzeugt** (Zuschnitt (c)). **Der Erzeuger weiss, was er
emittiert hat** — er prueft die Zusage gegen seine eigene Emission, ohne Induktion. Weder
zirkulaer noch Axiom.

> **Damit steht die Entwurfsregel, und sie ist neu:**
> **Eine Zusage, die der Code machen MUSS, darf nur eine Aussage ueber EINEN Schritt sein.
> Alles Globale ist Beweis oder Axiom — niemals Zusage.**

---

### Was es kostet

| | |
|---|---|
| **Zeilen** | **eine je erzeugter Operation.** Bei `CapSpace` vier. Sie zaehlen als Spezifikation (Quelle, vor der Codeerzeugung geloescht) |
| **Neue Woerter** | drei: `op`, `shrinks`/`grows`/`keeps`, `by` (vorhanden) |
| **Vorhersagbarkeit** | **wiederhergestellt** — nichts wird geraten, also haengt „uebersetzt es" nicht mehr am Loeser |
| **Vertrauensbasis** | **unveraendert** — die Zusage ist geprueft, nicht geglaubt |

---

### Was es NICHT tut — sonst waere es Ueberschreibung Nummer achtzehn

**Es hebt die Decke nicht.** Erreichbar bleibt: *Eigenschaften, die sich durch wohlfundierten
Abstieg ueber eine **deklarierte** Struktur beweisen lassen.* Was die Form nicht hat, hat sie auch
mit Zusagen nicht:

* Eigenschaften ueber **nicht deklarierten** Strukturen (Maschinenzustand),
* alles, was **Ablaeufe** quantifiziert (Lebendigkeit, D8),
* funktionale Korrektheit, deren Argument **kein Abstieg** ist (der IPC-Fastpath: eine Aussage
  ueber **Werte**, nicht ueber eine schrumpfende Menge).

> **Der Gewinn ist nicht Hoehe, sondern Sicherheit des Erreichens:** die Decke wird
> **automatisch** statt heuristisch erreicht. Das ist weniger, als die Frage hofft — und mehr,
> als der heutige Stand hat.

- [ ] **Die Zahl fehlt weiterhin, und sie ist dieselbe:** wieviele der 17 gemessenen
      Logik-Pflichten sind **Abstiegsaussagen** (dann greift das hier), wieviele sind
      **Wertaussagen** (dann nicht)? **Ohne diese Aufteilung ist auch dieser Entwurf eine
      Behauptung.**


---

# Teil VII — Die Umkehrung der Frage

## Die Umkehrung der Frage — jedes „geht nicht" wird zu „was muss minimal dastehen"

**2026-08-13.** Beide Papiertests fragten *„geht das?"* und meldeten Loecher. **Die Frage war
falsch.** Gabbro ist eine sehr enge Sprache, die schwer sein darf; die richtige Frage lautet:

> **Was muss der Code MINIMAL spezifizieren, damit es geht — und laesst sich das nach C absenken?**

Beides ist Bedingung. Eine Angabe, die sich nicht absenken laesst, ist keine Antwort.

**Das gilt fuer ganz Gabbro, nicht nur fuer Schleifen.** Unten steht die vollstaendige Umwandlung
aller achtzehn „geht nicht"-Befunde aus beiden Berichten.

---

### Der Fall, an dem die Umkehrung am deutlichsten wird: Schleifen

**Gemeldet war:** *„CAS-/Warteschleifen: keine Loesung. Kein Abstiegsmass, `divergent` ist falsch."*

**Das stimmt fuer `variant` und ist die falsche Frage.** Eine Warteschleife ist nicht masslos —
sie ist durch **Bedingungen an ihre Umgebung** begrenzt, und die lassen sich hinschreiben:

```gabbro
retry until slot_free(q)
    bounded    4096 attempts        -- oder: 2 ticks
    progress   assume holder_releases
    on_exceeded EP_FULL             -- benannte Absage, kein stiller Abbruch
    effects    { reads q }
{ }
```

| Angabe | wozu | Absenkung nach C |
|---|---|---|
| `bounded` | Terminierung — **eine Zahl, kein Abstiegsmass** | Zaehlschleife `for(i=0;i<N;i++)` |
| `progress` | **wer** die Schleife beendet: eine Lebendigkeitsannahme mit Falsifikator | verschwindet (Geist) |
| `on_exceeded` | Regel 3: der Ueberlauf ist **benannt**, nicht gedeutet | `break` in den Fehlerzweig |

**Minimal: drei Zeilen.** Und Caprock schreibt sie heute **von Hand** an jeder begrenzten Schleife
(`cdt_step_limit`, `note_overrun`, `ERR_EP_FULL`) — die Sprache macht zur Pflicht, was das Projekt
ohnehin tut, und faengt die Stellen, an denen es vergessen wurde (`migration_candidate`).

**Der Ticket-Lock** ist derselbe Fall: er terminiert, weil der Halter freigibt. Das ist eine
Annahme ueber die Umgebung — also `assume` mit Falsifikator (der Watchdog **ist** der Falsifikator),
plus eine Schranke, deren Ueberschreitung ein Befund ist. **Nicht „unbeweisbar", sondern
„beweisbar unter einer benannten, falsifizierbaren Annahme".**

---

### Die vollstaendige Umwandlung

| # | gemeldet als „geht nicht" | **was minimal dastehen muss** | Absenkung |
|---|---|---|---|
| 1 | CAS-/Warteschleifen | `bounded` + `progress assume` + `on_exceeded` — **3 Zeilen** | Zaehlschleife + Fehlerzweig |
| 2 | **ELF ist kein `format`** (offsetbasiert) | `e_phoff : u64 offset_into Self where + e_phentsize*e_phnum <= Self.len` — **1 Attribut + 1 `where`** | Bereichspruefung |
| 3 | `caprock-fat` nur halb `format` | `traverse over chain(fat, cluster) by unvisited` + Absage `Zyklus` — **2 Zeilen** | Schleife + Generationsstempel |
| 4 | `move_cap` — Knotenumbenennung | erzeugte Mutation `relabel` mit **1 `maintains`** | Zeigerumhaengung |
| 5 | `install` — Zustand ohne Namen | `linear Uninstalled(Object)`, nur von `alloc_slot` verbraucht — **1 Typ** | **verschwindet** |
| 6 | `Finalized<'a>` — keine Lebenszeiten | Recht `own` + `Duty` — **1 Rechtsangabe** | verschwindet |
| 7 | **Fastpath-Autoritaet** („darf dieser Thread hierhin schreiben?") | `linear ghost MayWrite(t, f)`, erzeugt von der Cap-Aufloesung — **1 Zeuge + 1 `requires`** | **verschwindet** |
| 8 | Berichtsgeruest braucht Formatierung | **die `measures`-Liste IST die Berichtszeile** — 0 zusaetzliche Zeilen | erzeugtes `printf` |
| 9 | Beziehung zwischen zwei Layouts (das verlorene `US`) | `maintains` **ueber zwei Deklarationen**: Aufteilen erhaelt die Rechtebits — **1 Zeile** | keine |
| 10 | kein Summentyp (13 `ObjectKind`-Varianten) | `tagged` — Deklaration | C-Union mit Marke |
| 11 | **kein `old`** | `ensures old(x) + 1 == x` — **1 Schluesselwort** | verschwindet |
| 12 | `maintains` kennt kein Oeffnen/Schliessen | `breaking I { … }` — der Bereich, in dem die Invariante ruht, wird **benannt** | keine |
| 13 | `fields` nur Einzelbits, keine Laufzeitoffsets | Bitbereich `FRO @[12:8]`; Basis `@ base + CAP.FRO*16`, M1-beschraenkt | Adressrechnung |
| 14 | 2 231 Atomics, null Woerter | `atomic` + `publishes { … }` — **1 Klausel je Atomic** | `_Atomic` + Barriere |
| 15 | **`device` toetet Falle 4 nicht** | `transition` nennt **das ganze geschriebene Wort**, nicht ein Bit — RMW wird damit unformulierbar | ein `store` |
| 16 | `effects` ist fail-open | `effects` **verpflichtend**; leer heisst rein und wird **geprueft** — 0 Zeilen fuer richtigen Code | keine |
| 17 | Registerbank an laufzeitberechneter Basis | parametrisiertes `device Bank(base: Pa)` | Adressrechnung |
| 18 | bedingte Uebersetzung (335 `cfg`-Stellen) | `when <const>` an der Deklaration | `#if` |

---

### Der Befund, der beim Umwandeln entsteht

**Sechs der achtzehn faellen auf DENSELBEN Mechanismus: den linearen Geisterzeugen (M2).**
Nummern 5, 6, 7 — dazu die Bootphase, das virtio-`used`/`avail`-Eigentum und die `check`-Pflicht.

> **Sechs unabhaengige Fundstellen fuer einen Mechanismus sind kein Entwurfswunsch mehr, sondern ein
> Befund.** Und es ist genau der Mechanismus, den **kein vorhandenes Werkzeug liefert**: Verus'
> `tracked` ist affin, Rust ist affin, SPARKs Leckpruefung haengt an einer Allokation.

**Die zweite Zahl: der Median der Zusatzangabe liegt bei ein bis zwei Zeilen je Stelle.** Keine
davon ist ein Lemma, keine ein Schleifeninvariant — es sind **Deklarationen**. Das ist der
Unterschied, auf den es fuer die Kennzahl ankommt.

---

### Was das NICHT heisst — sonst ist es Ueberschreibung Nr. 14

* **Die 2 : 1-Messung wird dadurch nicht besser.** Die Zeilen, die hier „minimal" heissen, sind
  genau die, die der Zaehler zaehlt. Was sich aendert, ist ihr **Charakter**: Deklaration statt
  Beweis — und ob ein Loeser die daraus entstehenden Pflichten **ohne Hinweise** erledigt, ist
  **ungeprueft**.
* **Papier, nicht Uebersetzer.** Achtzehn Umwandlungen auf Papier sind achtzehn Behauptungen ueber
  Absenkbarkeit. Keine davon ist uebersetzt worden.
* **Zwei bleiben unbequem.** Nr. 12 (`breaking`) legalisiert eine Invariantenverletzung — der Preis
  ist, dass der Bereich, in dem nichts gilt, sichtbar wird statt versteckt. Und Nr. 14 verlangt eine
  Klausel an **2 231** Stellen; ob das traegt, entscheidet keine Papieruebung.

---

### Die Folge fuer die Methode

- [ ] **Kein Pruefauftrag fragt mehr „geht das?".** Er fragt: *„was muss minimal dastehen, und laesst
      es sich nach C absenken?"* Ein Bericht, der ein Loch meldet, ohne die minimale Angabe zu
      nennen, ist unvollstaendig — **er hat die Arbeit an der Stelle abgebrochen, an der sie
      anfaengt.**
