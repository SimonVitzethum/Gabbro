# Gabbro — die Sprache

**Vier Mechanismen, zwei Deklarationsregeln, eine Bibliotheksschicht darüber.**
Ausgabe: C + Inline-Assembler. Zweck und Kennzahl im [`README`](README.md), der Weg in
[`PLAN.md`](PLAN.md).

> **Gabbro = C ohne seine Löcher, plus zwei Dinge.** Die zwei sind **Bereichstypen** und **lineare
> Werte (auch geisterhafte)**. Alles andere ist eine **Einschränkung** von C, keine Erweiterung.

**Die Schreibweise jedes Konstrukts steht in [`SYNTAX.md`](SYNTAX.md)** — hier stehen die
Mechanismen und ihre Begründung.

Stand 2026-08-13. **Nichts davon ist übersetzt worden.**

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
