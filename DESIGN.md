# Gabbro — die Konstrukte

**Diese Datei ist die Quelle für die BIBLIOTHEKSSCHICHT.** Sie beschreibt `format`, `table` und
die übrigen Deklarationsformen — das, was ein Anwender schreibt.

> **Achtung, Rollenwechsel (2026-08-13).** Als diese Datei entstand, *war* sie der ganze
> Sprachentwurf: ein enger Formaterzeuger, ausdrücklich ohne Kernel. Seither ist der Kern eine
> **Systemsprache** mit vier Mechanismen ([`VOLLDECKUNG.md`](VOLLDECKUNG.md) §3), und die sieben
> Konstrukte hier sind **Bibliotheken darüber**, keine Sprache daneben. Wo unten „die Linie" steht,
> ist die Linie **dieser Schicht** gemeint — die Linie der Sprache ist gewandert, und das steht
> dort.

Stand 2026-08-13. **Nichts davon ist übersetzt worden.** Was gemessen ist, steht als gemessen da.

---

## Das Ziel, mit Geltungsbereich

> **Diese Schicht beweist nicht — sie erzeugt Programme, deren Beweis billig ist.**
> **Wie billig, hängt davon ab, WAS bewiesen werden soll — und das ist bei `format` etwas anderes
> als überall sonst.**

**Nicht zu verwechseln mit dem Kern:** der *Sprachkern* beweist sehr wohl — Speichersicherheit,
und später Rennfreiheit (`README`, Zusagen 1/1b/2). Diese Schicht erzeugt Deklarationen darüber und
führt keinen eigenen Beweis. Gabbros Beitrag hier ist, dass **jedes Konstrukt seinen Vertrag
mitbringt**.

### Was jedes Konstrukt einem nachgelagerten Beweiser tatsächlich einbringt

**Diese Tabelle ist der Geltungsbereich.** Fehlt sie, wandert der Anspruch von selbst nach oben —
das ist genau die Bewegung, die in `HISTORIE.md` neunmal steht.

| Konstrukt | was daraus beweisbar wird | was **nicht** |
|---|---|---|
| **`format`** | **die vollständige funktionale Spezifikation** des Lesers/Schreibers | dass der Beschreiber der Wirklichkeit entspricht |
| `traverse` | Bereichssicherheit (S1a unformulierbar), Terminierung, Zyklusfreiheit, Rahmen | **der Rumpf.** `{ if it == s { found } }` ist Code — dass er das Richtige *sucht*, steht in keinem Vertrag |
| `table`-Invarianten | die **deklarierten** Invarianten, an den deklarierten Stellen | alles, was niemand deklariert hat |
| `state` | die **deklarierten** Übergänge; nicht deklarierte sind nicht formulierbar | dass die Menge der Übergänge die richtige ist |
| Arithmetik-Vorbedingung | Abwesenheit von stillem Über-/Unterlauf (S1b) | dass der Zähler das Richtige zählt |
| Wirkungen | Rahmenbedingung: was **nicht** angefasst wird | was mit dem Angefassten geschieht |
| `assume`/`falsifier` | **nichts** — es benennt die **Reichweite** des Beweises | die Wahrheit der Annahme |

**Die Summe:** für `format` ist funktionale Korrektheit erreichbar, überall sonst eine
**Sicherheitshülle plus die deklarierten Invarianten**. Das ist deutlich mehr als heutiges Rust und
deutlich weniger als seL4 — und **beides gehört in denselben Satz**, sonst entsteht Überschreibung
Nummer drei.

### Die Kennzahl — und warum sie ohne Protokoll die Wunschzahl liefert

Die belastbare Grösse ist *Zeilen Spezifikation je Zeile Code*: **seL4 rund 20 : 1**, HACL\*
vergleichbar, **Ziel dieser Schicht ≤ 1 : 1** — für `format`, wo der Beschreiber die vollständige
Spezifikation *ist*. **Für Kernelcode liegt das Ziel bei etwa 5 : 1**, weil dort die abstrakte
Spezifikation als Boden bleibt; Herleitung in [`VOLLDECKUNG.md`](VOLLDECKUNG.md) §3c.

**Nur ist die 20 : 1 eine Zahl für volle funktionale Korrektheit** (in SPARKs Übernahmeleiter:
*Platinum*), während oben steht, dass Gabbro ausserhalb von `format` etwas Schwächeres liefert. Ein
Verhältnis ohne genannte Stufe vergleicht über die Kluft.

**Und die Zahl ist doppelt manipulierbar, in beide Richtungen:**

* **über die Modulwahl** — am Manifest-Leser glänzt sie, an einem (c)-Mutationsmodul nicht;
* **über den Nenner** — ein geschwätziger Erzeuger verbessert das Verhältnis, indem er **mehr Code**
  erzeugt. Der Nenner muss deshalb die **handgeschriebene Referenz** sein, nicht die Ausgabe.

Das Messprotokoll steht als Abbruchbedingung 0b in `ROADMAP.md` und gehört **vor** die Messung.

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

## 1. `format` — Drahtformate

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

## 2. `table` — Tabellen mit Invarianten

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

    invariant kind_zeigt_zurueck cost O(n * kette) laeuft offline:
        forall s where s.parent = Some(p) => s in chain(p.first_child, next_sibling)
}
```

**`cost` und `laeuft` sind Pflicht, nicht Schmuck.** Eine Invariante ohne Kostenangabe ist
unter dem Kern-Lock kein Audit, sondern ein Ausfall — `colors.rs` hält heute **42 Ticks** und gilt
deshalb als Schuldposten. Und **inkrementelle** Prüfung setzt voraus, dass der Prüfer das Delta
kennt, das **nur der Mutator** kennt: **wer Invarianten im heissen Pfad will, hat Zuschnitt (c)
bereits gewählt.**

---

## 3. `traverse` — Schleifen gibt es nicht

„Endlich" ist das **schwächste** Versprechen: eine Schleife mit Schrittgrenze terminiert und kann
trotzdem ausserhalb der Tabelle indizieren. Genau das ist **S1a**.

```gabbro
traverse geschwister of p
    over  chain(first_child, next_sibling) in slots
    by    unbesucht                  -- Kosten: s. u.
    touches read slots
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

## 4. `state` — erlaubte Übergänge

Nennt die **zulässigen** Übergänge; alles andere ist nicht formulierbar. Das I9-Fenster
(`used = false` bei `refcount = 1`) wäre damit kein Zufall der Reihenfolge mehr, sondern ein
nicht existierender Übergang.

**Und derselbe Mechanismus trägt eine Ebene tiefer:** `iretq`/`eret` ist ein **typisierter
Übergang in einen gespeicherten Maschinenzustand** — dasselbe Konstrukt, angewandt auf Register
statt auf Felder. Das ist der Grund, warum „Syscalls ohne Assembler" kein Fremdkörper wäre.

---

## 5. Arithmetik mit Vorbedingung

`refcount -= 1` gibt es nicht. Es gibt:

```gabbro
decrement refcount requires refcount > 0        -- oder: wrapping
```

Damit ist **S1b** unformulierbar statt hinterher auffindbar. **Ein Umlauf, den niemand
ausgesprochen hat, ist ein Fehler; einer, der ausgesprochen ist, ein Entwurf** — genau der
Unterschied zwischen S1b und den Generationen, auf deren absichtlichem Umlauf `resolve` ruht.

---

## 6. `assume` / `falsifier` — Hardware-Annahmen

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

### Die Annahmenmenge gehört INS ERZEUGNIS, nicht nur in die Quelle

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

## 7. Wirkungen (`Global`/`Depends`-Form)

Jede Operation nennt, was sie liest und schreibt. Dafür gibt es **eine Messung am Mechanismus**:
im Caprock-Scheduler wurden mit SPARKs `Depends` **63 von 63** Datenabhängigkeiten bewiesen, und
„der Rust-Code liest überall genau einmal in eine Kopie" ging von *gelesen* zu *bewiesen*.
**Die Übertragbarkeit auf Gabbro ist damit angenommen, nicht gemessen** — SPARK prüft vorhandenen
Code, Gabbro erzeugt ihn.

---

## Anhang: `reason` — Regel 3, syntaktisch

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

## Die Linie DIESER SCHICHT: sieben Konstrukte, mehr nicht

`format` · `table` · `traverse` · `state` · Arithmetik-Vorbedingung · `assume`/`falsifier` ·
Wirkungen.

**In der Bibliotheksschicht: keine allgemeinen Vor-/Nachbedingungen, keine Quantoren über
Rechenausdrücke.**

> **DIE LINIE DER SPRACHE IST GEWANDERT — und der Widerspruch gehört ausgesprochen, nicht
> weggeschrieben.** Der Kern hat seit dem 2026-08-13 **Verträge über deklarierte Prädikate** und
> `spec fn`/`impl fn` mit erzeugter Verfeinerungspflicht; ohne sie ist „Bedingung über
> Registergrenzen" (Falle 1/2) nicht formulierbar und ein Gold-Beweis nicht billig.
> **Damit ist eingetreten, was hier als der unbequeme Ausgang stand:** *dann ist Gabbro der
> Beweisassistent mit Syntax, dem es ausweichen wollte.* Es ist eine **Entscheidung**, keine
> Entdeckung — und der Preis dafür steht in `VOLLDECKUNG.md` §6. **Allgemeine Quantoren über
> Rechenausdrücke bleiben weiterhin draussen.**

### Und die Linie bricht voraussichtlich an `revoke`

`decrement requires` ist eine Vorbedingung **auf einem Feld**. Die Korrektheitsbedingung von
`revoke` ist **strukturell**: ein Teilbaum verschwindet, und dass danach `kind_zeigt_zurueck` und
die Kettenendlichkeit noch gelten, ist eine Aussage über **Baumform** — strukturelle Induktion,
also genau die ausgeschlossenen Quantoren.

- [ ] **`revoke` in diesen sieben Konstrukten auf Papier ausdrücken.** Der Test hat seinen
      *Ausgang* verloren — die Linie ist ohnehin gewandert — und behält seinen **Wert**: er sagt,
      ob die Bibliotheksschicht die gefährlichste Mutation trägt oder ob `revoke` in den Kern
      hinuntermuss. Das ist die Frage, die den Zuschnitt (c) entscheidet.
