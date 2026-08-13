# Gabbro für ganz Caprock — und für beliebige Programme

**Was hier geplant wird, und was es kostet, steht vor dem Plan.**

Dieses Dokument verlässt den Zuschnitt, den `README.md` verteidigt. Es plant eine
**Allzweck-Systemsprache**. Damit fällt die Rechnung, die Gabbro billig machte — die geschlossene
Domäne —, und die Spezifikationslast kehrt zurück. **Die Linie wandert**, und `README.md` hat genau
das als den unbequemen Ausgang vorhergesagt: *dann ist Gabbro der Beweisassistent mit Syntax, dem es
ausweichen wollte.*

Die Messung dazu steht und wird nicht schöngeredet: die sieben Konstrukte decken heute **≤ 9 %** von
Caprock, hart **4,6 %**. Dieses Dokument plant die übrigen **91 %**.

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

## 2. Der Kern (Stufe 0) — was „beliebige Programme" verlangt

`format`/`table` sind Bibliotheken **über** diesem Kern, keine zweite Sprache daneben.

| Element | Entscheidung |
|---|---|
| **Typen** | algebraische Datentypen, feste Breiten, kein Wirtslayout. Generizität monomorphisiert |
| **Linearität** | **linear** (muss verbraucht werden) und **affin** (darf weggeworfen werden) als getrennte Qualifizierer. Rust ist nur affin — genau daran hängt Falle 45 |
| **Regionen** | jeder Zeiger trägt seine Region; Regionen sind geschachtelt, kein Zeiger überlebt seine Region |
| **Wirkungen** | jede Funktion nennt ihre Wirkungen (lesen/schreiben, Sperren, IRQ-Zustand, Allokation, Ein-/Ausgabe). Voreinstellung: **keine** |
| **Terminierung** | `traverse` ist die Voreinstellung. Für den allgemeinen Fall `loop … variant e` mit **ausgesprochenem** Abstiegsmass — die Ausnahme ist benannt, nicht verboten |
| **Speicher** | Arenen mit Lebensdauer, kein freier `malloc`, keine Halde im Kern. Ein Programm ohne Arena ist allokationsfrei — beweisbar, nicht behauptet |
| **Fehler** | `reason` mit `exhaustive`, kein Auffangzweig, kein `panic` als Sprachmittel |
| **Übersetzer** | bleibt **sicheres Rust**, `forbid(unsafe_code)`. Kein Selbst-Hosting — ein Erzeuger, der sich selbst übersetzt, verliert seinen unabhängigen Prüfer |

**Was das nicht ist:** kein GC, keine Ausnahmen, keine Vererbung, keine Reflexion, kein dynamisches
Laden. „Beliebige Programme" heisst hier *beliebige Systemprogramme*.

---

## 3. Die Stufen — jede mit Fundstellen, Syntax und getöteten Fallen

Jede Stufe nennt: **wie viele Fundstellen** sie in Caprock adressiert, **welche bezahlten Fallen**
sie unformulierbar macht, und **was sie nicht kauft**. Eine Stufe ohne getötete Falle ist eine
Stufe ohne Evidenz und wird nicht gebaut.

### Stufe 1 — Nebenläufigkeit · **2 231 `Ordering::` + 406 Sperrnahmen**

Der grösste Einzelposten, und der einzige, bei dem Rust **und** SPARK **und** Verus gleichermassen
schwach sind.

```gabbro
lock CAPS schuetzt { slots, cdt, gen_counter }
    ordnung  2                       -- Sperrordnung: nur absteigend nehmen
    maskiert irqs                     -- die WIRKUNG des Haltens steht am Lock

fn delete_leaf(s: SlotIdx) -> Result
    requires held(CAPS)               -- ohne Guard-Weitergabe ausdrueckbar
    wirkung  { schreibt CAPS.slots }
    haelt_hoechstens 200 zyklen       -- Sperrhaltedauer ist eine Groesse, keine Gewohnheit

atomic COLOR_DONE : bool
    veroeffentlicht { color_report }   -- die NUTZLAST steht am Atomic, nicht im Kopf
    release/acquire
```

| Regel des Übersetzers | tötet |
|---|---|
| Sperren nur in absteigender `ordnung` — sonst Übersetzungsfehler | **41** (`match lock() { None => lock() }`, Selbst-Deadlock) |
| Ein Guard, dessen Lebensdauer einen Rumpf überspannt, ist ein Fehler; `haelt_hoechstens` ist Pflicht | **93** (`while let`-Guard, Krypto unter maskierten IRQs) |
| `veroeffentlicht` ist Pflicht an jedem Atomic; die Nutzlast ist Teil des Modells | **33** (Loom sah die Nutzlast nicht, weil sie im `UnsafeCell` lag) |
| `maskiert irqs` propagiert als Wirkung durch jeden Aufrufer | **37** (lokale IRQ-Sperre als Fenster über eine globale Grösse) |

**Was es nicht kauft:** Fortschritt (Freiheit von Aushungern) und Ablaufreihenfolge. Ein
deadlockfreies Programm kann trotzdem verhungern lassen — D8 wäre nicht getötet.

### Stufe 2 — Geräte und MMIO · **125 `volatile` + die halbe HAL (13 518 Zeilen)**

`format` für den Draht, `device` für das Register. Die Analogie trägt, weil beide dasselbe Problem
haben: fremdbestimmtes Layout mit Bedingungen.

```gabbro
device Vtd at mmio {
    reg GCMD : u32 @0x18
        klasse write_only          -- KEIN Read-Modify-Write moeglich
        felder { TE @31, SRTP @30, IRE @25 }
    reg GSTS : u32 @0x1c  klasse read_only
    reg CAP  : u64 @0x08  klasse read_only

    uebergang te_scharf { GCMD.TE: 0 -> 1 }
        requires GSTS.RTPS == 1
        wirkung { dsb sy }         -- Barrierendomaene am Geraet, nicht "arch-neutral"
}

device Smmu at mmio {
    reg STE.S1STALLD : bit
        requires IDR0.STALL_MODEL == 0b10     -- Bedingung UEBER Register hinweg
}
```

| Regel | tötet |
|---|---|
| `klasse write_only` — ein Lesen zum Zurückschreiben ist nicht formulierbar | **4** (x86 `GCMD` ist kein RMW) |
| `uebergang` nennt die erlaubten Bitwechsel; alles andere existiert nicht | **5** (x2APIC `EN`+`EXTD` in einem Schritt) |
| `requires` über Registergrenzen | **1** (`STE.S1STALLD` ohne `IDR0.STALL_MODEL`), **2** (CD ohne `R`) |
| Registerbreite im Typ, kein impliziter Abschnitt | **11** (`CR3` per 32-Bit-Schreibzugriff) |
| Eigentum je Feld: `used` gehört dem Gerät | **35** (nur den Treiberteil der Virtqueue genullt) |
| Barrieren tragen ihre Domäne | **8** (`fence(SeqCst)` ist auf aarch64 `dmb ish`) |

**Was es nicht kauft:** dass der Beschreiber stimmt. Ein falsches Registerhandbuch ergibt einen
makellosen falschen Treiber — Falle 7 und 3 bleiben `assume`-Sache.

### Stufe 3 — Eigentum und Adressachsen · **403 Rohzeiger + 482 `unsafe`**

```gabbro
linear type Parked           -- MUSS verbraucht werden; kein Wegwerfen, kein Kopieren
linear type Endowment
fn admit(p: Parked) -> Tid   -- der einzige Verbraucher

einheit Pa   basis u64       -- getrennte Achsen, Arithmetik nur innerhalb
einheit Iova basis u64
einheit Farben               -- MASK_BITS ist KEINE Farbanzahl
```

| Regel | tötet |
|---|---|
| `linear` ist echt: kein `forget`, kein `Copy`, kein stiller Verlust | **45** (rustc prüft Herstellbarkeit, nicht Nicht-Weitergabe), **50** |
| Jeder Abweispfad muss lineare Werte verbrauchen | **96** (neuer Abweispfad erbt die Aufräumpflicht nicht), **15** (Endowment-Liste beim Austausch) |
| Regionen: ein Puffer gehört genau einem Besitzer | **40** (Treiberpuffer gehört dem letzten Client), **12** (geteilte Seitenverzeichnisse) |
| `einheit` — Arithmetik über Achsen hinweg ist nicht typisierbar | **10** (`MASK_BITS`), **58** (ein Parameter, zwei Bedeutungen) |
| Ein Stapel ist kein Slot | **28** (`sc_donee`, geschachtelte Spenden) |

**Was es nicht kauft:** die Wahl der Achsen. Falle 59 (VA-Fenster in GiB 0) ist eine
Entwurfsentscheidung, kein Typfehler.

### Stufe 4 — Platzierung, Bau und Architektur · **W-Klasse, aber zwei Fallen**

```gabbro
fn ring3_sonde() platziert .user_text arch x86_64 { … }
image caprock { sektionen aus kernel.ld  genau_einmal }
```

Tötet **72** (Ring-3-Code in `.text`, faultet an der eigenen Einsprungadresse — zweimal passiert)
und macht **81** (doppeltes `-T` durch Cargo-Vererbung) strukturell unmöglich, weil der
Sektionsvertrag im Programm steht und nicht in der Umgebung. **Der Rest der W-Klasse (16 von 18)
bleibt.**

### Stufe 5 — Der Eintritt (TAL) · **161 `asm!`-Stellen, davon 20–30 im Betrieb aktiv**

Eintrittsfunktionen mit erklärtem Registerabdruck, registergebundene Werte, eigene
Aufrufkonvention, `transition` (`iretq`/`eret`) als typisierter Übergang in einen gespeicherten
Maschinenzustand — dasselbe Konstrukt wie `state`, eine Ebene tiefer.

> **Diese Stufe hat keinen nachgelagerten Beweiser, und das bleibt so.** Verus kann keine
> Inline-Assembler-Semantik, Frama-C/WP über erzeugtem C erst recht nicht, und ein TAL-Typsystem im
> Erzeuger **prüft sich selbst**. Die haltbare Aussage ist: die vertrauenswürdige **Fläche**
> schrumpft von 161 Fundstellen auf eine Emissionsstelle. Reduktion, nicht Beseitigung.

**Getötete bezahlte Fallen: keine.** Diese Stufe steht ohne Evidenz aus der Basisrate da — sie ist
notwendig, damit ein Kernel überhaupt entsteht, aber sie ist **kein** Argument für die Sprache.

### Stufe 6 — `check`: die Messdisziplin als Konstrukt · **33 Fallen, 15,7 % des Codes**

Die eigentliche Neuheit. Ein Prüfer ist heute gewöhnlicher Code, und **jede** der 33 Fallen ist ein
Prüfer, der etwas anderes prüfte, als draufstand.

```gabbro
check epfull
    aussage     "ein Ueberlauf der Endpoint-Warteschlange ist BENANNT"
    misst       ep.rejected_send, ep.rejected_recv
    gattert     abnahme                       -- PFLICHT
    sprechprobe { 5 Sonden gegen 4 Plaetze }  -- kann diese Zeile ueberhaupt fallen?
    untergrenze rejected_send >= 1            -- Null ist ein Befund, kein Messwert
    gegenprobe  "TidQueue::enqueue ignoriert die Kapazitaet"
        erwartet genau_ein_konjunkt_offen
```

Die Regeln sind keine Empfehlungen, sondern Übersetzungsfehler:

| Regel | tötet |
|---|---|
| Ein `check`, der in **keiner** Gatterliste steht, ist ein Fehler | **17** (Urteil entsteht erst im Bericht), und das `all_done()`-Loch 21 gegen 24 |
| **`sprechprobe` ist Pflicht** — ohne sie übersetzt der `check` nicht | **25**, **66**, **97** („ein leerer Lauf ist kein Testergebnis") |
| Eine gemessene Grösse, die der **gemessene Pfad selbst schreibt**, ist ein Fehler | **79**, **90** (die Marke, die der Pfad in seiner ersten Zeile löscht) |
| Einseitige Schwelle ohne `untergrenze` ist ein Fehler | **83** (`NOSEL_TEXT == 0` meldete PASS) |
| `misst` bindet an die Grösse; Nachrechnen ist nicht formulierbar | **21**, **70**, **78** (ein Byte statt 512) |
| `gegenprobe` muss **genau ein** Konjunkt öffnen | **71** (eine Mutation, die zwei Dinge kaputtmacht) |
| Nullbefunde tragen ihre Stichprobengrösse im Typ | **64**, **65** (0,99982²³⁰⁰ ≈ 66 %) |

**Was es nicht kauft:** ob die *Aussage* die richtige ist. Falle 91 (ein Prädikat, das
stellvertretend liest) fällt in die B-Klasse und bleibt.

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
4. **Die Umstellung erzwingt einen grossen Schnitt.** Ein Vorhaben, das die Abnahmereihe abschaltet,
   um sich selbst zu bauen, hat keinen Prüfer mehr — und dieses Projekt hat gemessen, was dann
   passiert: zehn Tage rot, ohne dass es jemand sah.
