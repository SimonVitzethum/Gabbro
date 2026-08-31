# Sechs Adressräume, und der Erzeuger liest KEINEN

**Gemessen am 2026-08-31**, lokal (`free -g`: 31 GB gesamt, 18 verfügbar, 20 Kerne — die
Grenze aus `CLAUDE.md` ist damit eingehalten und nicht bloß gehofft).

Der Auftrag nannte den Befund so: *„`ctyp` liest `z.raum` für JEDEN Raum außer `mmio`
nicht."* **Die Messung sagt es schärfer:** `ctyp` liest `z.raum` für *keinen* Raum. Dass
`mmio` trotzdem richtig herauskommt, liegt nicht am Zeiger, sondern daran, dass **jeder
saubere `ptr<mmio, …>` im Korpus auf einen `device`-Typ zeigt** — und das `volatile` kommt
aus der `device`-Absenkung, nicht aus dem Raum am Zeiger. *Ein Raum, der nur deshalb
ankommt, weil kein Gegenbeispiel geschrieben wurde, ist keine Zusage.*

---

## §1 Die Stelle

`crates/gabbro-check/src/emit.rs`:3702, `fn ctyp`. Der Zweig für `TypExpr::Zeiger(z)` liest
genau zwei Dinge aus `z`: `z.ziel` (für den Zieltyp) und `z.rechte` (für das `const`).
**`z.raum` steht nicht darin.** Der ganze Zweig steht bei :3801–3823.

```rust
let konst = if z.rechte.iter().any(|r| matches!(r,
    Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_))) { "" } else { "const " };
Some(format!("{konst}{ziel} *"))
```

`grep -n 'Raum::' crates/gabbro-check/src/emit.rs` liefert **zwei** Treffer, beide in
`fn geraet` (:2507, :2516) und beide über `device … at <raum>` — **keiner über einen
Zeigertyp.**

## §2 Die Gegenprobe: sechs Räume, ein Ziel, ein Rumpf

Sechs Funktionen, die sich in *nichts* unterscheiden als im Raumwort:

```gabbro
type Zelle = { wert : u32, };
impl fn r_normal(p : ptr<normal, r> Zelle) -> u32 effects { reads p } costs <= 2 ops { return p.wert; }
impl fn r_mmio  (p : ptr<mmio,   r> Zelle) -> u32 effects { reads p } costs <= 2 ops { return p.wert; }
impl fn r_dma   (p : ptr<dma,    r> Zelle) -> u32 effects { reads p } costs <= 2 ops { return p.wert; }
impl fn r_code  (p : ptr<code,   r> Zelle) -> u32 effects { reads p } costs <= 2 ops { return p.wert; }
impl fn r_boot  (p : ptr<boot,   r> Zelle) -> u32 effects { reads p } costs <= 2 ops { return p.wert; }
impl fn r_port  (p : ptr<port,   r> Zelle) -> u32 effects { reads p } costs <= 2 ops { return p.wert; }
```

`gabbro pruefe`: **8 items, 0 errors, 0 hints.** `gabbro emit`, alle sechs Rümpfe:

```c
static uint32_t r_normal(const Zelle *restrict p) { return p->wert; }
static uint32_t r_mmio  (const Zelle *restrict p) { return p->wert; }
static uint32_t r_dma   (const Zelle *restrict p) { return p->wert; }
static uint32_t r_code  (const Zelle *restrict p) { return p->wert; }
static uint32_t r_boot  (const Zelle *restrict p) { return p->wert; }
static uint32_t r_port  (const Zelle *restrict p) { return p->wert; }
```

**Sechs Zeilen, ein Text.** Und alle sechs tragen `__attribute__((pure))` — bei `mmio` und
`port` ist das nicht bloß ein fehlendes `volatile`, sondern die *gegenteilige* Zusage:
`pure` erlaubt dem Übersetzer, den zweiten Ruf zu streichen. *Ein Registerlesen, das
wegoptimiert werden darf, ist die Registerfalle mit Erlaubnis.*

## §3 Was jeder Raum bedeuten soll — und was heute ankommt

| Raum | Zusage | Fundstelle | im C heute | Urteil |
|---|---|---|---|---|
| `normal` | gewöhnlicher Speicher | `SYNTAX.md`:463 | `T *` | **richtig** |
| `mmio` | flüchtiger Zugriff, kein Zwischenspeicher | `SPRACHE.md` A12 | `T *` — das `volatile` kommt aus `device`, nicht aus dem Zeiger | **richtig nur auf `device`-Zielen** |
| `dma` | ein Gerät schreibt mit; Barriere ungeklärt | `m3.rs`:8 | `T *` | **richtig nur, weil `R001`/`R008` daneben stehen** |
| `code` | ausführbarer Raum, Inhalt fremd | `SYNTAX.md`:268 | `struct T *` (unvollständig) | **richtig** — nur `extern fn`-Ziele, nie dereferenziert |
| `boot` | Speicher, den der Bootlader beschrieb; `.boot` ist ein Linkerabschnitt | `SYNTAX.md`:1607 | `T *` | **richtig** — ein gewöhnlicher Ladebefehl ist dort der richtige |
| `port` | `in`/`out`, **keine** Ladebefehle | `SPRACHE.md` §2188 | `T *`, gewöhnliche Ladung | **FALSCH** |

Nur **eine** Zeile ist falsch, und sie ist es unter einer wörtlichen Zusage. `SPRACHE.md`:2188:

> *„`at port` lowers accesses to `in`/`out` instead of to volatile loads/stores"*

## §4 Und am `device` ist es schlimmer als am Zeiger

Der Zeiger schweigt; das `device` **antwortet falsch**. `device SerialCom1 at port` prüft
mit 0 Fehlern und senkt ab zu:

```c
typedef struct { volatile uint8_t *basis; } SerialCom1;
static bool lies_lsr(const SerialCom1 *restrict d) {
    return (((*(volatile uint8_t *)(d->basis + 1021)) >> 5) & 1u);
}
```

`1021` ist `0x3FD` — die **Portnummer** des Leitungsstatusregisters, hier als **Versatz auf
einen Speicherzeiger** ausgegeben. Das erzeugte C liest RAM an `basis + 0x3FD`. *Es ist
nicht ein fehlender Befehl; es ist ein anderer Befehl auf eine andere Sache.*

Dasselbe für `at boot` und `at code` — beide werden angenommen und beide senken zum
`mmio`-Text ab, Wort für Wort.

Und die zweite Hälfte derselben Zusage steht auch nicht: `SPRACHE.md`:2189 sagt, ein
`port`-Gerät sei *„declarable only under `arch x86_64`"*. Die Probe oben trägt **kein**
`arch` und wird angenommen.

## §5 Wo die Räume WIRKLICH gehalten werden — und wovon

Nicht vom Erzeuger, sondern vom Prüfer, und zwar an drei Stellen (`m3.rs`):

* **`R008`** — der Raum am Argument muss dem Raum am Parameter *gleichen*. Ein
  `ptr<normal, …>` kommt nicht in ein `ptr<mmio, …>`-Loch.
* **`R001`** — ein `ops`-Träger in einem `dma`-Raum wird abgewiesen.
* **W9-Klausel** (`m3.rs`:22) — wo der Zeigertyp nicht auflösbar ist, sagt der Pass *nichts*,
  statt `normal` anzunehmen.

**Das ist eine Trennung und keine Lücke: der Raum ist eine Aussage über die *Herkunft* eines
Zeigers, und die trägt der Prüfer.** Was der Erzeuger schuldet, ist nur die *Zugriffsform* —
und die unterscheidet sich zwischen den sechs Räumen an genau **einer** Stelle: `port`.

## §6 Der Bedarf, gezählt (Regel A)

`grep -rhoE 'ptr<[a-z]+' beispiele/ messung/ --include=*.gab`:

| Raum | Zeigerstellen | davon dereferenziert in einem erzeugten Rumpf |
|---|---:|---:|
| `normal` | 249 | viele |
| `mmio` | 28 | alle auf `device`-Zielen (die drei Gegenbeispiele liegen in `gift/`) |
| `dma` | 13 | — |
| `port` | **2** | **2** |
| `code` | 2 | 0 — beide an `extern fn`, unvollständiger Typ, nie dereferenziert |
| `boot` | 1 | 1 — und ein Ladebefehl ist dort richtig |

`device … at <raum>` über denselben Korpus: **34× `mmio`, 5× `dma`, 0× `port`, 0× `boot`,
0× `code`, 0× `normal`** (`at normal` wird schon abgewiesen, `emit.rs`:2507).

**Die zwei `port`-Zeigerstellen:**

| Datei | Zeile | Form |
|---|---:|---|
| `messung/grammatik/geraeteworte.gab` | 55 | `impl fn tor_lesen(p : ptr<port, r> Stand) -> bool` |
| `messung/grammatik/raumworte.gab` | 94 | `impl fn tor_bereit(p : ptr<port, r> Torstand) -> bool` |

Beide dereferenzieren ein Feld eines gewöhnlichen Verbunds über einem Portzeiger. **Und
genau das hat keine Bedeutung:** `in`/`out` brauchen eine *Portnummer*, und ein Feld eines
Verbunds an einem Versatz ist keine. Es gibt keine Absenkung, die der Erzeuger hier
verschweigt — es gibt keine.

*Die Datei sagt es in ihrem eigenen Kommentar* (`raumworte.gab`:59): „Portraum ist kein
Speicher -- auf x86_64 sind das `in`/`out` und keine Ladebefehle." **Der Kommentar stimmt,
das Erzeugnis nicht.**

## §7 Was daraus folgt — und was ausdrücklich nicht

**`in`/`out` zu bauen ist nach Regel A NICHT gedeckt.** Null `device … at port` im ganzen
Korpus; die einzige Form, die `port` überhaupt gebrauchen könnte, ist nicht geschrieben.
Wer sie baut, baut sie gegen kein Programm.

**Was gedeckt ist, ist die Absage** — und sie hat einen gemessenen Mangel unter sich: zwei
Zeigerstellen, die ein Erzeugnis bekommen, das etwas anderes tut als die Zeile sagt, und ein
`device … at port`, das eine Portnummer als Speicherversatz ausgibt. Die Absage steht
**dort, wo `at normal` und `at dma` schon abgewiesen werden** (`emit.rs`:2507/2516) und
kostet über den Korpus null Zeilen an `device`-Stellen.

Für die zwei Zeigerstellen kostet sie zwei Zeilen, und beide sind der Mangel selbst.

*Nicht abgesagt werden `code` und `boot`.* Bei `code` wird nie dereferenziert (unvollständiger
Typ, `extern fn`), bei `boot` ist der gewöhnliche Ladebefehl die richtige Absenkung — `.boot`
ist ein Linkerabschnitt und kein anderer Befehlssatz (`SYNTAX.md`:1607). **Eine Absage über
diesen beiden wäre eine ohne Mangel**, und in dieser Nacht wurde schon eine solche
zurückgenommen.

## §8 Gebaut: zwei Absagen, und die zweite kostet null

**Beide sind `C001` und beide stehen im ERZEUGER**, nicht im Prüfer — anders als bei `N042`
nebenan, und der Unterschied hat einen Grund: `N042` redet über einen **Namen**, den der
Schreiber ändern kann, ohne sein Programm zu ändern. Hier redet die Absage über eine
**Absenkung, die es nicht gibt**, und das ist genau die Frage, für die `C001` da ist.

| | wo | was es kostet |
|---|---|---|
| ein Rumpf, der einen `ptr<port, …>` trägt | `emit.rs::funktion` | **zwei Stellen in 426 Dateien**, und beide waren der Mangel |
| `device … at port` | `emit.rs::geraet` | **null Stellen** |

Die zwei Zeigerstellen sind geheilt statt weggeworfen: `messung/grammatik/geraeteworte.gab`
und `messung/grammatik/raumworte.gab` tragen ihren `port`-Rumpf jetzt als **fremden**
(`extern fn`). Das Wort `port` bleibt gedeckt — es steht am *Typ*, und der Typ steht dort —,
und die Absenkung, die es nicht gibt, steht nicht mehr da. **Die Ratsche
`MARKE_EMIT_M` bleibt bei 30**; keine Datei hat die Emission verlassen.

Proben: `beispiele/gift/415-portzeiger-im-eigenen-rumpf.gab` und
`beispiele/gift/416-geraet-am-portraum.gab`, beide mit `-- erwartet: C001`.

**Die Zeigerregel hält an der SIGNATUR und nicht am Zugriff** (W10). Ein Rumpf, der einen
Portzeiger nimmt und nie anfasst, fällt auch — gröber als der Mangel und gröber in die
sichere Richtung. Eine Regel am Zugriff bräuchte den Raum des Zeigers an jeder Zugriffsstelle,
und die Ausdrucksabsenkung trägt ihn nicht.

## §9 Was ausdrücklich NICHT gebaut wurde

* **`in`/`out`.** Null `device … at port` im Korpus. Regel A sagt: kein Konstrukt ohne
  gemessenen Bedarf. *Wer es baut, baut es gegen kein Programm.*
* **Eine Absage über `boot`, `code`, `dma` oder `mmio` am Zeiger.** §3 rechnet jede der vier
  einzeln nach, und keine ist ein Mangel.
* **Die `arch x86_64`-Pflicht am `port`-Gerät** (`SPRACHE.md`:2189). Sie wäre eine zweite
  Regel über einem Konstrukt, das jetzt ganz abgewiesen wird — W7. *Sie gehört an den Tag, an
  dem `at port` eine Absenkung bekommt, und steht bis dahin hier.*
* **Ein `volatile` am `ptr<mmio, …>`.** Im sauberen Korpus zeigt jeder auf einen
  `device`-Typ, und dort trägt es die Geräteabsenkung. Die drei Gegenbeispiele liegen in
  `gift/` und fallen aus anderen Gründen. *Ein `mmio`-Zeiger auf einen gewöhnlichen Verbund
  ist heute keine gemessene Form* — er steht als Posten im `TODO.md` und nicht als Absage.
