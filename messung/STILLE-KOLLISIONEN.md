# Die Kollisionen, bei denen `cc` schweigt — und was dann zur Laufzeit passiert

**Gemessen am 2026-08-31**, lokal (`free -g`: 31 GB gesamt, 17 verfügbar, 20 Kerne).
`cc` ist `gcc (GCC) 16.2.1 20260810`, gefahren als
`cc -std=c11 -O0 -Wall -Wextra -Werror`. Die Proben liegen unter
`messung/stille-proben/`, die abgeleiteten (aus `beispiele/`) sind als Einzeiler-Aufsatz
beschrieben und in einer Minute nachgestellt.

`messung/ERZEUGERNAMEN.md` §3 nennt **eine** Form, bei der `cc` schweigt, und nennt sie *„die
unheimliche"*. Diese Messung zählt die Familie aus. **Es ist nicht eine Form, es sind fast
alle** — und die neun, die fallen, fallen aus einem Grund, der nichts mit der Klasse zu tun
hat.

---

## §1 Zuerst der Satz, dann die Tafel

Zwei Gabbro-Deklarationen bekommen denselben C-Namen. **Ob `cc` darüber spricht, hängt an
drei Dingen, und keines davon ist die Kollision selbst:**

1. **Sind die zwei C-Typen verträglich?** Zwei Funktionsdeklarationen desselben Typs sind in
   C eine zulässige Wiederholung.
2. **Definiert höchstens eine von beiden?** Prototyp plus Definition ist normal.
3. **In welcher REIHENFOLGE stehen sie?** C11 6.2.2p4: *eine nicht-statische Deklaration nach
   einer statischen erbt die interne Bindung.* Andersherum ist es ein Fehler.

> **Punkt 3 ist der, den man nicht erwartet, und er ist gemessen.**
> `messung/stille-proben/lnk.c` und `lnk2.c` unterscheiden sich in **zwei vertauschten
> Zeilen** und in nichts sonst:
>
> ```c
> static int f(void);   int f(void);          /* cc: exit 0 -- kein Wort   */
> int f(void);          static int f(void);   /* cc: exit 1 -- »Statische Deklaration
>                                                folgt nicht-statischer Deklaration« */
> ```
>
> *Und dieselbe Vertauschung lässt sich in Gabbro schreiben*, siehe §4 — mit byteidentischen
> Deklarationen, nur auf anderen Zeilen. **Ein Werkzeug, dessen Antwort an der Zeilennummer
> hängt, ist kein Orakel für diese Frage.** Das ist der stärkste Grund dafür, dass die Regel
> dem Prüfer gehört und nicht `cc`: nicht, dass `cc` sie manchmal nicht findet, sondern dass
> `cc` sie **je nach Quelltextreihenfolge findet oder nicht.**

## §2 Was der Erzeuger in welcher C-Form schreibt

Ausgemessen an einer kollisionsfreien Probe (`messung/stille-proben/`-Verfahren, Ausgabe von
`gabbro emit`), nicht aus `emit.rs` abgelesen — die Form entscheidet, und die steht im
Erzeugnis.

| Gabbro | C-Form | Bindung | definiert der Erzeuger? |
|---|---|---|---|
| `const K` | `#define K 7u` | — | — |
| `static mut z` | `static uint32_t z … = 0;` | intern | ja |
| `type V = {…}` | `typedef struct {…} V;` | — | — |
| `format F` | `typedef struct {…} F;` | — | — |
| `format F`, Feld `f` | `static inline … F_f(const F *)` | **intern** | **ja** |
| `format F` | `static inline bool F_gueltig(const F *)` | **intern** | **ja** |
| `tagged type T` | `typedef enum {…} T_marke;`, `typedef struct {…} T;` | — | — |
| `reason R` | `typedef enum {…} R;` | — | — |
| `table T` | `typedef struct{…} T_slot;`, `typedef struct{…} T;`, `#define T_NONE (…)` | — | — |
| `table T`, `ops` | `static void T_insert(…)` | **intern** | **ja** |
| `device D`, `bank B` | `static inline … D_B_r(…)` | **intern** | **ja** |
| `walk W` | `#define W_EBENEN`, `typedef struct{…} W_knoten;`, `static inline … W_ist_blatt(…)` | intern | ja |
| `atomic A` | `_Atomic T A;` | **extern** | ja (vorläufig) |
| `atomic A` **mit** Ordnung ≠ `relaxed` | `#define A_ORDER memory_order_…` | — | — |
| `lock L` | `void L_nimm(void);` `void L_gib(void);` | **extern** | **NEIN** |
| `rcu N` | `void N_lese_start(void);` `void N_lese_ende(void);` | **extern** | **NEIN** |
| `entry e` | `void gabbro_eintritt_e(void);` | **extern** | **NEIN** |
| `boot b` | `void gabbro_boot_b(void);` | **extern** | **NEIN** |
| `entrust t` | `void gabbro_gast_t(void);` | **extern** | **NEIN** |
| `check c` | `bool pruefe_c(void);` **und** `bool pruefe_c(void) {…}` | **extern** | **ja** |
| `accumulates n` | `static … n_lies(void)`, `static void n_melde(…)`, `static _Atomic … n_zellen[…]` | intern | ja |
| ein Baum mit `accumulates` | `uint32_t gabbro_kern(void);` | **extern** | **NEIN** |
| `fn` ohne Rumpf | `T f(args);` | extern | nein |
| `impl fn` ohne `pub` | `static T f(args) …;` + Rumpf | **intern** | ja |
| `pub impl fn` | `T f(args) …;` + Rumpf | extern | ja |

## §3 Die Tafel: dreizehn Proben, gefahren

`N042` ist der ausgelieferte Prüfer dieses Standes. `cc` ist `-fsyntax-only` über das
Erzeugnis; wo `N042` spricht, ist das Erzeugnis mit einem Prüfer ohne diesen einen Aufruf
gewonnen — **derselbe Baum, eine Zeile auskommentiert, sofort zurückgestellt**, und der
Zweig ist sauber (`git diff` leer).

| Probe | die zwei Deklarationen | `N042` | `cc` | Urteil |
|---|---|---|---|---|
| `m1-hijack` | `lock TOR` × `pub impl fn TOR_nimm()` | **1** | still | gedeckt — **Laufzeit gemessen, §4** |
| `m2-extern` | `lock TOR` × `extern fn TOR_nimm()` | **1** | still | gedeckt — die zehnte Form aus ERZEUGERNAMEN §3 |
| `m5-static` | `lock TOR` × `impl fn TOR_nimm()` *(ohne `pub`)* | **1** | **weist ab** | gedeckt; `cc` fängt sie auch |
| `m8-format` | `format Eintrag{a}` × `extern fn Eintrag_a(ptr<normal,r> Eintrag)->u32` | **1** | **still** | gedeckt — **und `cc` schweigt, sobald der Typ passt** |
| `m8b-format` | dieselbe, Reihenfolge vertauscht | **1** | weist ab | gedeckt |
| `m6b-order` | `atomic Z : u32 release` × `const Z_ORDER` | **1** | weist ab | gedeckt, echt |
| `m6-order` | `atomic Z : u32 relaxed` × `const Z_ORDER` | **1** | still | **FEHLALARM** — §5 |
| `m3-check` | `check kontostand` × `extern fn pruefe_kontostand()->bool` | **0** | still | **LÜCKE** — Laufzeit gemessen, §4 |
| `m4-boot` | `boot multiboot1` × `extern fn gabbro_boot_multiboot1()` | **0** | still | **LÜCKE** |
| `m4-gast` | `entrust jitpuffer` × `extern fn gabbro_gast_jitpuffer()` | **0** | still | **LÜCKE** |
| `m4-kern` | `accumulates …` × `extern fn gabbro_kern()->u32` | **0** | still | **LÜCKE** |
| `m7-akk` | `accumulates hoechststand` × `extern fn hoechststand_lies()->u64` | **0** | still | **LÜCKE** |
| `m7b-akk` | dieselbe, Reihenfolge vertauscht | **0** | **weist ab** | **LÜCKE** — §4, der Reihenfolgebefund |

`m4-*` und `m7-*` sind `beispiele/07-eintritt-und-boot.gab`, `beispiele/25-entrust.gab` und
`beispiele/23-akkumulatoren.gab` mit **einer angehängten Zeile**; sie stehen darum nicht als
Kopie hier.

> **`m4-boot` und `m4-gast` und `m4-kern` und `m3-check` und `m7-akk` melden `0 errors,
> 0 hints`**, und `cc -Werror` übersetzt das Erzeugnis. Fünf Formen, bei denen **die ganze
> Kette schweigt** — der Prüfer, der Erzeuger und der C-Übersetzer.

## §4 Was zur Laufzeit passiert — vier ausgeführte Programme

*Ein Fehler, den kein Werkzeug meldet, ist teurer als zehn, die `cc` fängt.* Also ausgeführt
und nicht überlegt. Die Treiber stehen daneben.

### (a) Die Sperre wird nicht genommen — sie ruft den Nutzer

`m1-hijack.gab`: `lock TOR` und `pub impl fn TOR_nimm()`, deren Rumpf `spur = 7` schreibt.
Im Erzeugnis:

```c
void TOR_nimm(void);            /* das Primitiv der SPERRE   */
void TOR_nimm(void);            /* der Prototyp des NUTZERS   */
void TOR_nimm(void) { spur = 7; }
void arbeite(void) { TOR_nimm(); nutz = 1; TOR_gib(); }
```

`cc -Werror`: **exit 0.** Ausgeführt:

```
spur vor  = 0
spur nach = 7
nutz      = 1
```

**Es wurde keine Sperre genommen.** `arbeite()` hat den Rumpf des Nutzers ausgeführt, den
geschützten Ort beschrieben und wieder freigegeben. `nutz = 1` steht da, als sei alles in
Ordnung. *Das ganze `protects`, der ganze `rank`, die ganze Haltezeitrechnung — sie stehen
über einem Aufruf, der woanders hingeht.*

**Die Gegenprobe steht daneben:** `m5-static.gab` ist dieselbe Datei ohne das `pub`. Dann
schreibt der Erzeuger `static void TOR_nimm(void)`, und `cc` weist ab
(*„Statische Deklaration von »TOR_nimm« folgt nicht-statischer Deklaration"*). **Ein Wort
entscheidet, ob die Kette spricht.**

### (b) Ein Rumpf, zwei Wege

`m2-extern.gab`: `lock TOR` und `extern fn TOR_nimm()`, dazu eine Gabbro-Funktion, die
`TOR_nimm()` selbst ruft. Der fremde Rumpf liegt in `m2-fremd.c` und zählt mit.

```
arbeite() -- die SPERRE wird genommen:
  [fremd] TOR_nimm gerufen, jetzt 1 mal
  [fremd] TOR_gib gerufen
ruft_selbst() -- der Nutzer ruft SEINE Funktion:
  [fremd] TOR_nimm gerufen, jetzt 2 mal
ein Rumpf, zwei Wege: 2 Rufe
```

Der Schreiber des fremden C sieht **zwei** Aufrufer, wo er einen geschrieben hat. Und die
Sperre nimmt, was immer dort steht.

### (c) Die eigene Bibliothek wird nie gebunden

`m3-check.gab`: ein `check kontostand` und daneben `extern fn pruefe_kontostand() -> bool`.
Der Schreiber liefert seinen Rumpf in `libmein.a` aus — der übliche Weg. Der Erzeuger
**definiert** `pruefe_kontostand` in derselben Einheit; der Binder findet das Symbol schon
und holt das Archivglied gar nicht.

```
frage() = true   (fremd sagt false, die Probe sagt true)
```

`N042` schweigt (`0 errors, 0 hints`), `cc -Werror` schweigt, der Binder schweigt. **Der
Aufruf des Schreibers landet in einem Prüfkörper, den er nicht gemeint hat.**

*Wird die fremde Datei stattdessen direkt gebunden, ist es laut* —
`ld: Mehrfachdefinition von »pruefe_kontostand«`. **Die Stille hängt daran, wie gebunden
wird**, und das ist keine Eigenschaft des Programms.

### (d) Derselbe Griff bei einem `format`-Leser

`m8-format.gab`: `format Eintrag { a }` neben `extern fn Eintrag_a(v : ptr<normal, r>
Eintrag) -> u32`. `ERZEUGERNAMEN.md` §2 führt genau diese Paarung als Fall 9 und schreibt
*„abweichende Typen"* daneben. **Das war die Signatur, nicht die Klasse.** Mit passender
Signatur:

```
frag() = 42   (fremd sagt 999, der erzeugte Leser sagt 42)
```

`cc -Werror`: exit 0. Der `static inline`-Leser des Erzeugers steht **vor** dem Prototyp des
Nutzers, also erbt dieser die interne Bindung (C11 6.2.2p4), und das Archivglied wird nie
angefasst. `N042` fängt es — *aber nur `N042`.*

**Und die Reihenfolge ist wirklich die Ursache:** `m7-akk` gegen `m7b-akk` sind dieselbe
Datei; in der einen steht `extern fn hoechststand_lies()` **hinter** dem `accumulates`, in
der anderen davor. `cc` sagt einmal nichts und einmal *„Statische Deklaration folgt
nicht-statischer Deklaration"*. **Byteidentische Deklarationen, verschiedene Zeilen,
verschiedene Antwort.**

## §5 Ein Fehlalarm, und er ist derselbe Fehler wie `{T}_speicher`

`erzeugernamen.rs` listet `{Atomic}_ORDER` **unbedingt**. Der Erzeuger schreibt es aber nur,
wenn die Ordnung nicht `relaxed`-ohne-Nutzlast ist (`emit.rs`, `ItemArt::Atomic`, der
`Some(o)`-Zweig).

`m6-order.gab`:

```gabbro
atomic ZAEHLER : u32 relaxed;
const ZAEHLER_ORDER : u32 = 3;
```

`N042` weist ab. Im Erzeugnis steht **ein einziges** `ZAEHLER_ORDER`, nämlich
`#define ZAEHLER_ORDER 3u` — das des Nutzers. `cc -Werror`: exit 0. **Eine Absage ohne
Mangel**, und zwar genau die Sorte, gegen die `ERZEUGERNAMEN.md` §7 den
`{T}_speicher`-Ausschluss geschrieben hat: *ein gelisteter Name, den der Erzeuger nie
schreibt.*

Die Gegenprobe `m6b-order.gab` (dieselbe Datei mit `release`) ist echt: `cc` meldet
*„»ZAEHLER_ORDER« redefiniert"*. **Die Bedingung steht im Baum** (`a.ordnung`,
`a.obermenge`) und ist damit hier beantwortbar — anders als bei `{T}_speicher`, wo sie in den
`Namen` des Erzeugers lebt.

## §6 Die volle Familie, in drei Sorten

**Sorte A — äußere Prototypen, die der Erzeuger NIE definiert.** Hier ist die Kollision
*immer* still, sobald der Nutzer den Typ trifft, und der Typ ist trivial zu treffen
(`void f(void)`). Der fremde Rumpf des Nutzers wird der Rumpf des Erzeugnisses.

| Name | Typ | in der Aufzählung? |
|---|---|---|
| `{L}_nimm`, `{L}_gib`, `{L}_nimm_geteilt`, `{L}_gib_geteilt` | `void(void)` | ja |
| `{Rcu}_lese_start`, `{Rcu}_lese_ende` | `void(void)` | ja |
| `gabbro_eintritt_{e}` | `void(void)` | ja |
| **`gabbro_boot_{b}`** | `void(void)` | **NEIN** |
| **`gabbro_gast_{t}`** | `void(void)` | **NEIN** |
| **`gabbro_kern`** | `uint32_t(void)` | **NEIN** |

*`gabbro_boot_{b}` ist die schärfste der drei: das ist die Adresse, an die die Maschine
springt.*

**Sorte B — äußere Namen, die der Erzeuger DEFINIERT.** Der eigene Rumpf des Nutzers wird
verdrängt oder der Binder meldet Mehrfachdefinition — je nachdem, wie gebunden wird.

| Name | Typ | in der Aufzählung? |
|---|---|---|
| **`pruefe_{c}`** | `bool(void)` | **NEIN** |
| `{A}` (atomic) | `_Atomic T` | ja |

**Sorte C — innere (`static`) Namen des Erzeugers.** Still, solange die erzeugte Deklaration
**zuerst** steht und der Typ passt — und zuerst steht sie, wenn der Träger im Quelltext vor
der Nutzerdeklaration steht.

| Namen | in der Aufzählung? |
|---|---|
| `{F}_{feld}`, `{F}_setz_{feld}`, `{F}_gueltig` | ja |
| `{T}_{op}` | ja |
| `{D}_{bank}_{reg}`, `{D}_{bank}_setz_{reg}`, `{D}_{übergang}` | ja |
| `{W}_ist_blatt`, `{W}_steigt_ab`, `{W}_absteigen` | ja |
| **`{acc}_lies`, `{acc}_melde`, `{acc}_zellen`** | **NEIN** |
| **`gabbro_boot_{b}_dispatch`** | **NEIN** |

**Und die acht der neun aus `ERZEUGERNAMEN.md` §2, die nicht Fall 9 sind, gehören in keine
der drei.** Sie sind *strukturell* laut, nicht zufällig:

* Fälle 1, 2, 3, 6 sind zwei Anhänge desselben Trägers — also zwei **Definitionen** derselben
  Funktion oder zwei Aufzählungswerte. C hat dafür kein Schlupfloch.
* Fälle 4 und 7 sind zwei `typedef` auf **anonyme** Verbunde; zwei anonyme Verbunde sind nie
  verträglich.
* Fälle 5 und 8 sind ein Makro gegen einen Aufzählungswert bzw. gegen ein zweites Makro mit
  anderer Ersetzungsliste.

*Die neun sind also nicht neun laute und eine stille, sondern acht strukturell laute, eine
zufällig laute (Fall 9) und eine strukturell stille (Fall 10).*

## §7 Was das für `N042` heißt

Die Aufzählung ist an **sechs** Stellen unvollständig und an **einer** zu weit:

| | was fehlt / zu viel ist | belegt durch |
|---|---|---|
| fehlt | `ItemArt::Check` ganz — `pruefe_{c}` | `m3-check`, ausgeführt |
| fehlt | `ItemArt::Entrust` ganz — `gabbro_gast_{t}` | `m4-gast` |
| fehlt | `ItemArt::Accumulates` ganz — `{n}_lies`, `{n}_melde`, `{n}_zellen` | `m7-akk`, `m7b-akk` |
| fehlt | `gabbro_boot_{b}` (nur die `_s{i}` und `_{setzt}` stehen da) | `m4-boot` |
| fehlt | `gabbro_boot_{b}_dispatch` | Erzeugnis von `beispiele/07` |
| fehlt | `gabbro_kern`, sobald der Baum ein `accumulates` trägt | `m4-kern` |
| zu viel | `{A}_ORDER` unbedingt statt nur bei Ordnung ≠ `relaxed`-ohne-Nutzlast | `m6-order` gegen `m6b-order` |

**Was diese Messung NICHT sagt:** dass jede der sechs eine Absage verdient. Das entscheidet
Regel A am Korpus, nicht diese Tafel. *Hier steht der Mangel; die Kosten stehen dort.*
