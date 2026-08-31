# Namen, die C schon vergeben hat — die Grundgesamtheit, gemessen

*Gemessen am 2026-08-31, Bahn F5, Posten 1. **Der `W24`-Vorlauf steht vor jeder Zeile Code**:
erst die naheliegende Form durch den UNVERÄNDERTEN Prüfer, dann die Entscheidung.*

Lokal gemessen (`free -g`: **31 GB gesamt, 16 GB verfügbar, 20 Kerne** — der Prüfer baut in
10 s Wanduhr und bleibt damit diesseits der 1-GB-Grenze aus `CLAUDE.md`), `cc` = GCC unter
`LC_ALL=C`, Prüfer aus `cargo build --release` desselben Standes.

---

## 1. Der `W24`-Vorlauf — was der unveränderte Prüfer tut

Die Datei, die die Frage stellt (drei Items, sonst nichts):

```gabbro
module w24::kollision {

extern fn exit() -> never effects { diverges };

pub fn haupt() -> u64
    effects { pure }
{
    return 7;
}

}
```

**`gabbro pruefe` sagt nichts:**

```
w24-exit.gab: 3 items, 0 errors, 0 hints
  M1 saw 1 expressions, 0 of them without a type (100 % coverage)
```

**`gabbro emit` schreibt 20 Zeilen C**, und darin steht wörtlich:

```c
#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <math.h>

_Noreturn void exit(void);
```

**`cc` weist sie zurück:**

```
w24-exit.c:14:16: error: conflicting types for built-in function 'exit'; expected 'void(int)'
                  [-Werror=builtin-declaration-mismatch]
   14 | _Noreturn void exit(void);
      |                ^~~~
w24-exit.c:13:1: note: 'exit' is declared in header '<stdlib.h>'
```

> **Damit ist die Lage benannt, bevor irgendetwas repariert wurde:** der Prüfer nimmt an, der
> Erzeuger schreibt, und die dritte Stufe fällt. *Genau die Eigenschaft, gegen die
> `PLAN-VOLLSTAENDIGKEIT.md` §2 geschrieben ist — «Prüfer nimmt an ⇒ es gibt C» —, und sie ist
> hier an drei Zeilen widerlegt.*

---

## 2. Welche Gabbro-Namen überhaupt als C-Bezeichner erscheinen

Gemessen an einer Datei mit je einer Deklaration jeder Art (`w24-arten.gab`, 46 Zeilen C):

| Gabbro | im C |
|---|---|
| `const KONST` | `#define KONST 1u` |
| `type Verbund` | `typedef struct { … } Verbund;` |
| `tagged type Marke` | `Marke_marke`, `Marke_Eins`, `Marke_Zwei`, `Marke` |
| `reason Grund` | `typedef enum { Grund_Weg = 1 } Grund;` |
| `extern fn fremd` | `uint64_t fremd(uint64_t x);` |
| `pub fn oeffentlich` | `uint64_t oeffentlich(uint64_t y)` — Deklaration **und** Rumpf |
| `impl fn innen` | `static uint64_t innen(uint64_t z)` |

**Der Erzeuger bildet den Gabbro-Namen unverändert ab.** Es gibt keine Verzierung, keinen
Modulpräfix, keine Fluchtform — `emit.rs` kennt keine `fn c_name`. *Was in Gabbro steht, steht
in C.*

---

## 3. Die Grundgesamtheit, in drei Klassen und je mit ihrem Befehl

**Nicht die vollständige C-Norm** — die Menge, die ein Gabbro-Programm hinschreiben kann und
die der Erzeuger wirklich erzeugt.

| Klasse | roh | Gabbro-reserviert | **erreichbar** | woher |
|---|---:|---:|---:|---|
| **C11-Schlüsselwörter** | 44 | 7 | **37** | C11 §6.4.1 |
| **die vier Header des Erzeugers** | 370 | 4 | **366** | `cc -dM -E`, `cc -aux-info`, `typedef`-Auszug |
| **eingebaute Funktionen von GCC** | 326 | 1 | **325** | gemessen, Datei für Datei |
| **Vereinigung** | | | **558** | `header` 366 · `keyword` 37 · `builtin` 155 |

Die sieben unerreichbaren C-Schlüsselwörter sind `const else extern if return sizeof static` —
sie stehen im Gabbro-Wortschatz (221 Wörter, 212 davon reserviert) und fallen schon an `P002`,
*„`x` is a word of the vocabulary, not an identifier"*. **Gemessen, nicht angenommen:** ein
`const bool : u64 = 3;` fällt heute an `P002`, nicht an einer neuen Regel.

Je Header:

| Header | Namen ohne führenden Unterstrich |
|---|---:|
| `math.h` | 200 |
| `stdint.h` | 89 |
| `stdatomic.h` | 78 |
| `stdbool.h` | 3 |

**Die eingebauten Funktionen sind die Klasse, die `F05` getroffen hat**, und sie ist die
unheimlichste: sie wirkt **ohne jeden `#include`**. Gemessen wurde sie so — je Kandidat eine
Datei ohne einen einzigen Header:

```c
typedef unsigned long u64;
u64 exit(u64 a);
u64 exit(u64 a) { return a; }
```

`cc -std=c11 -O0 -Wall -Wextra -Werror` bricht mit *„built-in function"*. Von 472 Kandidaten
(alle Funktionsnamen, die die vollständige C11-Headermenge deklariert, kleingeschrieben)
fallen **326** so.

---

## 4. Welche FORM woran bricht — und der erste Befund gegen `TODO.md`

Je Name × je Form, die der Erzeuger wirklich schreibt (mit seinen Attributen), gegen
`cc -std=c11 -O0 -Wall -Wextra -Werror`:

| Name | `extern fn` | `pub fn` | `impl fn` | `const` | `type` | `tagged` | `reason` | `let` | Parameter |
|---|---|---|---|---|---|---|---|---|---|
| `exit` `abort` `malloc` `free` `memcpy` `printf` | **BRICHT** | **BRICHT** | **BRICHT** | ok | ok | ok | ok | ok | ok |
| `read` `write` `index` `signal` | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| `int` `switch` `_Bool` `_Noreturn` | **BRICHT** | **BRICHT** | **BRICHT** | ok | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** |
| `bool` `true` `NAN` | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** |
| `INFINITY` | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | ok | ok | ok | **BRICHT** | ok |
| `uint64_t` | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | ok | ok |
| `atomic_load` | **BRICHT** | **BRICHT** | **BRICHT** | **BRICHT** | ok | ok | ok | ok | ok |
| `__builtin_x` `_Grosz` `_klein` | ok | ok | ok | ok | ok | ok | ok | ok | ok |

> ### Befund 1: `read` ist keiner. `TODO.md`:286 sagt es falsch.
>
> Dort steht: *„Ein Nutzer, der seine Funktion `exit`, `abort`, `free` oder **`read`** nennt,
> erfährt es vom fremden Übersetzer."* **`read` erfährt nichts.** Es ist POSIX, keine
> eingebaute Funktion von GCC und in keinem der vier Header des Erzeugers — `uint64_t
> read(uint64_t);` übersetzt tadellos. *Drei von vier Beispielen stimmten, das vierte war
> danebengegriffen, und niemand hat es nachgerechnet, weil die ersten drei trugen.*

> ### Befund 2: die reservierten Präfixe von C11 §7.1.3 brechen NICHT.
>
> `__builtin_x`, `_Grosz`, `_klein` sind nach der Norm reserviert — und `cc` nimmt sie an. **Es
> gibt keinen gemessenen Bedarf für eine Regel gegen den führenden Unterstrich**, und Regel A
> sagt: dann keine. *Was der Ordner davon trägt, steht in §6 als benannte Absage.*

---

## 5. Was die Regel den Baum kostet — die Ratsche, vorher gerechnet

Über alle **418 `.gab`-Dateien**, **743 verschiedene Item-Namen auf oberster Ebene**:

```
Treffer: 1
  exit    eingebaute Funktion    messung/fragmente/F05.gab
Namen mit fuehrendem Unterstrich: 0
```

**Ein einziger.** Und es ist genau der, für den die Regel gebaut wird. *Eine Regel, die 558
Namen verbietet und im ganzen Korpus eine Zeile trifft, ist keine Verschärfung des Baums,
sondern eine Absage an einen Fall, den bisher niemand geschrieben hat.*

---

## 6. Was NICHT gebaut wird, und warum

* **Keine Regel gegen den führenden Unterstrich.** C11 §7.1.3 reserviert `_` + Großbuchstabe
  und `__` — gemessen bricht nichts davon (§4, Befund 2), und der Korpus hat null solche
  Namen. *Regel A: kein Konstrukt ohne gemessenen Bedarf.*
* **Die 883 Namen mit führendem Unterstrich, die die vier Header stellen** (`_STDINT_H`,
  `__GLIBC__`, …) stehen **nicht** in der Liste. Sie sind die Schreibweise **einer** libc, nicht
  die von C — eine Liste, die sie trägt, misst glibc und nennt es C.
* **Keine Umbenennung im Erzeuger.** Ein Erzeuger, der `exit` still zu `gabbro_exit` macht,
  löst das Übersetzungsproblem und verschiebt die Erklärung in eine Ausgabe, die niemand liest.
  *Der Prüfer sagt es, oder es wird nicht gesagt.*
* **Keine Ausnahme für `extern fn`.** Eine `extern fn exit(…)` sieht aus wie die FFI-Zeile, die
  C-Bibliotheksfunktionen ruft — und wäre sie das, gehörte sie erlaubt. **Sie ist es nicht:**
  über 418 Dateien ruft **keine einzige** eine C-Bibliotheksfunktion, und `F05`s `exit()` meint
  den Prozessabbruch, nicht `void exit(int)`. *Null gemessener Bedarf; die Tür geht auf, wenn
  einer gemessen ist.*
