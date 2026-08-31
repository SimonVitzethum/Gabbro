# Die Vorrangtafel: eine flache Stufe gegen viere

**Gegenstand:** `crates/gabbro-syntax/src/parse.rs`, `fn bitexpr` — eine **flache
links-assoziative Schleife** ueber alle fuenf Bitoperatoren `<< >> & ^ |`. C hat dort
**vier** Stufen: `<< >>` > `&` > `^` > `|`. Der Erzeuger (`emit.rs`, `ExprArt::Binaer`)
schreibt den Ausdruck **ohne Klammern** durch.

> **Damit bedeutet derselbe Text in Gabbro und im Erzeugnis Verschiedenes**, sobald der
> linke Operator schwaecher bindet als der rechte.

Gemessen am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 13 GB verfuegbar, 20 Kerne),
gegen den **unveraenderten** Pruefer auf `9721d90`.

## Die Messapparatur — und warum sie zwei Formen laeuft

Je Paar stehen **zwei** Funktionen in `probe-vorrang-bitstufen.gab`:

    flach_<o1>_<o2>      return a o1 b o2 c;        was der Erzeuger ausliefert
    klammer_<o1>_<o2>    return (a o1 b) o2 c;      was Gabbro MEINT

Die geklammerte Form ist kein Kommentar, sondern eine **Messung**: eine Klammer in der
Quelle wird zu `ExprArt::Klammer` und emittiert als Klammer, also rechnet das C dort
zwingend Gabbros Baum. Ein Treiber ruft beide mit `a=3 b=5 c=2` und vergleicht die
gelaufenen Werte.

**`a=3 b=5 c=2` ist gesucht und nicht geraten.** Es ist das kleinste Tripel, bei dem
*alle* strukturell verschiedenen Paare auch im **Wert** verschieden sind — ein Tripel, das
einen Unterschied auf denselben Wert abbildet, misst ihn weg. Und die drei Werte liegen im
Bereich `u32 in 0 .. 7`, damit keine Schiebeweite die Wortbreite verlaesst: sonst sagt
`M104` ab, bevor die Vorrangfrage ueberhaupt gestellt ist.

## Die Tafel — alle 25 Paare, gelaufen

`gabbro pruefe` sagt ueber die ganze Datei: **52 items, 0 errors, 0 hints.** Auch ueber
die neun, die falsch rechnen.

| Ausdruck | C gruppiert als | geliefertes C | Gabbro meint | Urteil | `-Wall -Wextra` |
|---|---|---|---|---|---|
| `a << b << c` | `(a << b) << c` | 384 | 384 | gleich | schweigt |
| `a << b >> c` | `(a << b) >> c` | 24 | 24 | gleich | schweigt |
| `a << b & c`  | `(a << b) & c`  | 0 | 0 | gleich | schweigt |
| `a << b ^ c`  | `(a << b) ^ c`  | 98 | 98 | gleich | schweigt |
| `a << b \| c` | `(a << b) \| c` | 98 | 98 | gleich | schweigt |
| `a >> b << c` | `(a >> b) << c` | 0 | 0 | gleich | schweigt |
| `a >> b >> c` | `(a >> b) >> c` | 0 | 0 | gleich | schweigt |
| `a >> b & c`  | `(a >> b) & c`  | 0 | 0 | gleich | schweigt |
| `a >> b ^ c`  | `(a >> b) ^ c`  | 2 | 2 | gleich | schweigt |
| `a >> b \| c` | `(a >> b) \| c` | 2 | 2 | gleich | schweigt |
| `a & b << c`  | `a & (b << c)`  | **0** | **4** | **VERSCHIEDEN** | **schweigt** |
| `a & b >> c`  | `a & (b >> c)`  | **1** | **0** | **VERSCHIEDEN** | **schweigt** |
| `a & b & c`   | `(a & b) & c`   | 0 | 0 | gleich | schweigt |
| `a & b ^ c`   | `(a & b) ^ c`   | 3 | 3 | gleich | **warnt** |
| `a & b \| c`  | `(a & b) \| c`  | 3 | 3 | gleich | **warnt** |
| `a ^ b << c`  | `a ^ (b << c)`  | **23** | **24** | **VERSCHIEDEN** | **schweigt** |
| `a ^ b >> c`  | `a ^ (b >> c)`  | **2** | **1** | **VERSCHIEDEN** | **schweigt** |
| `a ^ b & c`   | `a ^ (b & c)`   | **3** | **2** | **VERSCHIEDEN** | warnt |
| `a ^ b ^ c`   | `(a ^ b) ^ c`   | 4 | 4 | gleich | schweigt |
| `a ^ b \| c`  | `(a ^ b) \| c`  | 6 | 6 | gleich | **warnt** |
| `a \| b << c` | `a \| (b << c)` | **23** | **28** | **VERSCHIEDEN** | **schweigt** |
| `a \| b >> c` | `a \| (b >> c)` | **3** | **1** | **VERSCHIEDEN** | **schweigt** |
| `a \| b & c`  | `a \| (b & c)`  | **3** | **2** | **VERSCHIEDEN** | warnt |
| `a \| b ^ c`  | `a \| (b ^ c)`  | **7** | **5** | **VERSCHIEDEN** | warnt |
| `a \| b \| c` | `(a \| b) \| c` | 7 | 7 | gleich | schweigt |

    Paare gesamt                 25
    im Wert verschieden           9
    gleich                       16

**Der Nenner steht daneben, und er ist die Haelfte des Befundes.** Sechzehn Paare rechnen
in beiden Sprachen dasselbe; neun nicht. Wer nur die neun zeigt, hat eine Liste, keine
Messung.

## Das Netz hat ein Loch — und wirft ausserdem drei Fehlalarme

`cc -Wall -Wextra` (gcc, `-Wparentheses` steckt in `-Wall`) meldet **sechs** Stellen. Sie
decken sich mit den neun falschen **nicht**:

    von den 9 FALSCHEN faengt gcc      3      a ^ b & c · a | b & c · a | b ^ c
    von den 9 FALSCHEN schweigt gcc    6      alle sechs mit einem SCHIEBEN rechts
    von den 16 RICHTIGEN warnt gcc     3      a & b ^ c · a & b | c · a ^ b | c

> Die sechs, bei denen gcc schweigt, sind genau die, bei denen rechts von `& ^ |` ein
> `<<` oder `>>` steht. **Das einzige Netz ist eine Stilwarnung eines fremden
> Uebersetzers, und sein Loch liegt an der Schiebestufe.**

Die drei Fehlalarme sind **kein Schoenheitsfehler**, sondern ein zweiter, unabhaengiger
Befund: `instrumente/pruefe-emission.sh` faehrt
`cc -std=c11 -Wall -Wextra -Werror`, und **Stufe 9 verlangt, dass jede emittierende Datei
das besteht.** Ein Gabbro-Programm mit `a & b ^ c` — eine Zeile, ueber die Gabbro und C
sich **einig** sind — erzeugt heute C, das der eigene Emissionswaechter des Ordners
zurueckweist. Gemessen: `cc … -Werror` gibt `rc=1` ueber die Probe.

## Die zweite Grenze: `& ^ |` gegen die Vergleiche

Die flache Bitstufe ist nicht der einzige Ort, an dem die zwei Tafeln auseinanderlaufen.
Gabbros `cmpexpr = bitexpr [ cmp bitexpr ]` legt die **ganze** Bitstufe **unter** den
Vergleich; C legt `& ^ |` **darueber**. Gemessen mit `a=3 b=5 c=2`:

| Ausdruck | Gabbro meint | geliefertes C | Urteil | `-Wall -Wextra` |
|---|---|---|---|---|
| `a & b == c`  | `(a & b) == c` → 0 | `a & (b == c)` → 0 | gleich *bei diesem Tripel* | warnt |
| `a ^ b == c`  | `(a ^ b) == c` → 0 | `a ^ (b == c)` → 1 | **VERSCHIEDEN** | warnt |
| `a \| b == c` | `(a \| b) == c` → 0 | `a \| (b == c)` → 1 | **VERSCHIEDEN** | warnt |
| `a << b < c`  | `(a << b) < c` → 0 | `(a << b) < c` → 0 | gleich (C hat hier recht) | schweigt |

Hier warnt gcc **auf allen dreien** — das Loch liegt allein an der Schiebestufe. Aber auch
diese drei Warnungen sind unter `-Werror` ein **Uebersetzungsabbruch**, und `gabbro pruefe`
sagt ueber die Datei `6 items, 0 errors, 0 hints`.

**Und dieser Ort ist NICHT durch Klammern im Erzeugnis allein zu heilen** — er ist der
Grund, warum Gabbros Tafel hier *besser* ist als Cs. Ritchies Vorrang fuer `&` unterhalb
von `==` gilt seit Jahrzehnten als Fehler; Gabbro hat ihn nicht. **Wer Gabbro an C
angleicht, importiert ihn.**

## Was hier NICHT gemessen ist

* **Nur `u32`.** Ob eine `wrapping`-Deklaration oder ein `float`-Nachbar den Cast-Zweig in
  `emit.rs` anders klammert, steht in dieser Tafel nicht.
* **Nur `gcc`.** Ob `clang` dieselben sechs Stellen meldet, ist nicht gemessen —
  `-Wparentheses` ist keine Norm, sondern die Auslegung eines Uebersetzers.
* **Ein Tripel.** Die Tafel zeigt, *dass* neun Paare auseinanderlaufen, nicht *wie weit*.
* **`a & b == c` steht als „gleich" da, und das ist ein Zufall dieses Tripels** — die
  Strukturen sind verschieden. Bei `a=2 b=2 c=2` faellt es auseinander.
