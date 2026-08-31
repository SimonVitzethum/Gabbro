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

---

# Die Rechnung: (a), (b), (c) — gegeneinander, nicht nach Geschmack

## (a) Der Erzeuger klammert — **gebaut**

**Nutzen, gemessen:** 9 von 25 Paaren rechneten falsch, jetzt 0 von 25. Dazu ein zweiter,
unabhaengiger Nutzen: die drei `-Wparentheses`-Fehlalarme und die drei an der
Vergleichsgrenze verschwinden, und damit besteht das Erzeugnis wieder
`cc -std=c11 -Wall -Wextra -Werror` — das Kommando, das **Stufe 9 von
`pruefe-emission.sh` ueber jede emittierende Datei fuehrt.**

**Kosten, gemessen:** `cc -O2 -S`, roher Vergleich je Funktion, ueber die 16 Paare mit
unveraenderter Bedeutung — dort und nur dort ist der Unterschied reiner Text:

    16 von 16 byteidentisch          vorher gegen nachher
    16 von 16 identisch              flach_X nachher gegen klammer_X vorher
    25 von 25 identisch              flach_X gegen klammer_X, beide nachher
     9 von 25 VERSCHIEDEN            dieselben Vergleiche vorher  <- der Riegel

Die letzte Zeile ist der Riegel gegen eine leere Messung. *Der erste Lauf war eine:* die
Assemblerdatei hatte vier Zeilen, weil der Erzeuger jede Funktion `static … unused`
schreibt und `-O2` sie ohne Aufrufer wegwirft. Er meldete „0 identisch, 0 verschieden" —
**und das sah aus wie ein Ergebnis** (W17).

> **Die Klammer kostet nichts als Zeichen.** Der Assembler ist Byte fuer Byte derselbe.

## (b) Die Grammatik bekommt Stufen wie C — **verworfen, und zwar gerechnet**

**Am Korpus unsichtbar:** keine der 485 Dateien mischt ungeklammert (gemessen: `pruefe`
und `emit` byteidentisch ueber beide Bauten). (b) wuerde dort nichts bewegen.

**Und trotzdem faellt es durch, an der zweiten Grenze.** Die Bitstufen an C anzugleichen
schliesst die Falle bei `& ^ |` gegen `<< >>` — und **laesst die bei `& ^ |` gegen die
Vergleiche offen.** Wer die *ganze* Tafel angleicht, kauft Ritchies anerkannten Fehler ein
(`&` unterhalb von `==`), um eine Aehnlichkeit zu gewinnen.

    (b) halb   Bitstufen wie C          Falle an der Schiebestufe zu, an der Vergleichsgrenze OFFEN
    (b) ganz   ganze Tafel wie C        beide zu, und `a & b == c` bedeutet ab jetzt `a & (b == c)`

*Es gibt keine Fassung von (b), die beide Fallen schliesst, ohne einen Fehler zu
importieren, den C selbst bereut.* **Das ist kein Geschmack, das ist die Tafel oben.**

## (c) Der Pruefer sagt ab — **gebaut, als `M136`**

**Warum neben (a) und nicht statt dessen:** eine Klammer im Erzeugnis heilt das
*ausgelieferte* Programm. Sie heilt nicht, dass der AUTOR `a & b << c` geschrieben und
`a & (b << c)` gemeint haben kann — dann hat der Pruefer etwas ueber ein Programm bewiesen,
das niemand schreiben wollte. *Was der Leser meint, steht in keiner Klammer.*

**Warum nicht breiter:** Regel A. `M136` sagt ab, **wo der Wert gemessen wandert** — neun
Paare und drei Vergleichsformen. Wo der linke Operator mindestens so fest bindet wie der
rechte, gruppiert C wie Gabbro, und dann gibt es keinen Mangel, den man absagen koennte.
`a << b & c`, `a & b ^ c`, `a & b & c` gehen durch. **gcc ist dort breiter und schweigt
zugleich bei sechs der neun, auf die es ankommt** — es ist kein zweiter Leser fuer diese
Zusage.

**Kosten am Korpus, gemessen:** 0 von 485 Dateien. `M136` feuert auf keiner.

## Die Arbeitsteilung, in einer Zeile

    (a) macht das PROGRAMM richtig, auch dort, wo (c) schweigt.
    (c) macht den TEXT eindeutig, auch dort, wo (a) schon geheilt hat.

`beispiele/gift/436` haelt genau diese Naht: `-- erwartet: M136 allein` verlangt, dass der
Pruefer absagt **und** dass `cc -Werror` das Erzeugnis annimmt. Die zweite Haelfte ist die
Gegenprobe auf (a) — sie misst das Produkt so, wie es ausgeliefert wuerde, wenn diese eine
Regel fiele.

## Was auch nach dem Bau ungemessen bleibt

* **Der zweite Korpus.** Gemessen ist der eigene (485 Dateien). Ob ein fremdes Programm die
  Form benutzt, sagt diese Zahl nicht.
* **`clang`.** Das Warnverhalten ist an `gcc` gemessen. `-Wparentheses` ist keine Norm.
* **`wrapping` und `float`.** Der Cast-Zweig in `emit.rs` klammert seine Operanden schon
  selbst; dass er dabei nie regruppiert, ist gelesen und **nicht gelaufen**.
* **Ob ein Mensch die Falle wirklich tritt.** Der Ausdruck ist mehrdeutig zwischen zwei
  Sprachen — das ist gemessen. Dass ein Leser deshalb irrt, ist plausibel und nicht
  gemessen. *`M136` steht auf einem Argument, nicht auf einem Vorfall.*

---

**Nachtrag zur Messapparatur.** Seit `M136` steht, sagt `gabbro pruefe` ueber
`probe-vorrang-bitstufen.gab` nicht mehr `0 errors`, sondern **genau 12** — die neun Paare
und die drei Vergleichsformen. Die Tafel oben ist gegen `9721d90` gemessen und bleibt, wie
sie ist. `crates/gabbro-check/tests/vorrang.rs` verlangt jetzt *diese zwoelf und keine
andere* und emittiert danach trotzdem: der Erzeuger laeuft auf dem geparsten Baum und fragt
die Paesse nicht. **Damit misst dieselbe Datei beide Bauten** — die Reichweite von (c) und
das Erzeugnis von (a) — und `abweichungen=0` steht weiter darunter.
