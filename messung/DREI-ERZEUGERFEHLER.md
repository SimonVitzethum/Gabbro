# Drei Erzeugerfehler, die `-Wextra` nicht sieht — der W24-Vorlauf

**Gemessen am 2026-08-31, lokal** (`free -g`: 31 GB gesamt, 17 GB verfügbar, 20 Kerne),
`gcc 16.2.1` (Arch), Binärprogramm aus `cargo build` desselben Standes, `LC_ALL=C`.

`messung/GRAMMATIKTAFEL.md` §8 hat die drei Befunde genannt und keinen entschieden. Dieses
Dokument ist der Vorlauf davor: **was schreibt der Erzeuger heute, was sagt der Übersetzer
dazu — wörtlich, und über jede emittierende Datei des Baumes, nicht über die drei.**

---

## 1. Der Lauf, und warum er über mehr als Stufe 9 geht

```bash
for q in beispiele/*.gab beispiele/gift/*.gab messung/*/*.gab \
         messungen/*.gab programmlogik/beispiel/*.gab sonden/*.gab passlogik/*.gab *.gab; do
    ./target/debug/gabbro emit "$q" > "$C" 2>/dev/null || continue
    cc -std=c11 -Wall -Wextra -O2 <SCHALTER> -c -o /dev/null "$C"
done
```

Acht Wurzeln, nicht zwei. Stufe 9 von `pruefe-emission.sh` fährt `beispiele/*.gab` und
`messung/*/*.gab`; §7 hat gezeigt, dass damit vier übersetzende Dateien außerhalb jeder
Reichweite liegen. *Ein Vorlauf, der die Reichweite des Wächters erbt, misst den Wächter.*

**83 Dateien emittieren.** Dieselbe Zahl wie §7 nach dem Merge — die zusätzlichen Wurzeln
(`sonden/`, `passlogik/`, die Wurzel selbst) tragen keine emittierende Datei bei, und das ist
ein Ergebnis und keine Auslassung.

**Ohne Zusatzschalter fallen 0 von 83.** Das Tor steht.

## 2. Was der schärfere Schalter findet: **vier Stellen, drei Dateien, ZWEI Familien**

`-Werror` verschweigt nichts, aber es hört bei der ersten Datei nicht auf zu zählen — die
Zahl unten ist trotzdem ohne `-Werror` gemessen, damit jede Fundstelle einzeln dasteht und
nicht nur die erste je Übersetzungseinheit.

```
$ cc -std=c11 -Wall -Wextra -O2 -Wconversion -c …        83 Dateien, 4 Meldungen

messung/grammatik/zahlbreiten.gab(C):84:14: warning: conversion from 'double' to 'float'
    may change value [-Wfloat-conversion]
   84 |     return x * 0.5;
      |            ~~^~~~~
messung/proben/probe-f32-literal.gab(C):35:14: warning: conversion from 'double' to 'float'
    may change value [-Wfloat-conversion]
   35 |     return x * 0.1;
      |            ~~^~~~~
messung/treiber/virtio-net.gab(C):241:24: warning: conversion from 'uint32_t' {aka 'unsigned
    int'} to 'uint16_t' {aka 'short unsigned int'} may change value [-Wconversion]
  241 |     a->slots[i].kopf = i;
      |                        ^
messung/treiber/virtio-net.gab(C):243:5: warning: conversion from 'uint32_t' {aka 'unsigned
    int'} to 'uint16_t' {aka 'short unsigned int'} may change value [-Wconversion]
  243 |     atomic_store_explicit(&AVAIL_IDX, i, memory_order_release);
      |     ^~~~~~~~~~~~~~~~~~~~~
```

```
$ cc … -Wredundant-decls -Wdouble-promotion -c …          83 Dateien, 3 Meldungen

beispiele/29-undurchsichtig.gab(C):18:10: warning: redundant redeclaration of 'pa_aus_zahl'
    [-Wredundant-decls]
   18 | uint64_t pa_aus_zahl(uint64_t z);
      |          ^~~~~~~~~~~
beispiele/29-undurchsichtig.gab(C):14:10: note: previous declaration of 'pa_aus_zahl' with
    type 'uint64_t(uint64_t)'
   14 | uint64_t pa_aus_zahl(uint64_t z) __attribute__((const));
      |          ^~~~~~~~~~~
messung/grammatik/zahlbreiten.gab(C):84:14: warning: implicit conversion from 'float' to
    'double' to match other operand of binary expression [-Wdouble-promotion]
messung/proben/probe-f32-literal.gab(C):35:14: warning: implicit conversion from 'float' to
    'double' to match other operand of binary expression [-Wdouble-promotion]
```

### Die Bauart: **einmal über achtzig Dateien, nicht achtzigmal**

Das war die Frage des Vorlaufs, und sie hat eine klare Antwort. Keine der vier Stellen ist
eine Klasse, die überall auftritt — jede hängt an **einem** Konstrukt:

| Familie | Stellen | Dateien | Konstrukt |
|---|---|---|---|
| **Ganzzahlverengung** (Fund A) | 2 | 1 | `index into T` in ein `u16`-Feld |
| **Gleitkommabreite** (Fund C) | 2 | 2 | Literal ohne Suffix neben einem `f32` |
| **Doppeldeklaration** (Fund B) | 1 | 1 | derselbe Name als `impl fn` und `extern fn` |

**Das ist die Bauart einer Absenkung, die an EINER Stelle im Erzeuger falsch ist** — nicht
die einer Regel, die über den ganzen Baum daneben greift. Eine Absage, die achtzigmal fiele,
wäre eine Aussage über die Sprache; diese hier sind Aussagen über drei Zeilen in `emit.rs`.

> **Und die zwei Gleitkommastellen tragen ZWEI Diagnosen auf derselben Zeile.**
> `-Wdouble-promotion` nennt den Hinweg (`float` → `double`, um zum anderen Operanden zu
> passen), `-Wfloat-conversion` den Rückweg (`double` → `float` bei der Rückgabe). *Derselbe
> Fehler, von beiden Seiten gesehen* — und genau das ist der Beweis, dass die Rechnung
> zwischendurch die Breite gewechselt hat.

## 3. Wie viele Dateien es wirklich betrifft — und wie viele es betreffen KÖNNTE

Die drei Konstrukte sind selten, aber nicht, weil sie schwer wären: **sie sind selten, weil
der Korpus sie selten schreibt.** Die Zahl daneben ist darum kein Maß der Gefahr.

```
`index into T` mit count <= 65536, in ein Feld geschrieben     1 Datei  (virtio-net)
Gleitkommaliteral neben einem `f32`                            2 Dateien
derselbe Name als `impl fn` UND `extern fn` in einer Einheit   1 Datei  (29-undurchsichtig)
```

*`messung/grammatik/zahlbreiten.gab` und `messung/proben/probe-f32-literal.gab` sind beide
erst am 2026-08-31 entstanden* — die eine aus der Grammatik geschrieben, die andere als
W24-Probe. **Vor diesem Tag hatte der Baum keine einzige `f32`-Rechnung**, und der Fehler war
trotzdem seit «F» da. *Was 0 Fundstellen hat, ist nicht geprüft, sondern unerreichbar.*
