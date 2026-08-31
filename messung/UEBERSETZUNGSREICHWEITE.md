# Die Übersetzungsregel, ausgedehnt — und `F06` geheilt

*Bahn V, Schritt V-4 des `dokumente/PLAN-VOLLSTAENDIGKEIT.md`. Gemessen am 2026-08-31 auf
`ki-pc-fisch-101`.*

> **Die Regel, seit Stufe 9 (2026-08-20):** *jede Datei, die durch `emit` kommt, muss
> `cc -Werror` bestehen.* Sie hat eine Liste abgelöst, weil eine Liste deckt, was jemand
> eingetragen hat, und eine Regel deckt, was da ist.
>
> **Ihre Reichweite war ein Verzeichnis.** `for q in "$W"/beispiele/*.gab` — und
> `messung/fragmente/F06.gab` lag seit dem 2026-08-14 daneben, emittierte 161 Zeilen und
> wurde von `cc -Werror` zurückgewiesen. *Eine Regel, deren Gegenstand die Sprache ist und
> deren Reichweite ein Verzeichnis, misst das Verzeichnis.* **Dieselbe Bauart wie die Liste,
> die sie abgelöst hat, eine Ebene höher.**

---

## 1. Der Befund, wörtlich

```
$ gabbro emit messung/fragmente/F06.gab > f06.c        # 161 Zeilen, Ruecklaufwert 0
$ cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null f06.c
f06.c:102:15: error: comparison is always true due to limited range of data type
                     [-Werror=type-limits]
  102 |         if (w != MUSTER) {
```

Bei `-O0` **und** bei `-O2`.

Die Zeile in Gabbro:

```gabbro
traverse w of s over elems of s.worte by decreasing (lenof(s.worte) - i) touches reads s
{
    if w != MUSTER { return i * 8; }
    i += 1;
}
```

`w` ist ein Index in `[u64; STACK_WORTE]` mit `STACK_WORTE : u64 = 8192`; `MUSTER` ist
`0xdead_beef_dead_beef`.

---

## 2. Die Frage: liegt die Ursache im ERZEUGER oder im PROGRAMM?

**Gemessen, nicht gelesen.** Drei Läufe gegen den unveränderten Prüfer.

### Messung A — sagt der Prüfer etwas zu einem konstant wahren Vergleich?

`messung/proben/probe-vergleich.gab`, eine lokale Variable mit Bereichstyp:

```gabbro
let a : u64 in 0 .. 10 = 5;
if a != GROSS { return 1; }        -- GROSS = 0xdead_beef_dead_beef
```

```
probe-vergleich.gab: 3 Items, 0 Fehler, 0 Hinweise
  M1 saw 9 expressions, 0 of them without a type (100 % coverage)
```

**Null Fehler bei voller Typdeckung.** Gabbro hat keine Regel gegen einen Vergleich, den
sein eigener Bereich konstant macht — *und das erzeugte C übersetzt hier sauber*, weil beide
Seiten `uint64_t` sind. **Der Prüfer nimmt die Form an, und das ist keine Lücke, sondern der
Ausgangspunkt der nächsten Messung.**

### Messung B — was macht der Erzeuger daraus?

`emit.rs`:6412 senkte `elems of` unbedingt so ab:

```c
for (uint32_t w = 0; w < (uint32_t)(sizeof(s->worte) / sizeof(s->worte[0])); w++)
```

`uint32_t`. Die Zeile ist eine **Kopie aus dem `slots of`-Zweig** vierhundert Zeilen weiter
oben — und dort ist die Breite ENTSCHIEDEN: ein Tabellenindex füllt ein Indexwort, und der
`option`-Sonderwert sitzt bei `2^32` (`beweise/Option_Sonderwert.thy`; der Erzeuger sagt es
selbst ab, wenn `count` das Indexwort füllt). **Ein FELD trägt keine solche Entscheidung** —
seine Länge steht als `const … : u64` in der Deklaration, und `sizeof(f)/sizeof(f[0])` ist
ein `size_t`.

### Messung C — die Gegenprobe, und sie entscheidet

Dieselben 161 Zeilen C, `uint32_t` → `uint64_t` in genau dieser einen Schleife:

```
$ cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null f06-mit-uint64.c
F06 mit uint64_t: UEBERSETZT
```

> **Damit liegt die Ursache im ERZEUGER.** Ein Programm, das der Prüfer annimmt, hat eine
> Absenkung, die übersetzt — der Erzeuger hat sie nur nicht geschrieben. *Das ist eine
> `UNGEDECKT`-Zelle der anderen Art: er kennt die Form, und was er daraus macht, ist kein C.*

**Und die Warnung war die billige Hälfte des Befundes.** `(uint32_t)(sizeof(f)/sizeof(f[0]))`
**schneidet ab**: ein Feld mit mehr als `2^32` Einträgen liefe gegen eine Schranke, die nicht
seine Länge ist. *Ein Erzeuger, der verengt, was die Deklaration geweitet hat, schreibt eine
Prüfung, die nichts prüft — und im Grenzfall eine Schleife, die nicht das Feld durchläuft.*

---

## 3. Was geändert wurde

| Ort | Änderung |
|---|---|
| `crates/gabbro-check/src/emit.rs`:6412 | `elems of` bindet einen Index in ein **Feld**: `uint64_t` statt `uint32_t`, mit dem Grund daneben. **`slots of` behält `uint32_t`** — die zwei Indizes zeigen in verschiedene Dinge, und die Asymmetrie ist die Aussage |
| `crates/gabbro-check/tests/rechenwerk.rs`:756 | die Zusicherung hielt die Kopie fest (`i < (uint32_t)(sizeof(`) und machte damit aus einem Versehen eine Zusage. Jetzt `uint64_t` |
| `instrumente/mutiere-pruefer.py` | der Anker von `elems-laesst-den-letzten-aus` zieht mit. *Nebenbei ist er eindeutig geworden* — bis heute stand derselbe Text zweimal im Baum, und der Ankerprüfer meldete MEHRDEUTIG |
| `instrumente/pruefe-emission.sh` | Stufe 9 läuft jetzt über `beispiele/*.gab` **und** `messung/*/*.gab` |

---

## 4. Die Sprechprobe der Ausdehnung — in beide Richtungen

**Rot vor der Heilung, grün danach, und die Reihenfolge ist die Probe.**

```
vor  der Berichtigung:  messung/fragmente/F06.gab  UEBERSETZT NICHT
                        (comparison is always true due to limited range)
nach der Berichtigung:  71 von 71 emittierenden Dateien uebersetzen
                        (53 aus beispiele/, 18 aus messung/)
```

*Ein Wächter, der beim ersten Versuch grün ist, ohne dass jemand ihn hat fallen sehen, ist
eine Verzierung* (R11). Dieser hier ist **mit einem Befund darin angetreten**, und der Befund
war der Grund für die Ausdehnung.

Die Gegenrichtung steht schon in der Stufe: eine Datei ohne Prototyp fällt an `cc -Werror`
(`Sprechprobe: ok`).

---

## 5. Zwei Ratschen, nicht eine

`MARKE_EMIT=53` (beispiele) und `MARKE_EMIT_M=18` (messung), **getrennt gebucht**.

> Eine Summe über zwei Verzeichnissen lässt sich ausgleichen: eine Datei verlässt
> `beispiele/`, eine kommt in `messung/` dazu, und die Zahl steht still. *Genau die
> Bewegung, gegen die diese Ratsche gebaut ist.*

Die 18 sind: `F02`, `F04`, `F06`, `F07`, `F08`, `F10`, die zwei W24-Proben dieser Messung,
fünf ABI-Proben, zwei Caprock-Dateien, `grenze`, `netz`, `treiber`.

Was `C001` sagt, fällt wie zuvor aus dem Nenner — **eine Weigerung ist eine ehrliche
Antwort**, und sie steht in `messung/ABSAGEFORMEN.md`.

> **Die zwei Zahlen sind am selben Tag noch zweimal gestiegen, und jedes Mal mit einem
> Grund:** `54` durch `beispiele/53-zwei-orte.gab` (V-3, `breaking` senkt ab) und `22` durch
> die zwei Dateien aus `messung/grammatik/` und zwei weitere W24-Proben (V-2). *Der Stand,
> den der Wächter selbst nennt, ist `54 / 22` — und er nennt ihn bei jedem Lauf; die Zahlen
> hier sind die des Augenblicks, in dem die Reichweite ausgedehnt wurde.*

---

## 6. Was offen bleibt

**Der Prüfer sagt zu einem konstant wahren Vergleich nichts** (Messung A), obwohl M1
Bereichstypen trägt und die Information hat. Das ist kein Loch in der Absenkung — das C
übersetzt jetzt und rechnet, was dasteht — sondern eine **Zeremonie ohne Wirkung im
Programm**: `if w != MUSTER` ist unter der entschiedenen Indexlesart von `elems of`
(«B12», 2026-08-20) immer wahr, und `F06`s eingefrorener Ausschnitt vom 2026-08-14 war unter
der Elementlesart geschrieben.

*Die Zeile zu berichtigen hieße, einen eingefrorenen Bericht zu ändern* — dieselbe Lage wie
`F01`s `N029` und `F09`s `costs <= 4096 ops`. **Der Posten gehört dem PRÜFER und ist damit
Bahn P**; er steht in `TODO.md`.

---

## 7. Die Reichweite endete auch an einer ÜBERSETZERFAMILIE — gemessen 2026-08-31

*Abgelesen mit `./instrumente/pruefe-uebersetzerfamilie.py`, 17 s lokal.*

Die Regel heißt *„muss `cc -Werror` bestehen"*. Gemessen wurde sie mit **gcc 13.3.0** auf
`ki-pc-fisch-101` und **gcc 16.2.1** lokal — beide gaben dieselbe Antwort, und genau das
steht als Beleg gebucht. **`cc` ist auf beiden Rechnern ein `gcc`.**

> *Zwei Übersetzer derselben Familie sind ein Übersetzer mit zwei Versionsnummern.* Die
> Zusage „das erzeugte C übersetzt" hing damit an **einer** Familie, und keine Zeile sagte
> das. Dieselbe Bauart wie die Liste vor der Regel und wie das Verzeichnis vor der
> Ausdehnung — **nur ist die Grenze diesmal kein Pfad, sondern ein Werkzeug.**

### Was `clang` sagt

`clang` **gibt es**, und zwar auf beiden Rechnern: **22.1.8** lokal, **18.1.3** auf
`ki-pc-fisch-101` (Ubuntu). Er ist nie gelaufen.

Gemessen über 466 `.gab` des Baumes, dieselbe Reichweite wie Stufe 9:

```
100  emittieren            (1 davon eine umgekehrte Probe, `-- erwartet: cc`)
 81  von 99: beide Familien EINIG
  6  davon einig im NEIN   -- die sechs `messung/tor-proben/`, die Stufe 9 schon meldet
 18  Dateien, an denen sie sich UNTERSCHEIDEN
```

**Alle 18 sind dieselbe Klasse, und `clang` ist der strengere:**

```
error: unused function 'Vtd_FRR_FR_LO' [-Werror,-Wunused-function]
```

Der Erzeuger schreibt zu jedem Feld eines Bitformats einen `static inline`-Zugriff. **`gcc`
warnt in C nicht über eine ungenutzte `static inline`-Funktion, `clang` schon** — und unter
`-Werror` ist die Warnung ein Fehler. Betroffen sind acht Dateien aus `beispiele/`, drei
Fragmente, zwei aus `messung/grammatik/`, zwei aus `messung/proben/` sowie `caprock/planer`,
`netz/udp-echo` und `treiber/virtio-net`.

**Stufe 9s Grün hieß nie „das erzeugte C übersetzt".** Es hieß *„es übersetzt mit gcc"* —
und der Unterschied ist 18 von 99 Dateien, also **18 %**.

### Und die umgekehrte Probe misst dieselbe Grenze von der anderen Seite

`beispiele/gift/414-tabellenspeicher-heisst-so.gab` trägt `-- erwartet: cc`: ihr C **soll**
fallen. Beide Familien lehnen ab — sie beißt also unter beiden. *Eine Probe, die nur unter
EINER Familie beißt, misst die Familie und nicht das Erzeugnis*; hier tut sie es nicht, und
das ist gemessen statt angenommen.

### Die Buchung

`MARKE_FAMILIENUNTERSCHIED = 18` steht auf dem **gemessenen** Stand, nicht auf null — sie ist
**gezogen, nicht geheilt**, und darf nur fallen. *Sie sind Schuld, kein Erfolg* (dieselbe
Form wie `zaehle-karten.py`s 40/36). **Die Heilung gehört dem Erzeuger**
(`crates/gabbro-check/src/emit.rs`) und damit einer anderen Bahn: die Zugriffe müssten
entweder entfallen, wenn niemand sie ruft, oder eine Form tragen, die beide Familien
schweigen lässt.

Die sechs, die **beide** ablehnen, färben diesen Lauf nicht: Stufe 9 besitzt sie und meldet
sie, und ein zweites Register über einer Sache ist `W7`. Sie stehen hier mit ihrer Zahl.

### Was das NICHT sagt

Eine Ablehnung durch `clang` ist nicht ohne weiteres ein Erzeugerfehler — sie kann eine
Warnung sein, die `gcc` nicht kennt, und genau das ist sie hier. **Ob `-Wunused-function`
über einer emittierten Kopfzeile eine sinnvolle Forderung ist, entscheidet der Ordner**; die
Messung sagt nur, dass die Zusage bisher an einer Familie hing. Und gemessen sind **zwei**
Familien, nicht alle: eine dritte kann eine dritte Antwort geben. *Sie verpflichtet, sie
spricht nicht frei* (W10).
