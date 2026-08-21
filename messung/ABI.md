# Die ABI — eine Brücke mit Maut, und der Schlagbaum stand offen

*Gemessen und gebaut am 2026-08-21. Alle Zahlen sind auf `ki-pc-fisch-101` erhoben; jeder
Befehl steht bei seiner Zahl.*

> **Der teuerste Befund steht zuerst, weil er der schlimmste mögliche Ausgang war:** die
> Brücke war schon gebaut, sie trug, und sie **schwieg**. Ein Programm aus zwei Bibliotheken,
> das `SPEICHER` unter `GERAET` und `GERAET` unter `SPEICHER` nimmt — ein Ring, also eine
> Verklemmung — lief mit **0 Fehler, 0 Hinweise** durch. *Nicht, weil die Regel fehlte:
> `H012` ist seit dem 2026-08-19 gebaut. Sondern weil die Schnittstelle den Sperrnamen
> hinaustrug und die Deklaration nicht.*

---

## 1. Der Stand VOR dem Bau

`ABI0` und `ABI1` standen bereits: `gabbro abi` schrieb ein `.gabi`, `gabbro pruefe --with`
las es. Was fehlte, war nicht der Riegel und auch nicht die Brücke, sondern die **Maut**.

### 1.1 Ohne Brücke fällt es laut — das war schon richtig

```
$ gabbro pruefe messung/abi-proben/mischt.gab
Fehler: [K003] …:17:9: `eintragen` promises costs, but `geraet_setze` is not declared here
Fehler: [K003] …:28:9: `austragen` promises costs, but `speicher_setze` is not declared here
messung/abi-proben/mischt.gab: 7 Items, 2 Fehler, 2 Hinweise
```

### 1.2 Mit Brücke fiel es gar nicht — und das war der Befund

```
$ gabbro abi messung/abi-proben/lib-speicher.gab > /tmp/speicher.gabi
$ gabbro abi messung/abi-proben/lib-geraet.gab   > /tmp/geraet.gabi
$ gabbro pruefe --with /tmp/speicher.gabi --with /tmp/geraet.gabi messung/abi-proben/mischt.gab
messung/abi-proben/mischt.gab: 15 Items, 0 Fehler, 0 Hinweise
```

**Null Fehler auf einer Verklemmung.** Die Ursache stand im Erzeugnis:

```
$ grep -E "^lock|^pub extern" /tmp/speicher.gabi
pub extern fn speicher_setze(i : index into Eintraege, m : u32) -> bool
    effects { writes Eintraege.slots, locks SPEICHER }      ← nennt SPEICHER
    costs   <= 30 ops;
                                                            ← und erklärt es nirgends
```

`ItemArt::Lock` stand in `abi.rs` überhaupt nicht in der Liste der mitgeführten Item-Arten.
Die Kopfzeile der Datei begründete das ausdrücklich mit *„absolute Zahlen komponieren nicht"*
— das Argument stimmt, **die Schlussfolgerung war falsch.** Die Ränge wegzulassen vermied die
Kollision nicht, es machte die Sperrordnung an der Grenze *unprüfbar*.

### 1.3 Und die Wurzel lag eine Ebene tiefer, INNERHALB einer Einheit

```
$ gabbro pruefe messung/abi-proben/unbekannte-sperre.gab
messung/abi-proben/unbekannte-sperre.gab: 4 Items, 0 Fehler, 0 Hinweise
```

Diese Datei nennt an **zwei** Stellen eine Sperre `NIEDA`, die niemand deklariert — in
`effects { … locks NIEDA }` und in `locks NIEDA { … }`. Kein Pass sah hin:

* `H006` holt den Rang mit `sperren.get(name)`, bekommt `None`, prüft nichts;
* `H012` tut dasselbe mit einem stillen `continue`.

> **Das ist kein ABI-Fehler.** Es ist ein Loch in der Sperrdisziplin, das die ABI nur
> *sichtbar* macht: innerhalb einer Einheit ist ein unbekannter Sperrname ein Randfall, an
> einer Bibliotheksgrenze ist er der **Normalfall** — dort kommt jeder Name von woanders.
> *Dieselbe Klasse wie der schon gebuchte Befund „Ein unbekannter TYPNAME fällt nirgends".*

---

## 2. Der Sperrrangzyklus — und die Aussage im TODO ist zu scharf formuliert

Der Auftrag nennt als schärfsten Posten: *„Zwei Bibliotheken mit unabhängig vergebenen
Sperrrängen ergeben einen ZYKLUS, den keine von beiden allein sehen kann."*

**Gemessen stimmt die Hälfte davon, und die andere Hälfte ist präziser zu sagen:**

| | |
|---|---|
| **Zyklus in der VEREINIGUNG absoluter Ränge** | **unmöglich.** Eine Rangfunktion in die ganzen Zahlen ist eine totale Ordnung; ein Ring kann darin nicht entstehen. Solange jede Sperre einen Rang trägt und jede Nahme geprüft wird, ist die Vereinigung **sound** |
| Was stattdessen passiert | die Vereinigung wird von den Zahlen geordnet, die **zwei fremde Autoren zufällig gewählt haben**. Eine legitime Mischung kann abgewiesen werden, und es gibt keine Abhilfe ausser die Bibliothek zu ändern |
| Der Fehler, den es WIRKLICH gab | **gar keine Ränge über die Grenze** — und damit gar keine Ordnung. Das ist kein Vollständigkeits-, sondern ein **Soundness**-Loch |

> *Eine falsche Abweisung ist ein schlechter Tag; ein falsches Grün ist eine Verklemmung.*

Damit ist «ABI2» (Ordnung statt Rang) **nicht** die Voraussetzung für einen sicheren
Übergang, sondern für einen *brauchbaren*. Die Reihenfolge im TODO — „ABI2 steht vor ABI3" —
bleibt richtig, aber die Begründung verschiebt sich: es geht um Ausdrucksstärke, nicht um
Deadlockfreiheit.

---

## 3. Was gebaut wurde

### 3.1 `H016` — ein Sperrname, den keine Deklaration erklärt

Die Gegenrichtung von `H008` (*„deklariert, aber nirgends genommen"*, ein Hinweis) und die
teurere von beiden: *„genommen, aber nirgends deklariert"*, ein **Fehler**.

Geprüft werden **zwei** Stellen, und beide sind durch die Grammatik eindeutig Sperrpositionen:
`locks X` / `locks shared X` in einer Wirkungsliste, und `locks X { … }` im Rumpf.

**`requires Held(…)` wird NICHT geprüft, und das ist eine Messung, keine Bequemlichkeit.**
Die erste Fassung prüfte es und machte `instrumente/pruefe-emission.sh` rot:

```
Fehler: [H016] …/f7.gab:11:15: this `requires Held(…)` names `PHASE_ROH`, and no `lock`
                               declaration explains it
```

`PHASE_ROH` ist **keine Sperre**, sondern eine BOOTPHASE — der Zeuge eines
`linear ghost type BootPhase`, und `dokumente/FRAGMENTE.md`:1337 sagt es zwei Zeilen darüber
selbst: *„`roh` heisst: vor der MMU … und das ist eine EIGENSCHAFT DER PHASE, nicht des
Geräts."*

> **`Held(…)` trägt in diesem Ordner zwei Lesarten, und nichts unterscheidet sie:** „diese
> Sperre ist gehalten" und „wir stehen in dieser Phase". Eine Regel, die jeden Namen abweist,
> den sie nicht unter den Sperren findet, hätte die zweite Lesart als Tippfehler abgewiesen —
> *und die Regel wäre falsch gewesen, nicht das Fragment.* **Der Fall ist offen und gebucht,
> nicht geraten.**

### 3.2 `gabbro abi` trägt die `lock`-Zeile

Eine Sperre kommt mit, **weil eine exportierte Signatur sie nennt** (`von_anfang: false`), über
dieselbe Fixpunktschleife, die schon Typen und Konstanten nachzieht. Eine rein interne Sperre
bleibt drinnen.

### 3.3 `gabbro emit --with` — sonst wäre die ABI eine halbe

`pruefe --with` nahm die Bibliothek an, `emit` nicht: ein Programm aus zwei Dateien liess sich
prüfen und **nicht übersetzen**. Beide gehen jetzt über dieselbe Brücke (`split_with`,
`read_preamble`).

*Gemessen, und es ist der Grund, warum das überhaupt geht:* **ein `.gabi` durch den Erzeuger
ist genau ein C-KOPF** — `typedef`, `#define` und Prototypen, **kein einziges Objekt**. Der
Vorspann im Erzeugnis ist damit das, was er in C ohnehin wäre, und zwei Einheiten binden ohne
doppeltes Symbol.

---

## 4. Nach dem Bau

```
$ gabbro pruefe --with /tmp/speicher.gabi --with /tmp/geraet.gabi messung/abi-proben/mischt.gab
Fehler: [H012] …:50:9: this call takes `GERAET` (rank 0) while `SPEICHER` (rank 0) is held here
Fehler: [H012] …:61:9: this call takes `SPEICHER` (rank 0) while `GERAET` (rank 0) is held here
messung/abi-proben/mischt.gab: 17 Items, 2 Fehler, 0 Hinweise
```

**Zwei Richtungen, zwei Fehler.** Gleicher Rang fällt, und das ist die richtige Antwort:
zwei Sperren desselben Rangs haben keine Ordnung, also können zwei Halter sie in zwei
Richtungen nehmen.

### Und die Gegenprobe, ohne die das nichts misst (R14/W17)

`messung/abi-proben/zaehlwerk.gab` (`ZAEHLER`, rank 1) und `dienst.gab` (`AUFTRAG`, rank 0):

```
$ gabbro pruefe messung/abi-proben/zaehlwerk.gab
messung/abi-proben/zaehlwerk.gab: 6 Items, 0 Fehler, 0 Hinweise
$ gabbro pruefe --with /tmp/zaehlwerk.gabi messung/abi-proben/dienst.gab
messung/abi-proben/dienst.gab: 13 Items, 0 Fehler, 0 Hinweise
$ gabbro pruefe messung/abi-proben/dienst.gab          # OHNE Brücke
Fehler: [H016] …:23:76: this `locks` effect names `ZAEHLER`, and no `lock` declaration explains it
Fehler: [K003] …:28:9: `erledige` promises costs, but `setze_stand` is not declared here
```

**Die Ordnung `AUFTRAG < ZAEHLER` steht in keiner der beiden Dateien.** Sie entsteht erst bei
der Vereinigung, und dort wird sie nachgerechnet.

### Regel A — das Programm aus zwei Dateien läuft

```
$ gabbro emit messung/abi-proben/zaehlwerk.gab              > zaehlwerk.c
$ gabbro emit --with zaehlwerk.gabi messung/abi-proben/dienst.gab > dienst.c
$ cc -std=c11 -Werror -Wall -Wextra -O0 -o prog zaehlwerk.c dienst.c treiber.c && ./prog
4242
$ cc -std=c11 -Werror -Wall -Wextra -O2 -o prog zaehlwerk.c dienst.c treiber.c && ./prog
4242
```

Geschrieben durch die Sperre des Rufers, zurückgelesen durch die geteilte Sperre der
Bibliothek. **Gebunden und ausgeführt, in beiden Optimierungsstufen.**

---

## 5. Je Klasse: wie sie über die Grenze kommt — oder warum nicht

`gabbro abi` führt **8 von 22 Item-Arten** mit: `use`, `type`, `const`, `static`, `fn`,
`table`, `atomic` und — seit heute — `lock`.

| Pass | kommt über die Grenze? |
|---|---|
| 1 **Namen** | **ja.** Das `.gabi` ist gültiger Gabbro; derselbe Parser, derselbe Namenspass |
| 2 **D1/D2** (opaque) | **ja.** `pub opaque type` geht mit, die Modulgrenze bleibt die Wand (`D004`) |
| 3 **M1 + V1–V3** | **ja.** Bereichstypen und `count`-Konstanten werden bis zum Fixpunkt nachgezogen |
| 4 **M3** (Adressräume) | **teilweise.** Zeigerrechte stehen in der Signatur; `device` geht **nicht** mit |
| 5 **M2** (linear/ghost) | **ja**, soweit es in der Signatur steht (`consumes`, `linear`) |
| 12 **Sperren** | **ja — seit heute.** `lock … rank N` geht mit, `H006`/`H012` rechnen über der Vereinigung. *Der Rang ist absolut; siehe §2* |
| 11 **Phasen** | **nein.** `order`/`advances` sind eigene Item-Arten und werden nicht mitgeführt |
| 6 **M4/Schleifen** | **entfällt** — eine Aussage über Rümpfe, und Rümpfe überqueren die Grenze nicht |
| 7 **Paarung** | **nein.** `publishes`/`awaits` stehen in der Signatur, aber die `atomic`-Tore nur, wenn `pub` |
| 8 **effects** | **ja.** Die Wirkungsliste ist der Kern des `.gabi`; `E008` rechnet über die Hülle |
| 10 **Gruppe** | **nein.** `group … over { … }` samt Verbindungsinvarianten wird nicht mitgeführt |
| 9 **costs** | **ja.** `costs <= N ops` steht in der Signatur, `K001` rechnet beim Rufer damit |

**Was ausdrücklich NICHT mitgeht, und wo es steht:**

* **`assume`** — Absicht, und in `abi.rs` begründet: eine Bibliothek, die ihre Hardwareannahmen
  mitschickt, zwingt jedem Importeur ihre Maschine auf. Das ist «ABI4».
* **`rcu`, `group`, `order`, `device`, `state`, `reason`, `format`, `entry`, `accumulates`,
  `walk`, `boot`, `entrust`, `axiom`, `check`** — 14 Item-Arten, **ungemessen**.
* **`spec fn`** — wird in `abi.rs` ausdrücklich übersprungen. Ob eine `pub`-Signatur ihn in
  `ensures` nennen kann, ist nicht gemessen.

---

## 6. Was NICHT gelungen ist

### 6.1 Dieselbe Stille steht noch bei der RCU-Domäne

```
$ gabbro pruefe messung/abi-proben/unbekannte-domaene.gab
messung/abi-proben/unbekannte-domaene.gab: 4 Items, 0 Fehler, 0 Hinweise
```

`observes NIEDADOM { … }` mit einer Domäne, die niemand deklariert — **null Fehler.**
`H016` schliesst die Sperr-Ausprägung eines Lochs, das **allgemeiner** ist. Für `rcu`,
`entry` und `group` ist es offen, und an einer Bibliotheksgrenze hat es dieselbe Gestalt.

### 6.2 Der Korpus hat keine ABI — und das entwertet die beruhigendste Zahl

Die naheliegende Kreuzprobe ist: jedes erzeugte `.gabi` wieder durch den Prüfer schicken. Eine
Schnittstelle, die etwas nennt und nicht erklärt, fällt dann.

```
== .gabi prüft sauber: 49 ; mit Fehlern: 0 ==
```

**Diese Zahl misst fast nichts (W10):**

```
== .gabi mit Inhalt: 1 ; leer: 48 ; davon mit lock-Zeile: 0 ==
```

**48 der 49 Erzeugnisse sind LEER.** Genau ein Beispiel (`29-undurchsichtig.gab`) hat
überhaupt eine öffentliche Fläche, und **keines** trägt eine Sperre über die Grenze. *Der
Korpus prüft die ABI nicht, weil er keine hat.* Die gesamte Beweislast der Brücke liegt auf
`messung/abi-proben/` — fünf Dateien, von Hand für diesen Zweck geschrieben, und damit
genau die Sorte Beleg, die dieser Ordner sonst misstrauisch ansieht.

### 6.3 Nicht gebaut: «ABI2», «ABI3», «ABI4»

* **ABI2** (Ordnung statt Rang) — eine Sprachänderung, und §2 zeigt, dass sie **nicht**
  sicherheitskritisch ist. Sie bleibt richtig und wird billiger, seit die Ränge überhaupt
  über die Grenze gehen.
* **ABI3** (die Vereinigung ist die Vereinigung: `UNPROVED` färbt, `arch` mischt nicht) —
  nicht angefasst. Ein `gabbro zeugnis` über die MISCHUNG gibt es nicht.
* **ABI4** (`annimmt { … }`, `override` als Beweispflicht) — nicht angefasst.

### 6.4 Zwei Lesarten von `Held(…)`

§3.1: der Ordner benutzt `Held(X)` für „Sperre gehalten" **und** für „Phase betreten", und
nichts unterscheidet sie. `H016` weicht dem aus, statt es zu entscheiden. **Das ist eine
Sprachfrage, und sie ist gebucht statt geraten.**

---

## 7. Der Preis, ehrlich

`H016` fällt an **zwei** Stellen des eingefrorenen Dokumentenkorpus — `locks SCHEDS` in
`FRAGMENTE.md`:652 und `locks CAPS` in `SYNTAX.md`:764. **Keine davon ist eine Fehlmessung:**
ein Fragment ist ein AUSSCHNITT, beide nennen Sperren, die ausserhalb des Schnitts deklariert
sind. *Dieselbe Lage wie `S003` beim `progress`-Zeugen — und in einem ganzen Programm wäre es
der Fehler.* Beide sind in `crates/gabbro-check/tests/korpus.rs` benannt gebucht.
