# Der volle Lauf, gemessen — **`100 %` über einem Wächter, der nach 2,8 Sekunden stand**

*Gemessen am 2026-09-01, lokal (`free -g`: 31 GB gesamt, 13 GB verfügbar, 20 Kerne;
`ki-pc-fisch-101` nicht angefasst). Der volle Lauf: **1390 s = 23 min 10 s**. Eine zweite Bahn
rechnete zeitweise auf demselben Rechner — die Wanduhrzahl ist damit eine obere Schranke.*

`OB1` fragte nach den **47 ausgelassenen Stellen, davon 45 in `pruefe-emission.sh` allein**:
lässt sich der schlichte Lauf so schneiden, dass er mehr sieht, ohne länger zu dauern — oder
ist `--voll` der einzige belastbare Lauf, und muss die Schlusszeile das dann schärfer sagen?

**Beides ist gemessen, und die Antwort auf die zweite Frage ist die, auf die es ankommt.**

---

## Der Befund, der alles andere ordnet

Der volle Lauf druckte:

```
== Und ihr GEGENSTAND: hoechstens 94 von 94 gefaehrlichen Stellen besucht -- 100 % ==
   Kein ungefahrener Waechter traegt eine -- der Lauf hat den ganzen
   gezaehlten Gegenstand angesehen.
```

Vier Blöcke weiter unten, **in derselben Ausgabe**:

```
! 2 Waechter haben nur die HAELFTE gemessen …
   pruefe-emission.sh   [1]  ABGESCHNITTEN in: Differenztest fragment4 -- Ruecklaufwert 1
```

`pruefe-emission.sh` trägt **45 der 94 Stellen** und lief **2,8 Sekunden**. Es starb im
vierten seiner fünfundzwanzig Durchstiche; die Stufen 9 und 10 sah es nie.

> **Das Wort `höchstens` nennt die RICHTUNG eines Irrtums und nicht seine GRÖSSE.** Hier war
> die Größe 47 von 94, und das Wort stand daneben, als wäre es eine Beruhigung. *Ein
> `100 %`, das über einem Wächter steht, der in seiner dritten Sekunde ausgestiegen ist, ist
> nicht zu freundlich — es ist im Kopf des Lesers falsch.*

`besucht` hieß bis heute **`gestartet`**. Das stand in der Erklärung darunter und nicht in
der Zahl.

## Was der volle Lauf kostet — je Wächter

| | s | Anteil |
|---|---:|---:|
| `mutiere-pruefer.py` (372 Mutationen) | **807,2** | 58 % |
| `zaehle-probenzweige.py` (43 Instrumente unter der Spur) | **322,9** | 23 % |
| `pruefe-lean-beweis.sh` | 80,1 | 6 % |
| `pruefe-beweise.sh` (15 Isabelle-Theorien) | 33,5 | 2 % |
| `pruefe-luecken.py` (15 Verdrehungen, 13 Bauten) | 26,5 | 2 % |
| `pruefe-uebersetzerfamilie.py` · `pruefe-p6-beweis.sh` · `pruefe-todo.py` · `pruefe-zahlen.py` | 71,6 | 5 % |
| **`pruefe-emission.sh`** | **2,8** | **0,2 %** |
| die übrigen 44 zusammen | ~45 | 3 % |
| **zusammen** | **1390** | |

**Zwei Wächter tragen 81 % der Zeit, und keiner von beiden ist der, um dessentwillen der
volle Lauf gefahren wird.** Der Wächter mit 48 % des Gegenstands kostet **0,2 % der Zeit** —
weil er abbricht.

*Nach der Reparatur unten läuft `pruefe-emission.sh` bis Stufe 9 und braucht dafür **32,8 s**
(gemessen, `-O0`/`-O2`/UBSan über 25 Durchstiche und 110 Übersetzungseinheiten).*

## Was der volle Lauf WIRKLICH gesehen hat — drei Dinge, die der Schnelllauf strukturell nicht sehen kann

**1. `mutiere-pruefer.py` meldet überlebende Mutationen** (`rc=1`, 807 s). Der Schnelllauf
fährt `--anker`, also reines Textzählen; **kein Schnelllauf kann eine überlebende Mutation je
sehen.**

**2. `pruefe-emission.sh` stand auf einer Buchung, die seit 22 Stunden tot war.** Der
Differenztest `fragment4` vergleicht das Zeugnis gegen einen gebuchten Text:

```
gebucht:    2 assumptions (… 2 UNCOVERED …)
bekommen:   3 assumptions (… 3 UNCOVERED …)
```

Ursache mit Datum: `c887a9d` (2026-08-31, 23:08) teilt `assume dma_kohaerent` in
`messung/fragmente/F04.gab` in **zwei** Annahmen — *„und `dma_kohaerent` waren immer zwei"*.
Die Buchung in `pruefe-emission.sh` wurde nicht mitgezogen, **und niemand sah es, weil der
volle Lauf nicht lief.** Dieselbe Klasse wie die zwei toten Anker in `pruefe-luecken.py` vom
Vorabend: *ein Anker verwittert im Tempo des Baumes, und ein Werkzeug, das nicht fährt, merkt
davon nichts.*

**3. Hinter dem Schnitt lag der nächste Schnitt.** Mit berichtigter Buchung läuft der Wächter
bis **Stufe 9** und fällt dort mit drei weiteren Befunden:

```
FUND: 60 statt 57 emittierende Dateien in beispiele/   -- die Marke gehoert nachgezogen
FUND: 45 statt 40 emittierende Dateien in messung/*/   -- die Marke gehoert nachgezogen
NEUE WURZEL EMITTIERT: halde.gab -- 1 Datei ausserhalb der fuenf gebuchten Wurzeln
```

`halde.gab` ist bis zum 2026-08-31 an einem **falschen** `L104` gefallen und hat nie
emittiert; seit dessen Reparatur (`1548879`) tut es das — aus einer Wurzel, die niemand
gebucht hat. *Die Reichweite ist lautlos zurückgeblieben, genau so, wie der Wächter es
beschreibt.* **Diese drei sind hier gemeldet und nicht geheilt:** zwei der drei Marken zählen
`beispiele/`, und dort arbeitet gerade eine zweite Bahn — eine Marke über einer bewegten
Grundgesamtheit gehört dem, der zusammenführt.

> **Ein Schnitt verdeckt nicht eine Messung, sondern eine KETTE.** Jede Reparatur legt die
> nächste frei, und die Zahl der Befunde hinter einem Schnitt ist nach unten unbeschränkt.

## Die Rechnung — lässt sich der schlichte Lauf schneiden?

Der Nenner ist **nicht verteilt**:

| | gefährliche Stellen | Anteil |
|---|---:|---:|
| `pruefe-emission.sh` | **45** | **48 %** |
| 62 in Schalenwächtern insgesamt (inkl. der 45) | 62 | 66 % |
| die übrigen 51 Instrumente zusammen | 32 | 34 % |

**Es gibt genau EINEN Hebel mit Masse, und das ist `pruefe-emission.sh`.** Alles andere ist
Rundung. Damit steht die Rechnung:

```
Schnelllauf heute                    ~220 s      zwischen 38 und 47 von 94   (40–50 %)
+ pruefe-emission.sh                 +32,8 s     zwischen 38 und 92 von 94   (40–98 %)
                                     = +15 %     obere Grenze +45, untere Grenze +0
```

**Die untere Grenze bewegt sich nicht**, weil der Wächter heute selbst abgeschnitten ist —
seine 45 Stellen wandern von *„nicht gefahren"* nach *„gefahren, aber nicht erreicht"*. In
der Einheit, in der der Bruch gerechnet wird, kauft man für 15 % Laufzeit **nichts
Sicheres.**

*Und der Grund, aus dem er in `SCHWER` steht, ist ohnehin nicht die Zeit:* es ist der ORT —
`cargo run` je Einheit, und die Rechenlast gehört auf `ki-pc-fisch-101` (`CLAUDE.md`). **Eine
Ausnahme, deren Grund die Zeit gar nicht ist, lässt sich mit einer Zeitmessung nicht
aufheben.** Regel A: kein Umbau ohne gemessenen Bedarf — und der gemessene Bedarf zeigt hier
in die andere Richtung.

**Also ist die ehrliche Antwort die zweite: `--voll` ist der einzige Lauf mit einem Anspruch
auf den ganzen Gegenstand — und selbst er hat ihn heute nicht eingelöst.**

## Was gebaut wurde: ein INTERVALL statt eines Adverbs

`abnahme.py:unsichere_stellen()` zählt, wie weit die obere Schranke danebenliegen kann. Zwei
Quellen, beide heute besetzt:

* **halb gefahren** — `SCHNELL_TEIL` gibt dem Wächter die billige Hälfte.
* **abgeschnitten** — eine `TEILMESSUNG` ist mitten im Lauf ausgestiegen.

Die Schlusszeile des Schnelllaufs sagt seitdem:

```
== Und ihr GEGENSTAND: zwischen 38 und 47 von 94 gefaehrlichen Stellen besucht -- 40 bis 50 % ==
   47 davon stehen in Waechtern, die dieser Lauf nicht gefahren hat …
   9 davon sind als *besucht* GEBUCHT, ohne dass der Lauf sie erreicht haben kann --
   `besucht` heisst hier GESTARTET:
     mutiere-pruefer.py           5 Stellen   nur `--anker` gefahren
     pruefe-englisch.py           2 Stellen   ABGESCHNITTEN -- was hinter dem Schnitt stand, lief nicht
     zaehle-probenzweige.py       2 Stellen   nur `--anker` gefahren
   **Und der Nenner ist nicht verteilt:** `pruefe-emission.sh` allein traegt 45 der 94
   Stellen (48 %).
```

**Beide Enden sind gezählt.** Die untere zieht die unsicheren Stellen GANZ ab und irrt damit
nach unten — `mutiere-pruefer.py --anker` erreicht nachweislich zwei seiner fünf, sie stehen
vor der Betriebsartweiche. Die obere zählt sie ganz mit und irrt nach oben —
`pruefe-englisch.py` erreicht nachweislich keine seiner zwei, beide stehen hinter der
Überschrift, an der es abbricht.

> *Die Wahrheit liegt zwischen zwei gezählten Zahlen statt hinter einem Adverb.*

Für denselben vollen Lauf hätte die Zeile `zwischen 47 und 94 von 94 — 50 bis 100 %` gesagt.
**Dieselben Daten, dieselbe Sekunde, und ein anderer Satz.**

### Fünf Richtungen in der Sprechprobe

| Richtung | verlangt |
|---|---|
| eine `TEILMESSUNG` nimmt ihre Stellen aus der unteren Grenze | 2 |
| ein ganz gefahrener Wächter macht KEINE Stelle unsicher | 0 |
| und der Satz trägt dann **kein** Intervall | `2 von 2` |
| mit Unsicherheit trägt er eines, **mit beiden Enden** | `zwischen 0 und 2 von 2 … 0 bis 100 %` |
| die Schlusszeile trägt es ebenfalls, in beiden Richtungen | `zwischen 47 und 94 von 94` / ohne |

Die zweite und die dritte sind die, die die Zahl ehrlich halten: *ein Satz, der immer warnt,
sagt nichts.*

## Was NICHT gebaut wurde

* **Keine Zeilenspur, die die untere Grenze festzieht.** `zaehle-probenzweige.py` führt
  bereits eine; sie könnte sagen, welche Funktion ein Lauf überhaupt betreten hat. **Heute
  wären das zwei Stellen von 94.** Regel A: der Bedarf wird gemessen, nicht vermutet.
* **Keine Zeilennummer in der Abschnittsmeldung.** `abschnitt.melde()` könnte die Quellzeile
  der letzten Überschrift nennen, und dann ließe sich je Stelle entscheiden, ob sie vor oder
  hinter dem Schnitt liegt. Für `pruefe-englisch.py` wären das heute **dieselben 2 Stellen**,
  die die grobe Regel schon abzieht; und **62 der 94 Stellen stehen in Schalenwächtern**, die
  diese Meldung gar nicht tragen. *Der Aufwand läge dort, wo die Wirkung nicht ist.*
* **`pruefe-emission.sh` bleibt in `SCHWER`.** Sein Grund ist der Ort, nicht die Zeit — siehe
  die Rechnung oben.
* **Die drei Stufe-9-Befunde sind gemeldet, nicht geheilt.** Zwei ihrer Marken zählen
  `beispiele/`, und dort arbeitet eine zweite Bahn.
