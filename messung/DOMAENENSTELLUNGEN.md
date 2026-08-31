# Die 53 Stellen, einzeln verfälscht — und was von ihnen bleibt

*Gemessen am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 13 GB verfügbar, 20 Kerne, Swap
8 GB). Werkzeug: der **unveränderte** Prüfer `target/debug/gabbro`, gebaut aus `61b41be`.*

`messung/DOMAENENNAMEN.md` §3 hat gezählt: **`M109` liest `f.ensures` und sonst nichts**, und
das sind 7 der 60 Quantorenstellen des Korpus. Die anderen 53 stehen in einem `requires`, in
einer `invariant` oder im Rumpf einer `spec fn`, und *dort ist selbst der Grundname des Orts
ungelesen.*

**Eine Zahl über Stellen ist noch keine über Mängel.** Dieses Dokument fragt deshalb nicht
„wie viele Stellen gibt es", sondern: *an wie vielen der 53 würde eine Namensprobe überhaupt
etwas zu sagen haben — und was sagt der Prüfer heute?* Gemessen wird nicht an einem
Giftbeispiel, sondern **an jeder einzelnen der Stellen, die der Korpus wirklich trägt.**

---

## 0. Die Apparatur

Drei Riegel, und jeder hat heute schon jemanden gekostet:

1. **`gabbro pruefe` schreibt auf STDOUT.** Wer `stderr` liest, bekommt „0 Fehler" für alles.
   *Das Werkzeug dieser Bahn liest beide Leitungen und zählt die Kennungen aus der
   Vereinigung.*
2. **Der Korpus wird nicht angefasst.** Jede Verfälschung läuft an einer KOPIE im
   Kratzverzeichnis; die Quelle im Baum wird gelesen und nie geschrieben. *Ein Lauf, der in
   den Baum schreibt und hinterher zurückstellt, ist ein Lauf, dessen Abbruch den Baum
   zerlegt.*
3. **Die GRUNDLAST wird abgezogen.** Achtzehn der Stellen stehen in Giftdateien, die ohnehin
   fallen. Gezählt wird je Stelle nur, was **NEU** fällt: die Kennungsliste vor der
   Verfälschung wird von der danach abgezogen. *Sonst misst man die Datei und nicht die
   Verfälschung.*

Die Gegenprobe steht vor der ersten Messzeile, nicht daneben: dieselbe Apparatur, über
dieselben Dateien, an den **`ensures`**-Stellen gefahren.

| | Stellen | mit neuer Absage |
|---|---|---|
| `ensures` | 17 | **16** (13 × `M109`, 3 × `M109` + `M111`) |
| alles andere | **53** | **2** — und beide `D012` |

*Ohne die obere Zeile wäre die untere keine Messung, sondern ein Werkzeug, das nichts
findet.* Die eine stumme `ensures`-Stelle ist `fields of Wort` — die Domäne, deren Grundname
ein **Pfad** ist und die `sammle_namen_pred_geb` gar nicht erst betritt.

> **Und die zwei, die etwas melden, melden nicht über den Namen.** `D012` ist die Regel über
> die Prämissen an einem Ruf einer erzeugten Operation (`opsruf.rs`); sie fällt, weil der
> verfälschte Name eine Prämisse nicht mehr trifft. **Über die Auflösung des Namens sagt sie
> nichts** — die Stelle bliebe genauso stumm, stünde der Ruf zwei Zeilen weiter oben nicht.
> *Null von 53 bekommen eine Absage über den Namen.* (W25: die Zahl belegt ihren Nenner, nicht
> ihre Beschriftung — hier ist die Beschriftung „Absage über den Namen", und `D012` trägt sie
> nicht.)

---

## 1. Der Nenner, nachgerechnet

Gezählt über `beispiele/` und `messung/` (Kommentarzeilen abgezogen), **ohne** die neue Probe
dieser Bahn:

| Stellung | Träger | Stellen |
|---|---|---|
| `ensures` | `impl fn`/`fn` | 19 |
| `invariant` | `table` | 29 |
| `invariant` | `walk` | 6 |
| `invariant` | `group` | 6 |
| `requires` | `impl fn` | 7 |
| `spec fn =` | `spec fn` | 5 |
| **Summe** | | **72** |

**72 − 19 = 53.** Die Tafel in `DOMAENENNAMEN.md` §3 zählte 60 mit 7 in `ensures`; die
Differenz sind **genau die zwölf Stellen, die jene Bahn selbst angelegt hat** (neun in
`messung/proben/probe-neun-domaenen.gab`, drei in den Giftproben `422`–`424`). *Die 53 stehen
unverändert, und das ist die Probe darauf, dass beide Zählungen dieselbe Sache zählen.*

Und so verteilen sie sich:

| Domäne | Stellen unter den 53 |
|---|---|
| `slots of` | 41 |
| `mappings of` | 6 |
| `chain(a, b) in` | 2 |
| `queue` | 2 |
| `ancestors of` | 1 |
| `elems of` | 1 |
| `descendants of` · `fields of` · `threads` | **0** |

| Grundname des Orts | Stellen |
|---|---|
| `Self` | **26** (22 an einer `table`, 4 an einem `walk`) |
| ein Tabellen- oder Walkname (`Kapslots`, `Endpunkte`, `A`, `Inodebaum`, …) | 17 |
| ein Parameter (`c`, `o`, `r`, `t`, `g`, `dst`) | 10 |

> **Sechsundzwanzig der 53 nennen `Self`, und das ist der Grund, aus dem eine Ausweitung von
> `M109` hier NICHT die naheliegende Antwort ist.** `M109` teilt sich seine Schleife mit
> `M120`, und `M120` sagt: *„`Self` in `ensures` names no carrier"*. In einer
> `table`-`invariant` ist `Self` **genau der Träger** — dieselbe Schleife über die
> Invarianten gelegt hätte 26 Fehlalarme erzeugt, und `M111` (*„cannot establish this
> postcondition"*) hätte über einer Vorbedingung gar nichts zu suchen. *Die Messung sagt:
> eigene Kennung.*

---

## 2. Die Messreihe je Stellung und je Domäne

Träger: `messung/proben/probe-stellungen.gab` — dieselben neun Domänen wie
`probe-neun-domaenen.gab`, aber in `requires`, in einer `invariant` und im Rumpf einer
`spec fn`. **Nullmessung: 27 Items, 0 Fehler, 0 Hinweise.**

Je Zelle die kleinste Verfälschung: der Grundname des Orts durch `zzznix` ersetzt, alles
andere unverändert.

| Domäne | `requires` | `invariant` | `spec fn =` |
|---|---|---|---|
| `slots of` | nichts | nichts | nichts |
| `chain(a, b) in` | nichts | nichts | nichts |
| `descendants of` | nichts | nichts | nichts |
| `ancestors of` | nichts | nichts | nichts |
| `queue` | nichts | *unformulierbar* | nichts |
| `elems of` | nichts | *unformulierbar* | nichts |
| `fields of` | nichts | *unformulierbar* | nichts |
| `mappings of` | nichts | nichts | nichts |
| `threads` | — nennt keinen Namen — | — | — |

**Vierundzwanzig Verfälschungen, null Absagen** (die fünf `invariant`-Zellen tragen je einen
äußeren `slots of`-Quantor als Träger, deshalb 24 Läufe und nicht 21). Drei Zellen der
`invariant`-Spalte sind nicht ungemessen, sondern **unformulierbar**: eine `table`-`invariant`
spricht über `Self` und über andere Träger, und einen Verbund (`queue`, `elems of`) oder ein
Format (`fields of`) hat sie dort nicht zur Hand. *Das ist eine Aussage über die Sprache und
keine Lücke der Messung.*

### 2a Und derselbe Rost für den TYP des Orts

`DOMAENENNAMEN.md` §2b hat zehn Typverfälschungen in `ensures` gemessen und null Absagen
gefunden. Dieselbe Frage in den anderen vier Stellungen, an einem Träger, der alle vier
Sorten Ort als Parameter führt (`k : ptr Knoten`, `r : ptr Ring`, `w : ptr Baum`,
`z : RingNr`) — **Nullmessung 0 Absagen**:

| Stellung | Verfälschungen | Absagen |
|---|---|---|
| `requires` | 11 (`slots of r` · `slots of z` · `chain(…) in r` · `descendants of r` · `ancestors of r` · `queue k` · `queue z` · `elems of k` · `elems of r.kopf` · `mappings of k` · `fields of Knoten`) | **0** |
| `spec fn =` | dieselben 11 | **0** |
| `invariant` an einer `table` | 3 (`mappings of Self` · `queue Self` · `elems of Self`) | **0** |
| `invariant` an einem `walk` | 3 (`slots of Self` · `descendants of Self` · `queue Self`) | **0** |

**Achtundzwanzig Typverfälschungen in vier Stellungen, null Absagen** — und mit den zehn aus
`ensures` sind es **achtunddreißig**. *Die Lücke ist keine der Stellung, sondern eine der
Adresse: es gibt keinen Pass, der die Frage stellt.*

---

## 3. Die 53 einzeln — jede Stelle des Korpus, jede für sich verfälscht

Nicht an einer Probe, sondern **an den Stellen, die es wirklich gibt**: 53 Läufe, je einer
mit einem verfälschten Grundnamen, je einer gegen die Grundlast derselben Datei.

```
53 Stellen  ->  51 stumm  ·  2 melden `D012` (die Prämisse eines Rufs, nicht der Name)
                              ------
                              0 melden ueber den NAMEN
```

Die 53 verteilen sich über **35 Dateien**, davon 18 in `beispiele/gift/`. Unter den stummen
stehen tragende Invarianten des Korpus: `beispiele/01-tabelle.gab`:70 und :78,
`messung/caprock/kapraum.gab`:73 und :77, `beispiele/07-eintritt-und-boot.gab`:32 und :35 —
*W^X über die ganze Seitentabelle, und ihr Träger ist ein Name, den niemand auflöst.*

---

*Die Abschnitte 4 bis 7 stehen unter demselben Datum und nach dem Bau.*
