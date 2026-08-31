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
gefunden. **Diese Bahn fährt dieselbe Frage über ALLE FÜNF Stellungen und an EINEM Träger** —
einer Einheit, die alle vier Sorten Ort als Parameter führt (`k : ptr Knoten`, `r : ptr Ring`,
`w : ptr Baum`, `z : RingNr`), damit je Verfälschung genau ein Wort wechselt.
**Nullmessung: 0 Absagen.**

| Stellung | Verfälschungen | Absagen |
|---|---|---|
| `ensures` | 11 (`slots of r` · `slots of z` · `chain(…) in r` · `descendants of r` · `ancestors of r` · `queue k` · `queue z` · `elems of k` · `elems of r.kopf` · `mappings of k` · `fields of Knoten`) | **0** |
| `requires` | dieselben 11 | **0** |
| `spec fn =` | dieselben 11 | **0** |
| `invariant` an einer `table` | 3 (`mappings of Self` · `queue Self` · `elems of Self`) | **0** |
| `invariant` an einem `walk` | 3 (`slots of Self` · `descendants of Self` · `queue Self`) | **0** |

**Neununddreißig Typverfälschungen über fünf Stellungen, null Absagen.** *Die Lücke ist keine
der Stellung, sondern eine der Adresse: es gibt keinen Pass, der die Frage stellt.*

> Die elf in `ensures` sind **keine Wiederholung** der zehn aus `DOMAENENNAMEN.md` §2b,
> sondern eine zweite Messung an einem anderen Träger mit demselben Ergebnis. *Zwei Wege zu
> derselben Null sind mehr wert als einer, und der Preis ist eine Zeile.*

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

## 4. Was gebaut wurde — `D017` und `D018`

Beide sitzen in `crates/gabbro-check/src/domaene.rs` und werden aus `m1::lauf` gerufen — dort,
wo die `Umgebung` schon steht. **Dieselbe Adresse wie `D014`–`D016`**, und aus demselben
Grund: der Pass, der die Kettenkante liest, läuft ohnehin durch alle Stellungen.

| Kennung | die Frage | das Vorbild |
|---|---|---|
| **`D017`** | der **Grundname** des Orts löst auf | `M109` — dieselbe Auflösung, in den Stellungen, die `M109` nicht liest |
| **`D018`** | der Ort ist von der **Art**, die die Domäne braucht | keins — die Rechnung stand in `domaenenschranke` und wurde nie als Frage gestellt |

`D018` je Domäne, und **nur dort, wo die Zuordnung eindeutig ist**:

| Domäne | der Ort muss sein |
|---|---|
| `slots of` | eine `table` (oder ein `index into T`) |
| `queue` | ein Verbund |
| `elems of` | ein Feldarray |
| `mappings of` | ein `walk` |
| `descendants of` · `ancestors of` · `chain(a, b) in` | ein **Slot** (`<x>.slots[i]`) oder die Tabelle selbst |
| `fields of` · `threads` | **nicht gebaut** — §7 |

> **Der Slot ist eine GESTALT und kein Typ.** `c.slots[s]` hat als Typ einen gewöhnlichen
> Verbund; der Name der Tabelle, aus der er stammt, ist beim Feldzugriff verlorengegangen
> (`umgebung.rs::feld_von`). Ohne die Formfrage hätte `D018` `descendants of c.slots[s]` in
> jeder sauberen Datei abgewiesen — die Mutation `domaenenort-slot-ist-kein-slot` in §6 ist
> genau dieser Zustand, und sie reißt `jedes_beispiel_geht_sauber_durch` mit.

### 4a Die Stellungen, die der Pass betritt

`requires` · `ensures` · Rumpf einer `spec fn` · `invariant` einer `table` · **`invariant`
eines `walk`** · `invariant` einer `group` · `invariant` aller drei Schleifenformen ·
`traverse`.

Zwei davon sind neu, und beide waren nötig:

* **Die `walk`-Invariante** trägt vier der 53 Orte, darunter die zwei, die W^X über die ganze
  Seitentabelle aussprechen (`beispiele/07`). `Self` ist dort der `walk`, und der Pass bindet
  ihn — im Typwerk ist ein `walk`-Kopf ein `Verbundname`, und `walknamen` unterscheidet ihn
  vom `format`.
* **Die Träger einer `group`** werden von der `over { … }`-Zeile *erklärt*. Ohne diese Bindung
  fiel `dokumente/SYNTAX.md`:1440 — das `group`-Beispiel der Grammatik selbst — an `D017`
  über `Endpunkte`, einen Namen, den seine eigene erste Zeile einführt. *Eine Absage, die die
  Sprachdokumentation auslöst, ist eine Absage über den Pass und nicht über das Programm.*

### 4b Warum zwei eigene Kennungen und keine weitere `M109`

Nicht Geschmack, sondern die Zahl aus §1: **26 der 53 Orte heißen `Self`.** `M109` teilt sich
seine Schleife mit `M120` (*„`Self` in `ensures` names no carrier"*), und in einer
`table`-`invariant` ist `Self` genau der Träger. `M111` (*„cannot establish this
postcondition"*) hätte über einer Vorbedingung nichts zu sagen. Dieselbe Schleife eine
Klausel weiter gelegt wäre eine Regel gewesen, die 26 richtige Zeilen abweist.

---

## 5. Die Messung nach dem Bau — dieselbe Apparatur, dieselben Stellen

### 5a Die 53

```
vorher    0 von 53 melden ueber den Namen
nachher  53 von 53 melden `D017`
```

**Damit ist die Frage beantwortet, mit der diese Bahn angetreten ist:** *alle 53 tragen einen
auflösbaren Namen.* Keine Stelle bleibt übrig, weil ihr Ort für den Prüfer unauffindbar wäre —
26 mal `Self` (gebunden), 17 mal ein Tabellen- oder Walkname (über die Deklarationskarten), 10
mal ein Parameter. *Die Lücke war die Stellung und nicht der Gegenstand.*

### 5b Die Tafeln aus §2, neu gefahren

| | Verfälschungen | vorher | nachher |
|---|---|---|---|
| Grundname, je Stellung × Domäne (`probe-stellungen.gab`) | 24 | 0 | **22** |
| Typ des Orts, über alle fünf Stellungen | 39 | 0 | **36** |

Die **fünf**, die stehen bleiben, sind alle dieselbe Zelle: `fields of` — zweimal beim Namen,
dreimal beim Typ. §7 nennt den Grund.

### 5c Die Gegenrichtung: 462 Dateien, ein Treffer, und er ist ein Mangel

`gabbro pruefe` über jede `.gab` in `beispiele/` und `messung/`. **`D017` fällt in null
Dateien, `D018` in einer** — und sie ist der Fund:

```
messung/proben/probe-vier-zellen.gab:41
    traverse i over queue q      q : ptr<normal, rw> Warteschlange   -- eine TABELLE
```

Die Datei ist die Probe, mit der gemessen wurde, *ob der Prüfer die vier `UNGEDECKT`-Formen
annimmt*. Ihr eigener Kopf hält fest, dass mit einer Kostenzusage `K003` fiel: *„die Domäne
`queue` der Traversierung hat keine Schranke aus der Deklaration."*

> **Der Satz war wahr und die Diagnose falsch.** Die Schranke fehlt nicht, weil eine
> Deklaration schweigt, sondern weil dieser Ort keine Warteschlange ist.
> `arraylaenge_im_verbund` verlangt einen `Typ::Verbund` und bekam einen Tabellenzeiger —
> *ein Messgerät, das etwas anderes misst als seinen Gegenstand*, dieselbe `W16`-Gestalt wie
> an `walkschranken` und an `rsync -a` gegen `cargo`.

Die Probe trägt jetzt einen Verbund mit einem Feldarray, ihre vier `C001`-Absagen des
Erzeugers stehen unverändert daneben, und der Grund steht in der Datei. **Der Gegenstand der
Probe ist derselbe geblieben; nur ihr Träger war falsch.**

### 5d Die Giftproben

| Datei | gemessen |
|---|---|
| `beispiele/gift/425-domaenenort-gibt-es-nicht.gab` | `D017`, sonst nichts |
| `beispiele/gift/426-domaene-passt-nicht-zum-ort.gab` | `D018`, sonst nichts |
| `beispiele/gift/427-queue-ueber-einer-tabelle.gab` | `D018`, sonst nichts |

`425` trägt seine Gegenprobe in derselben Datei (`slots of Self` daneben, grün), `426`
ebenso (`elems of r.plaetze` über demselben Verbund, grün). `427` ist die Gestalt, die der
eigene Korpus geliefert hat.

---

## 6. Die Mutationsprobe — gebaut, nicht nur verankert

Vier Mutationen von Hand gesetzt, **gebaut**, mit `cargo test --no-fail-fast` gezählt und die
Quelle danach byteweise zurückgestellt (`sha256` verglichen).

| Mutation | Schaden | gefallene Proben |
|---|---|---|
| `domaenenort-nur-in-nachbedingungen` | `D017` liest wieder nur `ensures` — der Zustand von gestern | **2** |
| `domaenenort-jeder-name-geht` | jeder Name gilt als gebunden | **2** |
| `domaenenort-jeder-typ-geht` | die Domäne entscheidet nicht mehr über ihren Ort | **3** |
| `domaenenort-slot-ist-kein-slot` | die Slotgestalt zählt nicht mehr | **4** |

> **Die letzte ist die interessante, und sie fällt nach der anderen Seite.** Ohne die
> Formfrage weist `D018` `descendants of c.slots[s]` in jeder sauberen Datei ab: es fällt
> `jedes_beispiel_geht_sauber_durch`, nicht eine Giftprobe. *Eine Mutation, die den Korpus
> zerlegt statt eine Probe, misst die Gegenrichtung* — und die ist hier die teurere Hälfte.

**Und `--no-fail-fast` ist keine Zierde.** Ohne es hält der Lauf beim ersten roten Ziel an und
meldet immer genau eine Probe; die Bahn davor hat diese Falle an derselben Datei bezahlt.

---

## 7. Was ungeprüft bleibt — jede Stelle mit ihrem Grund

| Stelle | Zustand | Grund |
|---|---|---|
| der **Pfad von `fields of`** — sein Name und sein Typ | **ungeprüft** | Zwei Gründe, und der zweite allein trüge es nicht. **(a)** `fields of` trägt einen `Pfad` und keinen `Ort`; die Auflösung eines Typpfads ist `N040`s Gegenstand in `namen.rs`, nicht die dieses Passes. **(b)** *Regel A*: null Mängel im Korpus — die einzige Korpusstelle ist richtig, und der Erzeuger sagt die Domäne ohnehin namentlich ab. **Fünf der 63 Verfälschungen bleiben deshalb stehen, und alle fünf sind diese eine Zelle.** |
| `threads` | **nichts zu prüfen** | die Domäne nennt keinen Namen — Sprachentscheidung `Q3` |
| der **Grundname an einem `traverse`** | **ungeprüft von `D017`** | **Geltungsbereich, nicht Reichweite.** Eine Domäne im Rumpf kann über eine `let`-Bindung laufen, und dieser Pass trägt keinen Blockgeltungsbereich — er würde den Namen abweisen, den die Zeile darüber einführt. *Gemessen*: `traverse i over slots of zzznix` mit Kostenzusage fällt heute an **`K003`** — über die fehlende SCHRANKE, nicht über den Namen. Wieder die `W16`-Gestalt, und sie steht hier als Befund und nicht als Bauauftrag. **`D018` läuft dort sehr wohl**: ein Ort ohne auflösbaren Typ ist für ihn schlicht stumm |
| `Self` an einer Stelle, an der es **keinen Träger** nennt | **ungeprüft** | `M120` sagt den Satz für `ensures`; für eine `group`-Invariante, ein `requires` oder eine `spec fn` sagt ihn niemand. **Null Korpusstellen** — Regel A. Und `D017` schweigt über `Self` ausdrücklich: *„is not declared here" schickt den Leser los, ein Wort zu erklären, das die Sprache nicht erklären lässt* — genau die Absage, die `M120` ersetzt hat |
| ein Ort, dessen **Typ nicht auflöst** | **`D018` schweigt** | `None` heißt schweigen. Ein Ort, den der Prüfer nicht typisieren kann, ist kein Ort der falschen Art; eine Absage darüber wäre eine Absage über die eigene Unkenntnis. *Betroffen sind Summentypen, Geräteregister, `reason`-Werte und Funktionszeiger — keiner davon ist ein Domänenträger, und keiner ist gemessen* |
| ein `queue`-Verbund mit **zwei** Feldarrays | **ungeprüft** | `D018` fragt „ist es ein Verbund", nicht „hat er genau ein Feldarray". Die zweite Frage ist die des Kostenpasses: `arraylaenge_im_verbund` liefert `None`, und `K003` verlangt eine Deklaration statt zu raten. *Eine zweite Absage darüber wäre eine zweite Regel über einer Sache, und der Korpus trägt den Fall nicht* |
| eine Tabelle, an der `descendants of` läuft und die **keine `tree`** hat | **ungeprüft** | unverändert der Befund aus `DOMAENENNAMEN.md` §6e: der Erzeuger sagt `C001`, und an einer Annotation läuft er nicht. `D018` fragt nach der ART des Orts, nicht nach den Kanten der Tabelle dahinter |
| die **Rolle** der beiden `chain`-Kanten | **ungeprüft** | `DOMAENENNAMEN.md` §6b — es gibt keine Messung, die eine Reihenfolge falsch nennt |
| die **Feldnamen im Suffix** von `elems of` (`elems of r.gibtsnichtfeld`) | **ungeprüft** | `M109` steigt nur in `[index]`-Suffixe ab, nicht in `.feld`; `D017` liest den GRUNDnamen. `D018` fängt den Fall halb: löst der Feldname nicht auf, ist der Typ des ganzen Orts `Unbekannt`, und dann schweigt auch er. *Der Feldname eines Suffixes ist ein Name im TYP — eine andere Frage als die des Orts* |
| ob die geprüften Namen die **richtigen Dinge** benennen | **ungeprüft, und es bleibt so** | Gabbro hat keinen Beweiser. Ein Ort, der existiert und von der richtigen Art ist, ist deshalb nicht der Ort, den das Programm meint. *Geprüft wird die Wohlgeformtheit, und die ist die Hälfte, die eine Maschine haben kann* |

---

## 8. Was dieses Dokument NICHT sagt

1. **Nichts darüber, ob eine Quantorenstelle etwas Wahres sagt.** Die 53 Absagen von §5a sind
   53 *Verfälschungen*, die auffallen — keine 53 Aussagen, die eingelöst werden.
2. **Nichts über die Emission.** Alle Messungen stehen im Prüfer; was der Erzeuger an
   denselben Domänen namentlich absagt, führt `messung/ABSAGEFORMEN.md`.
3. **Die Zahl 53 ist der Stand vom 2026-08-31.** Sie wächst mit dem Korpus, und wer sie
   nachrechnet, zählt `beispiele/` und `messung/` neu — *eine Zahl belegt ihren Nenner, nicht
   ihre Beschriftung* (W25).
