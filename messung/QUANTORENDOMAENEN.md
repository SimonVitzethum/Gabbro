# Drei Quantorendomänen, an Gegenständen geschrieben — und zwei tragen nicht, was sie sollen

*Gemessen am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 15–17 GB verfügbar, 20 Kerne).
Werkzeuge: der unveränderte Prüfer und Erzeuger (`target/debug/gabbro`, gebaut aus
`a86234f`), `cc (GCC) 16.2.1`, `instrumente/pruefe-grammatiktafel.py`.*

`chain(a,b) in place`, `queue place` und `threads` standen als `UNGEDECKT` in der
Grammatiktafel. Der Vollständigkeitsplan §8 hat nachgemessen, dass das **keine
Sprachentscheidung** ist, sondern eine Korpuslücke: drei Programme fehlten. Dieses Dokument
schreibt sie und sagt, **was dabei herausgekommen ist** — und der Ertrag ist bei zweien von
dreien der negative.

> **Der Auftrag lautete ausdrücklich nicht „füll die Zelle".** Eine Zelle zu füllen, weil sie
> leer ist, misst danach nur noch, dass jemand sie gefüllt hat — *Falle 80 im Kleinen*. Also:
> **erst der Gegenstand, dann die Zusicherung, dann das Programm** — und die Frage, ob die
> Domäne die Zusicherung überhaupt trägt, kam zuletzt und durfte mit *nein* beantwortet
> werden.

---

## 0. Die Messapparatur — und sie war im ersten Anlauf falsch

`gabbro pruefe` schreibt seine Fehler auf **STDOUT**, `gabbro emit` auf **STDERR**. Das erste
Prüfskript dieses Abends las für beide `stderr`. **Ergebnis: acht Verfälschungen, achtmal
„0 Fehler" — und jede einzelne davon wäre als Befund über die Sprache in dieses Dokument
gewandert.**

```
verfaelscht: c.slots[zzz]   gemessen (falsch):  0 Fehler
                            gemessen (richtig): M109 -- `zzz` in `ensures` is not declared here
```

*Klasse `W16`: ein Messgerät, das die falsche Leitung abhört.* Aufgefallen ist es an einer
Gegenprobe, die zu grün war — `tree { child gibtsnicht }` musste fallen und fiel nicht.
**Jede Zahl unten steht hinter der berichtigten Apparatur**, und jede Verfälschung ist
zusätzlich gegen eine Kontrolle gefahren, von der bekannt ist, dass sie fällt.

---

## 1. Die drei Programme

| Datei | Domäne | Gegenstand | trägt die Domäne die Zusicherung? |
|---|---|---|---|
| `beispiele/55-kindkette.gab` | `chain(erstes_kind, naechstes_geschwister) in c.slots[p]` | die Rückwärtskante eines Ableitungsbaums | **ja** — und keine andere Domäne tut es |
| `beispiele/56-auftragsring.gab` | `queue r` | ein Auftragsring, untere Treiberhälfte | **halb** |
| `beispiele/57-faedenhalt.gab` | `threads` | das Anhalten der Welt über einen IPI | **nein** |

Je Datei gemessen: `gabbro pruefe` **0 Fehler, 0 Hinweise**, `gabbro emit` **0 `C001`**,
`cc -std=c11 -Wall -Wextra -Werror` bei **`-O0` und `-O2`** angenommen. `gabbro pflichten`
trägt je Datei Pflichten (55: 1 Erhaltung + 1 Nachbedingung · 56: 3 Nachbedingungen · 57:
1 Nachbedingung + 1 Vorbedingung am Rufort).

---

## 2. `chain(a, b) in <ort>` — sie trägt, und ihre Kante ist ungeprüft

### Der Gegenstand und die Zusicherung

Ein Kappenraum hängt jedes Kind in die Geschwisterkette seines Elters ein. Die Zusage, an der
das Löschen hängt:

```gabbro
forall x in chain(erstes_kind, naechstes_geschwister) in c.slots[p] :
    c.slots[x].elter == Some(p)
```

**Keine andere Domäne sagt das.** `slots of Kappraum` läuft über alle Slots — dort ist der
Satz falsch. `descendants of c.slots[p]` läuft über den ganzen Unterbaum — dort ist er
ebenfalls falsch, denn ein Enkel nennt seinen eigenen Elter und nicht `p`. Nur die
Geschwisterkette ist die Menge, über der die Aussage stimmt.

*Der Satz steht seit jeher im Entwurf* (`dokumente/SPRACHE.md`:383, `kind_zeigt_zurueck`) —
**geschrieben hatte ihn niemand.** Er steht jetzt als `invariant` an der Tabelle, mit zwei
Ebenen Schachtelung (die äußere zählt die Elter, die innere ihre direkten Kinder).

### Der Fund: die beiden Feldnamen liest kein Pass

Verfälschungen an `beispiele/55-kindkette.gab`, je **0 Prüferfehler und 0 `C001`**:

| statt `chain(erstes_kind, naechstes_geschwister)` | was es bedeutet | Befund |
|---|---|---|
| `chain(gibtsnicht, auchnicht)` | Felder, die es nicht gibt | **nichts fällt** |
| `chain(belegt, belegt)` | ein `bool` — also gar keine Kante | **nichts fällt** |
| `chain(naechstes_geschwister, erstes_kind)` | die Kante verkehrt herum | **nichts fällt** |
| `chain(elter, elter)` | die Kante des BAUMS statt der Kette | **nichts fällt** |

Und die Kontrollen an derselben Datei, die **fallen**:

| Verfälschung | Kennung |
|---|---|
| `tree { child gibtsnicht }` | **`D006`** — *„names no field of `Kappraum`"* |
| `in c.slots[zzz]` | **`M109`** — *„`zzz` in `ensures` is not declared here"* |
| `ensures` über `Kappraum.slots` statt `c.slots` | **`M111`** — *„cannot establish this postcondition"* |

> **Die eine Domäne, die ihre Kante AM DURCHLAUF nennt, ist die eine, deren Kante niemand
> prüft.** `dokumente/SYNTAX.md`:1060 begründet den Umzug der Baumkante an die `table` genau
> damit, dass zwei Stellen verschiedene Felder nennen könnten, *„ohne dass jemand die beiden
> vergleicht"* — und nennt `chain(a, b) in` dabei als das Vorbild, das es längst konnte.
> **Auf `chain` selbst ist das Argument nie zurückgefallen.**

Der Prüfer sieht `Domaene::KetteIn { ort, .. }` an drei Stellen (`wirkungen.rs`:1164,
`m1.rs`:4048, `gruppe.rs`:527) und liest jedes Mal **nur den Ort**, nie `a` und `b`.

---

## 3. `queue <ort>` — sie sagt in einer Annotation nichts Eigenes

### Der Gegenstand und die Zusicherung

Ein Auftragsring, jeder Platz hält eine Auftragsnummer oder `LEER`. Die Zusage: **kein
Auftrag steht zweimal im Ring** — ein zweiter Eintrag lässt denselben Auftrag ein zweites Mal
laufen, nachdem der erste Lauf ihn freigegeben hat. *Ein Gebrauch nach der Freigabe, im
Kleinen.* Der Satz ist eine Aussage über PAARE von Plätzen, also braucht er zwei
geschachtelte Quantoren über der Schlange.

### Fund 1 — `kopf` und `zahl` sind für die Domäne unsichtbar

Der Satz, den man über einer Warteschlange eigentlich will, lautet *„jeder LEBENDE Eintrag
…"*. `queue r` nennt weder `kopf` noch `zahl`; es läuft über den ganzen Puffer.
**Schreibbar ist nur die Aussage über alle PLÄTZE.** `beispiele/56` hält den Unterschied
klein, indem freie Plätze `LEER` tragen — *das ist eine Eigenschaft dieses Programms und
keine der Domäne.*

### Fund 2 — `queue r` ist in einer Annotation dasselbe wie `elems of r.plaetze`

Ersetzt man in `beispiele/56` jedes `queue r` durch `elems of r.plaetze`, ist das erzeugte C
**byteidentisch** (`diff` über beide `gabbro emit`-Ausgaben) und der Prüfer sagt dasselbe.
Weiter gemessen, alles je **0 Fehler, 0 `C001`**:

| Verfälschung | was das heißen sollte | Befund |
|---|---|---|
| ein **zweites Feldarray** im Verbund | `domaene.rs::arraylaenge_im_verbund` gäbe `None`, *„zwei Arrays — nicht entscheidbar, also nicht geraten"* | **nichts fällt** |
| `queue p` über einem **Skalar** (`p : PlatzNr`) | kein Verbund, keine Schlange | **nichts fällt** |
| `queue Auftrag` über einer **Tabelle** | eine `table` ist keine Warteschlange | **nichts fällt** |
| `queue zzznix` | unbekannter Grundname | **`M109`** — fällt |

> **Die Eindeutigkeitsregel des einen Feldarrays ist eine Regel des KOSTENPASSES, nicht der
> Domäne.** Sie greift an `traverse … over queue r` unter einer Kostenzusage (`K003`); in
> `requires`/`ensures` läuft kein Kostenpass, also greift sie nirgends. *In einer Annotation
> ist `queue` heute ein Wort für `elems of` mit weniger Text — und der Zugewinn, den es
> hätte, wären die lebenden Einträge, also genau das, was es nicht sagen kann.*

---

## 4. `threads` — die Domäne ohne Ort, und kein Pass liest ihre Variable

### Zuerst: was die Sprache heute über Nebenläufigkeit sagt

`gabbro kontexte` über `beispiele/57-faedenhalt.gab`:

```
contexts: 1
halt_ipi   beispiel::faedenhalt::halt_verteiler   writes 1   nested-never
    Faden.slots
places touched: 1 · context roots with no visible body: 0 of 1
```

Das ist die eine Ausführungsumgebung, die die Einheit erklärt: **ein Eintritt, sein
Verteiler, was er anfasst, ob er verschachtelt.** Daneben stehen `lock … rank … held …
masks irqs`, `atomic … publishes/awaits` und `accumulates … per cpu N`. **Die Sprache spricht
über KONTEXTE, ORTE und SPERREN — nirgends über eine Menge von Fäden.**

### Und was `forall t in threads : …` hinzufügt

Verfälschungen an `beispiele/57`, je **0 Prüferfehler, 0 `C001`**:

| Verfälschung | Befund |
|---|---|
| `threads` durch `slots of Faden` ersetzt | **nichts ändert sich** |
| `Faden.slots[t]` durch `Faden.slots[0]` — `t` gebunden und unbenutzt | **nichts fällt** |
| den Quantor ganz weggelassen | **nichts fällt** |
| der Rumpf schreibt `.kern` statt `.zustand` | **nichts fällt** |
| zwei `forall t in threads` nebeneinander über derselben Tabelle | **nichts fällt** |

Und das ist keine Nachlässigkeit eines Passes, sondern steht dreimal wortgleich im
Quelltext: `Domaene::Threads => {}` in `wirkungen.rs`:1166, `m1.rs`:4049 und `gruppe.rs`:533.
**Eine Domäne ohne Ort hat keinen Ort, den ein Pass lesen könnte.**

Was **fällt**, fällt aus einem anderen Grund: schreibt man `Anderes.slots[t]` über einer
zweiten Tabelle, kommt **`M111`** — weil das `ensures` einen Ort nennt, den die Funktion
laut `effects` nicht schreibt. *Der Leser prüft den GRUNDNAMEN, nicht die Bindung von `t`.*

### Der Fund

> **`t` bekommt seine Bedeutung erst dadurch, dass der Leser sie hineinliest.** Die Domäne
> sagt „Fäden"; die Sprache kennt keine Fadenmenge; also indiziert `t` diejenige Tabelle, auf
> die man es zeigen lässt.

Der Erzeuger sagt genau das, und präziser als jede Absicht:

```
`threads` -- the thread set is not declared in a translation unit
```

**Jede andere Domäne hängt an einer Deklaration:**

| Domäne | ihre Deklaration |
|---|---|
| `slots of` | `table … count N` |
| `descendants of` / `ancestors of` | `tree { … }` an der Tabelle («B41b») |
| `mappings of` | `walk … levels` |
| `elems of` | die Länge im Feldtyp |
| `queue` | das einzige Feldarray des Verbunds |
| **`threads`** | **nichts** |

---

## 5. Was daraus folgt — und was hier NICHT gebaut wird

| | Posten | Zustand |
|---|---|---|
| **Q1** | **`chain(a, b)`: die beiden Feldnamen prüfen** — sie existieren, sie sind `option index into Self`, so wie `D006` es für `tree` tut | **benannt.** Ein Programm misst den Bedarf noch nicht (Regel A) — und die Bahn, der `crates/gabbro-check/src/` gehört, ist eine andere |
| **Q2** | **`queue`: Kopf und Ende sichtbar machen**, sonst ist die Domäne in einer Annotation `elems of` | **benannt.** Es ist eine Entscheidung über die SPRACHE, nicht über den Erzeuger |
| **Q3** | **`threads` an eine Deklaration hängen** — `threads over <tabelle>` oder eine Marke an der Tabelle | **benannt.** Dasselbe: eine Sprachentscheidung, und ein Gegenstand misst sie nicht |
| **Q4** | Ein **zweiter Träger** je Wort — heute hängen `chain`, `queue` und `threads` an je einer Datei (`MARKE_ALLEIN` 0 → 3) | **benannt**, siehe `EINSAME-WOERTER.md` §5c |

**Keiner der vier ist hier gebaut, und das ist Regel A und keine Bequemlichkeit.** *Eine
benannte Absage ist ein Ergebnis; ein Bau aus einem einzigen Programm heraus ist eine
Vermutung mit Quelltext.*

---

## 6. Was dieses Dokument NICHT sagt

1. **Nichts darüber, ob die Zusicherungen WAHR sind.** Gabbro hat keinen Beweiser. `gabbro
   pflichten` zählt sie als Pflichten; *eine gezählte Pflicht ist keine eingelöste.* Bricht
   man den Rumpf, ohne den genannten Ort zu wechseln, fällt nichts — das ist der Stand der
   Sprache und kein Fund dieser drei Dateien.
2. **Nichts über andere Stellungen.** `chain`, `queue` und `threads` senken als
   Quantorendomäne ab, weil eine Annotation überhaupt kein C erzeugt. Als
   **Traversierungsdomäne** sagt der Erzeuger sie namentlich ab, gemessen an
   `messung/proben/probe-vier-zellen.gab`. Seit dem 2026-08-31 druckt
   `pruefe-grammatiktafel.py` beide Adressen nebeneinander — *sonst hätten diese drei
   Programme vier gemessene Absagen hinter einer grünen Zelle verschwinden lassen.*
3. **Nichts über `state`.** Das ist die vierte Zelle, sie bleibt `UNGEDECKT`, und ihre Absage
   ist als richtig nachgemessen (Plan §8, `messung/ABSAGEFORMEN.md`).
