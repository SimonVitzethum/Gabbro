# Was ein `check` nennt, und wer davon etwas liest

**Der W24-Vorlauf zu dem Nebenbefund aus `GIFT-GEGEN-ZUSAGE.md` §10** — dort steht seit dem
2026-08-30 der Satz *„`N021` liest die `gates`-Funktionen eines `check` nicht"* und daneben
die offene Frage, *ob das eine Lücke ist oder die richtige Grenze.* Diese Datei beantwortet
sie mit einem Lauf statt mit einer Ansicht.

Gemessen am 2026-08-31, gegen den **unveränderten** Prüfer
(`ab32267`+`9adafec`, `cargo build`, `./target/debug/gabbro pruefe`).
Die Programme stehen in `messung/tor-proben/`, eines je Frage.

## Die Gegenprobe zuerst — `gabbro pruefe` schreibt auf **stdout**

Wer `2>&1 1>/dev/null` liest, bekommt für jede der zwölf Dateien **null Bytes** und hält
jede für fehlerfrei. Gemessen, bevor irgendetwas anderes gemessen wurde:

```
  messung/tor-proben/t1-tor-schreibt.gab            -> 0 Bytes auf stderr
  messung/tor-proben/t2-tor-gibt-es-nicht.gab       -> 0 Bytes auf stderr
  …  (alle zwölf, ausnahmslos 0)
```

Der Rücklaufwert trägt das Urteil (`0` sauber, `1` Befund), der Text steht auf stdout.
*Ein Messgerät, das den falschen Kanal liest, meldet für alles dasselbe — und dasselbe ist
hier „in Ordnung".*

## Die Tafel

| Probe | was drinsteht | unveränderter Prüfer |
|---|---|---|
| `t1-tor-schreibt` | die Torfunktion **schreibt** die gemessene Grösse | `0 errors` |
| `t2-tor-gibt-es-nicht` | `gates gibt_es_nicht` | `N020` |
| `t3-tor-ist-ein-static` | `gates` nennt einen `static mut` | `N020` |
| `t4-tor-falsche-signatur` | `gates tor` an `fn tor(x : u32) -> u32` | `0 errors` |
| `t5-measures-gibt-es-nicht` | `measures gibt_es_nicht` | `0 errors` |
| `t6-gegenprobe-gibt-es-nicht` | `counterprobe … expects gibt_es_nicht` | `0 errors` |
| `t7-floor-gibt-es-nicht` | `floor gibt_es_nicht >= 1` | `N022` — über `k`, nicht über den Namen |
| `t8-can-fail-gibt-es-nicht` | `can_fail { if gibt_es_nicht >= 3 … }` | `M119` |
| `t9-check-gattert-sich-selbst` | `check c { … gates c }` | `0 errors` |
| `t10-zwei-tore-im-kreis` | `check a { gates b }` · `check b { gates a }` | `0 errors` |
| `t11-measures-verschrieben` | `beispiele/gift/155`, ein Buchstabe anders | nur `N027` — **`N021` ist weg** |
| `t12-floor-nennt-nichts` | `floor k >= 1, gibt_es_nicht >= 1` | `0 errors` |

Wörtlich, die vier Zeilen, auf die es ankommt:

```
############ messung/tor-proben/t1-tor-schreibt.gab
messung/tor-proben/t1-tor-schreibt.gab: 4 items, 0 errors, 0 hints
   [exit=0]
############ messung/tor-proben/t4-tor-falsche-signatur.gab
messung/tor-proben/t4-tor-falsche-signatur.gab: 4 items, 0 errors, 0 hints
   [exit=0]
############ messung/tor-proben/t5-measures-gibt-es-nicht.gab
messung/tor-proben/t5-measures-gibt-es-nicht.gab: 4 items, 0 errors, 0 hints
   [exit=0]
############ messung/tor-proben/t9-check-gattert-sich-selbst.gab
messung/tor-proben/t9-check-gattert-sich-selbst.gab: 3 items, 0 errors, 0 hints
   [exit=0]
```

und die Zeile, die den Riegel gegen `N020`/`N022` zeigt:

```
############ messung/tor-proben/t2-tor-gibt-es-nicht.gab
error: [N020] …:9:14: `gates gibt_es_nicht` names no declared function and no `check`
############ messung/tor-proben/t7-floor-gibt-es-nicht.gab
error: [N022] …:12:19: `k` is compared one-sidedly and no `floor` names it
```

## Die Familie: welchen Namen eines `check` löst jemand auf?

| Klausel | wird aufgelöst? | von wem | Beleg |
|---|---|---|---|
| `claim "…"` | es gibt nichts aufzulösen — ein Textliteral | — | — |
| `measures o, …` | **NEIN** | niemand | `t5` |
| `gates g, …` | ja, die **Existenz** | `N020` | `t2`, `t3` |
| — der Rumpf des Tors | **NEIN** | niemand | `t1` |
| — die Signatur des Tors | **NEIN** | niemand | `t4` |
| — Kreis über Tore | **NEIN** | niemand | `t9`, `t10` |
| `can_fail { … }` | ja | M1 (`M119`), `N027` | `t8` |
| `floor p, …` | die Namen: **NEIN**; ob `measures` genannt ist: ja | `N022` | `t7`, `t12` |
| `counterprobe … expects s` | **NEIN — und mit Grund** | `N024` prüft nur die Eindeutigkeit | `t6` |

`counterprobe` ist die einzige der sechs, deren Schweigen eine Entscheidung ist:
`SYNTAX.md` §13 hält seit dem 2026-08-19 fest, dass `expects` eine **äussere** Sonde nennt —
sie steht nicht in Gabbro, *weil sie LÄUFT*. Ein Name, der auf nichts in der Einheit zeigt,
ist dort der Normalfall und kein Mangel. Die anderen fünf schweigen ohne Entscheidung.

## Die Antwort auf die offene Frage aus §10: **die richtige Grenze — URTEIL**

`gates` nennt, **wer die `linear ghost Duty(check)` verbraucht** (`SPRACHE.md`:183,
`SYNTAX.md`:1524). Verbrauch kommt nach Erzeugung: das Tor läuft, **nachdem** die Pflicht
eingelöst ist. Damit ist eine Schreibstelle im Tor **flussabwärts** von der Messung, und
`N021` — *„der gemessene Pfad verändert seine eigene Messung"* — spricht über sie nicht.

Zwei Messungen stützen das, und keine beweist es:

* Der Erzeuger schreibt `gates` als **Kommentarzeile** in das C und sonst nirgendwohin
  (`emit.rs:2781`, ` * gates: %s`); der Rumpf von `bool pruefe_c(void)` ist genau
  `c.can_fail` (`emit.rs:2807`). *Der gemessene Pfad im Erzeugnis IST der `can_fail`-Rumpf.*
* Die beiden Tore des einzigen `check` im sauberen Korpus (`beispiele/06-annahmen.gab`)
  tragen `effects { reads kerne_gemessen }` und `effects { reads tiefe_max }` — sie **lesen**
  die gemessene Grösse. Genau das ist die Form, für die das Tor da ist: die freigegebene
  Handlung liest die Messung, die sie freigegeben hat.

**Eine Absage über schreibende Tore wäre eine Absage ohne gemessenen Mangel** und fiele an
der einen Datei, die es gibt, aus dem falschen Grund nicht. *Sie wird nicht gebaut.* Was
stattdessen gebaut wird, steht darunter — es ist die Lücke, die dieselbe Messung
aufgedeckt hat und die niemand gesucht hatte.

## Der Fund, den der Vorlauf nicht suchen sollte: `measures` schaltet `N021` und `N022` ab

`N021` und `N022` finden ihre Grösse über einen **Namensvergleich gegen `c.measures`**
(`namen.rs:1712`, `namen.rs:1744`). Steht dort ein Name, den es nicht gibt, vergleicht
sich der Vergleich mit nichts — und **beide Regeln schweigen**.

`t11` ist byteweise `beispiele/gift/155-messung-schreibt-sich-selbst.gab`, mit `measures kk`
statt `measures k`. Gemessen:

```
  beispiele/gift/155…gab   ->  N027 + N021    (2 errors)
  messung/tor-proben/t11…  ->  N027           (1 errors)
```

**Ein Buchstabe, und die Regel ist weg.** Das ist die ausbleibende Absage in ihrer
reinsten Form: die Datei sieht nicht anders aus als eine, in der nichts zu melden war.
Und `measures` ist nach `SYNTAX.md` §13 *„die Berichtszeile"* — ein Name, der nirgends
steht, beschreibt in ihr einen Zustand, den es nicht gibt.

**Gebaut wird darum `N043`** — dieselbe Klasse wie `N020` (`gates` ohne Tor), `N040`
(Typname ohne Typ) und `S007` (`on_exceeded` ohne Namen): *ein Name, hinter dem nichts
steht.*

## Die Mutation, von Hand gesetzt und nachgezählt

`measures-darf-nennen-was-es-will` macht `sichtbar.contains(&m.basis.text)` zu
`true || …`. Gebaut, und über 394 Dateien (`beispiele/`, `beispiele/gift/`,
`messung/tor-proben/`) je die Zahl der Absagen vorher und nachher gezählt. Der ganze
Unterschied:

```
  beispiele/gift/421-measures-ins-leere.gab        1  ->  0
  messung/tor-proben/t11-measures-verschrieben.gab 2  ->  1
  messung/tor-proben/t5-measures-gibt-es-nicht.gab 1  ->  0
```

**Genau EINE Giftprobe fällt** — `421`. Die zwei anderen sind die Messdateien dieses
Vorlaufs und stehen in keinem Wächterlauf. *Die Zahl steht hier, weil an diesem Tag zwei
Mutationen „genau EINE" sagten und fünf meinten.* Die Quelle ist danach byteweise
zurückgestellt (`git status` leer).

## Was ungeprüft bleibt

* **Die Signatur des Tors** (`t4`). Welche Signatur eine `Duty` verbrauchen **kann**, ist
  nicht entscheidbar, solange die `Duty` nirgends erzeugt wird — `PLAN.md` `A8`, Zeile 6,
  führt genau das als offen. Eine Absage darüber wäre eine über eine Sprache, die es
  in diesem Übersetzer noch nicht gibt.
* **Der Kreis über Tore** (`t9`, `t10`). Ein `check`, der sich selbst gattert, kann seine
  Pflicht nie einlösen; zwei, die einander gattern, ebenso wenig. Der Mangel ist gemessen
  und die Regel ist **nicht gebaut** — sie ist die nächste an dieser Stelle.
* **Die Namen in `floor`** (`t12`). Das Prädikat trägt Binder (`forall i in …`) und
  eingebaute Formen (`lenof`, `old`), und eine Namensauflösung ohne sie wäre eine falsche
  Absage. `N043` fasst darum nur `measures` an.
* Ob `N021` und `N027` nach `N043` **trennbar** werden — sie sind es nicht. `N043` macht die
  eine Umgehung unmöglich, mit der es jemand versucht hat; das Paar aus §10 steht
  unverändert.

---

# Nachtrag 2026-08-31: die zwölf Torproben erzeugten C, das nicht übersetzt

*Gemessen am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 17 GB verfügbar, 20 Kerne). Werkzeug:
der **unveränderte** Prüfer und `cc` (gcc, `-std=c11`).*

Die zwölf Dateien dieses Vorlaufs schreiben alle denselben Probenrumpf:

```gabbro
can_fail { if k >= 3 { return; } }
```

Und der Erzeuger macht daraus:

```c
bool pruefe_c(void) { if (k >= 3) { return; } }
```

**Ein `can_fail` liefert ein `bool`, und ein leeres `return` hat keinen Wert.** Gemessen je
Datei, alle drei Stufen einzeln:

| Stufe | Befund |
|---|---|
| `gabbro pruefe` | **0 Fehler** über die Zeile |
| `gabbro emit` | **kein `C001`** |
| `cc` | *»return« ohne Wert in nicht-void zurückgebender Funktion* — **6 von 12** |

Die anderen sechs emittieren gar nicht erst: ein früherer Pass (`N020`, `N022`, `N043`,
`M119`, `N027`) hält sie an. **Ihr Mangel ist derselbe und nur latent** — er tritt in dem
Augenblick auf, in dem jemand den benannten Fehler repariert.

> **Drei Stufen liefen durch, und die vierte gehört nicht zur Sprache.** Dieselbe Gestalt wie
> die vier blinden Walker, einen Ring weiter außen: der Rumpf wurde betreten, ein Zweig davon
> nicht — nur ist der Zweig hier eine ganze Konstruktion.

## Und der Ordner wusste es

`beispiele/06-annahmen.gab` trägt seit dem 2026-08-20 einen Kommentar an seinem eigenen
`can_fail`, der genau diesen Mangel benennt — *der Rumpf gab keinen Wert zurück, und im
Erzeugnis stand ein `return;` in einer `bool`-Funktion.* **Repariert wurde dieser eine
Rumpf, und keine Zeile Prüfercode.**

*Ein Kommentar, der einen Mangel benennt und hinter dem keine Regel steht, wird als Beleg
gelesen* — und elf Tage später sind zwölf neue Dateien hineingelaufen.

## Gebaut: `N044` und `N045`

| Kennung | die Frage | im C |
|---|---|---|
| **`N044`** | trägt jedes `return` des Blocks einen Wert? | `return;` in einer `bool`-Funktion — **cc-Fehler** |
| **`N045`** | endet der Block auf jedem Weg? | ein Weg erreicht die schließende Klammer — **nur eine Warnung** (`-Wreturn-type`) |

**Zwei Kennungen, weil es zwei Reparaturen sind:** `N044` nennt das `return`, das einen Wert
bekommen muss; `N045` den Weg, der ein `return` bekommen muss. Die Giftproben
`beispiele/gift/428` und `429` treffen je **allein** — die beiden Fälle sind trennbar.

> **Und der Unterschied zwischen ihnen ist gemessen:** `N044` ist ein harter `cc`-Fehler,
> `N045` ohne Schalter nur eine Warnung — `gcc` übersetzt, und der Rückgabewert ist
> unbestimmt. Erst `cc -Wall -Wextra -Werror`, wie `pruefe-emission.sh` es fährt, macht
> daraus ein Rot. *Die gefährlichere Hälfte ist die, die nur bei scharfen Warnungen
> auffällt.*

## Die achtzehn Dateien sind repariert, nicht ausgenommen

Sechs Giftproben (`154`, `155`, `156`, `158`, `187`, `421`) und die zwölf Torproben trugen
die Gestalt. **Jede einzelne war ein Mangel und keine ein Fehlalarm** — deshalb steht die
Regel und keine Ausnahmeliste. *Sechs Dateien in die seit dem 2026-08-20 leere Ausnahmeliste
zu schreiben hätte aus einer Erzeugerlücke eine grüne Zeile gemacht*, und der Grund der
Vorbahn steht damit unverändert.

Nach der Reparatur: `pruefe-emission.sh` **ALL PASS**, 100 von 100 emittierenden Dateien
übersetzen; `N044`/`N045` fallen im ganzen Korpus (462 Dateien) nur in ihren eigenen zwei
Giftproben.

## Die Mutationen, von Hand gesetzt und gebaut

| Mutation | gefallene Proben |
|---|---|
| `probenurteil-return-darf-leer-sein` | **2** |
| `probenurteil-darf-durchfallen` | **2** |

Je die Giftprobe und der Einzeltest (`eine_probe_gibt_ein_urteil_zurueck`), gezählt mit
`cargo test --no-fail-fast`; die Quelle danach byteweise zurückgestellt (`sha256` verglichen).

## Was auch danach ungeprüft bleibt

* **Der TYP des zurückgegebenen Werts.** `return 3` in einem `can_fail`-Block wird von
  `N044`/`N045` nicht abgewiesen — sie fragen, *ob* ein Wert dasteht, nicht *welcher*. Der
  Korpus trägt den Fall nicht, und M1 sieht den Block ohne Vertrag (`N027`s Grund).
* **Eine Probe, deren einziger Ausgang in einer Schleife steht.** `endet_immer` behandelt
  jede Schleife als durchfallend (`lib.rs` sagt das dort ausdrücklich), also fiele
  `can_fail { forever { … return true; } }` an `N045`. **Das ist aus dem Quelltext GELESEN
  und nicht am Korpus gemessen** — keine Datei trägt die Form, und ob die Absage dort ein
  Fehlalarm wäre, hängt an Pass 6 und nicht an dieser Zeile. *Sie steht hier, damit die
  nächste, die die Form schreibt, sie findet.*
