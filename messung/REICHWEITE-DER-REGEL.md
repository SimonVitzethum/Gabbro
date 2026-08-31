# Zwei Wächter über einer Regel: **83 gegen 88**, und die Lücke sind fünf Dateien

*Gemessen am 2026-08-31 auf `ki-pc-fisch-101` (`gabbro-r2`, `gcc 13.3.0`, 16 Kerne), über
den Stand `893e53a`. Ein Durchgang über **alle** `.gab` des Baumes, ohne eine Zeile am Baum
zu ändern.*

Die Regel steht an zwei Orten und lautet an beiden gleich:

> **Jede Datei, die emittiert, muss auch übersetzen.**

`pruefe-emission.sh` Stufe 9 sagt `83 von 83`. `pruefe-grammatiktafel.py` sagt `87 von 88`.
**Beide Zahlen sind richtig** — und der Unterschied ist keine Rundung, sondern ein Glob.

---

## 1. Die Reichweite, als reine Mengenarithmetik

| | Muster | Dateien |
|---|---|---:|
| **R9** — Stufe 9 | `beispiele/*.gab` + `messung/*/*.gab` | **109** |
| **RT** — Grammatiktafel | `rglob("*.gab")` ohne `target/`, `.claude/`, `.lake/` | **431** |
| `RT \ R9` | | **322** |
| `R9 \ RT` | | **0** |

Die letzte Zeile ist die wichtigste: **Stufe 9 sieht keine Datei, die die Tafel nicht auch
sieht.** Die Reichweite ist eine echte Teilmenge, kein Überschneiden — damit ist die Frage
„welcher ist der Gegenstand, welcher die Gegenprobe" überhaupt entscheidbar (§4).

Die 322 nach Verzeichnis:

```
317  beispiele/gift/          `beispiele/*.gab` ueberspringt keinen `/`
  2  messungen/               das Verzeichnis heisst `messungen`, nicht `messung`
  2  programmlogik/beispiel/  eine dritte Wurzel, die keine Stufe kennt
  1  <Wurzel>/                `halde.gab`
```

> *Der Shell-Glob `*` überspringt keinen `/`, und darauf beruht die ganze Lücke.* Beim ersten
> Auszählen hat `fnmatch.fnmatch(d, "beispiele/*.gab")` in Python **doch** einen `/`
> übersprungen und `R9 = 426` gemeldet — die Lücke verschwand im Werkzeug, das sie messen
> sollte. **Dieselbe Klasse wie `W16`**: ein Messwerkzeug mit anderer Semantik als der
> Gegenstand misst sich selbst. Die Zahl oben steht mit `PurePosixPath(...).parts` da, nicht
> mit `fnmatch`.

## 2. Und das Emissionskriterium ist bei beiden DASSELBE

Zwei Register über einer Sache können auch am Nenner auseinandergehen, nicht nur an der
Reichweite. Hier tun sie es nicht — nachgemessen und nicht angenommen:

| Kriterium | Dateien |
|---|---:|
| Stufe 9: `gabbro emit` endet mit `0` **und** die Ausgabe ist nicht leer | **88** |
| Tafel: 0 Prüferfehler **und** 0 `C001` | **88** |
| symmetrische Differenz | **0** |

*Der Erzeuger schreibt kein C, wenn der Prüfer widerspricht* — deshalb fallen die zwei
Formulierungen zusammen. **Das ist eine Messung und keine Zusage**: schriebe `emit` eines
Tages C trotz Prüferfehler, gingen die Nenner auseinander, ohne dass ein Wächter es sagt.

## 3. Die drei Mengen

| | | Dateien |
|---|---|---:|
| **A** | emittierend **und** Stufe 9 sieht sie | **83** (54 `beispiele/` + 29 `messung/*/`) |
| **B** | emittierend **und** die Tafel sieht sie | **88** |
| **E** | emittierend, über dem ganzen Baum | **88** |

`B = E`, weil die Tafel den ganzen Baum liest. **Die Differenz `E \ A` sind fünf Dateien:**

| Datei | `cc -Werror`, `-O0`/`-O2` |
|---|---|
| `beispiele/gift/286-maintains-ohne-schreiben.gab` | grün |
| `beispiele/gift/413-format-feld-heisst-gueltig.gab` | **`error: redefinition of 'Eintrag_gueltig'`** |
| `messungen/narrow.gab` | grün |
| `messungen/tabelle.gab` | grün |
| `programmlogik/beispiel/lager.gab` | grün |

## 4. Die schärfere Frage: wie viele emittierende Dateien übersetzen NICHT?

```
Stufe 9 sieht    83 von 83 uebersetzen     faellt: --
Tafel sieht      87 von 88 uebersetzen     faellt: beispiele/gift/413-…
ganzer Baum      87 von 88 uebersetzen     faellt: beispiele/gift/413-…
```

**Die `83 von 83` sind wahr und vollständig — über 83 Dateien.** Über dem Baum ist die
Antwort `87 von 88`, und die eine ist genau die, die Stufe 9 nicht sieht. *Eine Regel, die
über einer Teilmenge hält, hält über der Teilmenge.*

## 5. Die Zahl, an der die Entscheidung hängt: **2 von 317**

Das Argument gegen eine Ausdehnung lautet: *Giftproben emittieren mit Absicht kaputtes C,
also gehören sie nicht unter eine Regel, die C fordert.* Gemessen ist es falsch — und zwar
nicht knapp:

```
Giftproben im Baum                                317
davon emittieren VOLLSTAENDIG                       2
davon weist der Pruefer oder `C001` ab            315
```

**315 von 317 kommen am C-Tor nie an.** Der Filter *„emittiert vollständig"* schließt sie
längst aus, und er tut es aus dem richtigen Grund — nicht weil sie in einem Verzeichnis
liegen, sondern weil der Prüfer sie abweist. Eine Verzeichnisregel obendrauf schlösse
zusätzlich `gift/286` aus, **das grün übersetzt**, und `gift/413`, **das die einzige
Fundstelle der Regel im ganzen Baum ist**.

> *Wenn es eine ist, ist die Antwort eine andere, als wenn es dreißig sind.* Es sind zwei,
> und eine davon ist der Befund. **Die Zahl entscheidet gegen die Verzeichnisregel.**

## 6. Was heute nur EIN Wächter hält

`beispiele/gift/413-format-feld-heisst-gueltig.gab` ist die Giftprobe zu Befund A aus
`GRAMMATIKTAFEL.md` §9.3: der Erzeuger bildet die Prüfkörperfunktion `{Format}_gueltig` und
den Feldleser `{Format}_gueltig` aus demselben Präfix, und heißt das Feld `gueltig`, stehen
zwei gleiche Definitionen da.

```
Pruefer   0 Fehler, 0 Hinweise
Erzeuger  0 `C001`
N041      greift nicht -- er haelt die Namen, die C vergeben hat, nicht die eigenen
cc        error: redefinition of 'Eintrag_gueltig'
```

**Das C-Tor ist die einzige Stelle im Baum, die etwas dazu sagt** — und heute nur das der
Grammatiktafel, deren Lauf aus einem *anderen* Grund rot ist (die vier `UNGEDECKT`-Zellen,
§4). *Ein Befund, der in einem Rot mit anderer Ursache steht, ist ein Befund, den niemand
liest.*

## 7. Was diese Messung NICHT sagt

* **Nichts über den Erzeugerfehler selbst.** `emit.rs:3369` bildet den Namen; die Heilung
  gehört zu `crates/` und nicht hierher.
* **Nichts über `cc` als Maßstab.** Gemessen mit `gcc 13.3.0`. `GRAMMATIKTAFEL.md` §7 hat
  dieselbe Menge an zwei Übersetzern gemessen; diese Messung hat das nicht wiederholt.
* **Nichts über die 315.** Dass sie nicht emittieren, heißt, dass der Prüfer sie abweist —
  *warum* er es tut und ob mit dem richtigen Code, misst `zaehle-absagen.py` und nicht diese
  Tafel.
