# Zweige, die nur die Sprechprobe je erreicht hat — **12 von 43**, und der Nenner ist die Hälfte der Antwort

*Gemessen am 2026-09-01 über `acec1df`, lokal (`free -g`: 31 GB gesamt, 13 GB verfügbar,
20 Kerne), in 5 min 30 s. Werkzeug: `instrumente/zaehle-probenzweige.py`.*

Die Frage stand als offener Posten in `OB1` und hatte kein Werkzeug:

> **Wie viele der 51 Instrumente haben einen Zweig, den nur die Sprechprobe je erreicht hat?**
> Heute unbekannt.

Bei `abnahme.py` war ein Fall nachgewiesen: der Zweig `92 von 92` — die Schlusszeile **ohne**
benannte Lücke — ist nur durch die Sprechprobe belegt. Ein echter Lauf hat ihn nie erreicht,
weil in jedem echten Lauf etwas ausgelassen ist.

> **Ein Zweig, den nur die Sprechprobe erreicht, ist nicht falsch — er ist UNBELEGT.** Die
> Probe zeigt, dass er tut, was er soll, *wenn* man ihn erreicht. Sie zeigt nicht, dass die
> Welt ihn je erreicht.

---

## Die Zahl

```
12 von 43 gemessenen Instrumenten tragen einen Zweig,      172 Anweisungszeilen
   den nur die Sprechprobe je erreicht hat
 4 davon liegen in einer Funktion, die der echte Lauf       37 Anweisungszeilen
   NIE BETRETEN hat
```

Der Nenner der **Frage** ist 52 (die 51 aus `besetzung()` plus `abnahme.py`, minus das
Werkzeug selbst). Was die Messung davon sieht, sind **43**.

| | | |
|---|---:|---|
| spurbar und gemessen | **43** | |
| Schalenwächter | 8 | `sh`; hier laufen Python-Zeilen durch eine Python-Spur |
| `pruefe-luecken.py` | 1 | teuer (`SCHWER`) — baut dreizehnmal neu |
| **davon ohne benannte Probe** | **15** | die Spur erkennt eine Probe am FUNKTIONSNAMEN |

**Die 15 sind die schärfste Einschränkung, und sie sind keine Null.** `pruefe-zahlen.py`,
`pruefe-widerruf.py`, `pruefe-todo.py`s README-Hälfte und zwölf weitere führen ihre
Sprechprobe **im Rumpf von `main`**, nicht in einer eigenen Funktion. Für sie ist die
gemessene Null eine Aussage über diese Messung und nicht über sie. *Blind bei 15 von 43 —
und bei 9 von 52 überhaupt.*

## Wie gemessen wird

Jedes Instrument läuft in einem eigenen Prozess unter `sys.settrace`. Jede ausgeführte Zeile
**seiner eigenen Datei** fällt in eine von zwei Mengen:

```
PROBE   irgendein Rahmen auf dem Aufrufkeller ist eine Probenfunktion
ECHT    keiner ist es
```

Der Zustand wird **je Rahmen beim Aufruf vererbt** — was eine Sprechprobe ruft, wie tief
auch immer, liegt auf der PROBE-Seite; dieselbe Funktion aus `main` gerufen liegt auf der
anderen. *Nach Funktion statt nach Aufrufkette zu buchen hieße, jeden Helfer als probenbelegt
zu führen, sobald eine Probe ihn einmal anfasst.*

Gezählt wird `PROBE ohne ECHT`, **abzüglich der Probenkörper selbst**. Dass eine Sprechprobe
ihre eigenen Zeilen erreicht, ist kein Befund.

## Die Tafel

| Instrument | nur Probe | davon ganze Funktion | Lauf |
|---|---:|---:|---|
| `pruefe-todo.py` | 69 | 6 | 0 |
| `pruefe-waechter.py` | 28 | 14 | 0 |
| `zaehle-c-formen.py` | 17 | — | 0 |
| `abnahme.py` | 19 | 9 | **2** |
| `pruefe-grammatiktafel.py` | 12 | — | **1** |
| `mutiere-pruefer.py --anker` | 9 | 8 | 0 |
| `zaehle-bloecke.py` | 8 | — | 0 |
| `pruefe-englisch.py` | 5 | — | **1** |
| `zaehle-gifttreffer.py` | 2 | — | 0 |
| `pruefe-kennungen.py` · `pruefe-vergabe.py` · `pruefe-zitate.py` | je 1 | — | 0 |
| die übrigen 31 | 0 | — | |

## **Es sind ZWEI Klassen, und sie zu mischen wäre der eigentliche Fehler**

### 1. Eine ganze Funktion, die der echte Lauf nie betritt — 4 Instrumente, 37 Zeilen

`abnahme.schlusssatz` ist der Fall, der die Frage ausgelöst hat, und er ist hier gemessen
wiedergefunden. Ebenso `pruefe-waechter.hauptauscheckung` und `korpus_ort`, die
`mutiere-pruefer.emissionseinheiten` und zwei Funktionen in `pruefe-todo.py`.

**Dort ist die Probe der einzige Aufrufer, den es je gab.** Nicht „heute nicht gefeuert",
sondern *es gibt keinen Weg dorthin, den ein Lauf dieses Baumes nimmt.*

### 2. Ein Zweig in einer Funktion, die der Lauf betritt — der Rest, 135 Zeilen

Fast immer der **Befundweg eines Wächters, der heute nichts findet**: `pruefe-todo.pruefe()`
läuft, und seine sechs `befunde.append(...)`-Zweige feuern nur auf den erfundenen
`TODO.md`-Vorlagen der Sprechprobe. *Erreichbar und unbelegt* — und belegt in der Sekunde,
in der jemand die echte Datei bricht.

> **Beide sind unbelegt. Nur die erste sagt, dass nichts außer der Fixtur dorthin kommt.**

Eine dritte Form steht daneben und ist eine eigene Beobachtung: `pruefe-kennungen.py`,
`pruefe-vergabe.py` und `pruefe-zitate.py` tragen je **einen** Parameter (`zusatz`), der
einzig dazu da ist, dass die Sprechprobe eine vergiftete Zeile in den echten Scanner
einschleusen kann. *Ein Argument, das nur die Probe belegt* — die kleinste und sauberste
Instanz der Klasse.

## Was diese Messung NICHT sieht

*Der Nenner steht vor dem Zähler.*

1. **Schalenwächter** — acht, und für sie ist die Zahl **keine Null, sondern kein Wert**.
2. **Wer keine Probenfunktion mit Namen hat** — fünfzehn.
3. **Die Teuren** — `pruefe-luecken.py` läuft nicht; `mutiere-pruefer.py` nur mit `--anker`.
4. **ANWEISUNGEN, nicht Zweige.** Ein `if` ohne `else`, dessen Bedingung nie greift, hat
   keine Zeile, die fehlen könnte.
5. **EIN Lauf, EIN Satz Argumente.** Eine Zeile, die nur `--voll` erreicht, steht nicht in
   ECHT — berührt die Probe sie, fällt sie hier auf. *Überschätzung in die sichere Richtung.*
6. **Den Zustand des Baumes am Messtag** — und das ist nicht theoretisch, es hat sich
   innerhalb einer Stunde bewegt. Beim ersten Lauf endeten **sechs** der 43 selbst nicht mit
   0, beim letzten nur noch **drei** (`abnahme.py`, `pruefe-grammatiktafel.py`,
   `zaehle-lean.py`), weil `pruefe-abstieg.py`, `pruefe-englisch.py` und `pruefe-zahlen.py`
   inzwischen grün sind. Ein rot endender Wächter erreicht sein grünes Ende nicht, und dessen
   Zeilen sehen darum probenbelegt aus. **`abnahme.py`s 19 Zeilen sind genau davon
   betroffen:** wäre der Lauf grün gewesen, wäre nur der Zweig `92 von 92` übrig geblieben
   und nicht auch der mit der Lücke. *Die Tafel druckt jeden Rücklaufwert daneben, damit das
   nicht verschwindet.*
7. **Sich selbst.** Das Werkzeug fährt die anderen. Dieselbe Klasse wie das `pgrep -f`, das
   sich in `CLAUDE.md` selbst gefunden hat.

**Und die Richtung der Vergröberung geht in beide:** eine Zeile, die BEIDE Mengen trifft,
fällt heraus — der Zähler ist damit eine untere Schranke für das, was die Probe allein trägt;
die Punkte 5 und 6 heben ihn nach oben.

## Der Befund über das Werkzeug selbst — zweimal, und beide vor dem ersten Ergebnis

**Erstens: die Sprechprobe hat es gefangen.** Die schärfere Klasse kam anfangs über den
ganzen Baum leer heraus. Grund: die Spanne einer Funktion begann bei der `def`-Zeile, und
die läuft in **jedem** Lauf, weil sie die Funktion *definiert*. Damit galt jede Funktion als
betreten. *Eine Regel, die die Definition mitzählt, zählt das Einlesen der Datei.*

**Zweitens: es hat sich selbst gefahren.** `zaehle-probenzweige.py` heißt `zaehle-*`, steht
damit in `besetzung()`, und `abnahme.py` gehört zu seinem Gegenstand — nach elf Minuten
standen **drei geschachtelte Ebenen** nebeneinander. Es steht seither in
`pruefe-waechter.SCHWER` mit genau diesem Grund und in `abnahme.SCHNELL_TEIL` mit `--anker`.

> *Ein Werkzeug, dessen Gegenstand seinen eigenen Aufrufer enthält, hat keinen Fixpunkt* —
> und `SCHWER` ist die Stelle, an der das aufgeschrieben wird.


## Nachtrag derselben Stunde: **167 → 172, und die fünf sind meine**

`abnahme.py` druckt seit derselben Sitzung ein **Intervall** statt `hoechstens`
(`messung/ABNAHME-STELLEN.md`). Die zwei Funktionen, die dafür entstanden sind — `spanne()`
und `unsichere_stellen()` —, brachten **fünf Zeilen mit, die heute nur die Sprechprobe
erreicht**: dieser Baum lässt die Abnahme mit `2` enden, und sie kommt an ihr eigenes grünes
Ende nicht.

> **Das Werkzeug, das die Klasse zählt, hat den Code erwischt, der in derselben Stunde
> danebengeschrieben wurde.** Genau dafür steht eine Ratsche über der eigenen Werkstatt.

Die Zahl der TRÄGER bewegte sich nicht: `abnahme.py` war schon einer der zwölf. *Ein Zähler
über Instrumenten sagt nichts darüber, wie viel jeder einzelne trägt* — deshalb führt die
Ratsche beide Zahlen.
