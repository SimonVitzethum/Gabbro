# Zweige, die nur die Sprechprobe je erreicht hat — **14 von 43**, und der Nenner ist die Hälfte der Antwort

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

---

# Nachtrag 2026-09-01, zweite Lesung: **das blinde Loch fällt von 15 auf 6, und zwei der Neun tragen wirklich**

*Gemessen lokal (`free -g`: 31 GB gesamt, 14 verfügbar, 20 Kerne), voller Lauf über 43
Instrumente. Die Zahl steigt — und der Anstieg ist eine **Korrektur**, kein Rückschritt:*

```
                    erste Lesung        zweite Lesung
blind (keine Probe, die die Spur sieht)   15 von 43      6 von 43
Traeger                                   12             14
Anweisungszeilen                         172            189
```

## Was gebaut wurde, und warum nicht das andere

Die erste Lesung nannte die schärfste Einschränkung selbst: *die Spur erkennt eine Probe am
FUNKTIONSNAMEN, und 15 von 43 fahren ihre im Rumpf von `main`.* Zwei Wege standen offen.

| | Kosten | Risiko |
|---|---|---|
| die Probe in eine benannte Funktion **heben** | 15 Umbauten an tragendem Code, je mit Parametern aus dem Rumpf von `main` | ein gebrochener Wächter — *um eine Messung zu ermöglichen* |
| ein **Markenpaar** `# speech_test: begin/end` | 2 Kommentarzeilen je Datei | keines: ein Kommentar ändert kein Verhalten |

**Regel A: die billigere Apparatur zuerst, und der Gegenstand bleibt unberührt.** Innerhalb
der Spanne wird der Zustand ZEILENweise statt rahmenweise gesetzt; was von dort gerufen
wird, erbt ihn genau wie aus einer benannten Funktion. Die markierten Zeilen selbst werden
wie ein Probenkörper abgezogen.

Zwei neue Richtungen in der Sprechprobe halten das ehrlich (jetzt **acht**): eine markierte
Probe muss **denselben** Zweig finden wie eine benannte, und ein `begin` ohne `end` wird
**abgelehnt** statt als leere Spanne gelesen — *eine offene Marke verschlänge sonst den Rest
der Datei auf die Probenseite, und der Zähler stiege über nichts.*

## Die Antwort auf die eigentliche Frage: **2 von 9**

Neun der 15 haben einen markierbaren Probenblock bekommen. Davon tragen **zwei** wirklich
einen probenexklusiven Zweig:

| markiert | nur Probe | was |
|---|---:|---|
| `pruefe-zahlen.py` | **15** | 8 davon die ganze Funktion `lauf()` — siehe die dritte Form unten |
| `pruefe-widerruf.py` | **2** | der Aufzeichnungsweg eines Befundes |
| `pruefe-gruende` · `-reichweite` · `-schablonen` · `-wortschatz` · `zaehle-fragmente` · `-netz` · `-zeremonie` | 0 | |

*Die 15 waren 14, bis `pruefe-zahlen.py` grün wurde:* der Wächter fand eine Zahl in
`TODO.md`, die diese Bahn zwei Minuten vorher durch das Schreiben zweier Dateien ungültig
gemacht hatte. Repariert erreicht er sein grünes Ende — **und dieses Ende ist eine weitere
Zeile, an die nur die Probe kommt.** *Ein Wächter, der grün wird, HEBT diese Zahl* (Punkt 6),
und eine Marke ohne diesen Satz daneben liest sich wie ein Rückschritt.

**Für sieben der neun war die gemessene Null gerechtfertigt** — und das ist ein Ergebnis,
kein Nullbefund. Bei `pruefe-widerruf.py` sind es die zwei Zeilen, die einen lebenden
Widerruf aufzeichnen: **jeder widerrufene Satz im Baum ist heute durchgestrichen**, also
erreicht nur die vergiftete Kopie der Sprechprobe `treffer.append`. *Erreichbar, unbelegt,
und belegt in der Sekunde, in der jemand einen Widerruf lebend hinschreibt.*

## Eine DRITTE Form, und sie ist die interessanteste

`pruefe-zahlen.lauf()` — die Funktion, die jeden bewachten Befehl mit Frist fährt, den
Selbstbezugsriegel hält und die `MISCHUNG`-Aussetzung bucht — wird in diesem Lauf **nur aus
der Sprechprobe heraus betreten.** Nicht, weil es keinen anderen Weg gäbe:

```
Sprechprobe:  pruefe_eintraege(verstellen=nr)  fuer jeden Eintrag   ->  fuellt den Cache
danach:       pruefe_eintraege()                                    ->  LIEST den Cache
```

> **Die Fixtur war zuerst da.** Die Zeile ist nicht unerreichbar — sie ist schon abgearbeitet,
> wenn der echte Durchgang kommt. Gebucht wird sie trotzdem, weil der Lauf es so getan hat;
> hier steht sie, weil *„nichts außer der Fixtur kommt dorthin"* genau das ist, was sie
> **nicht** zeigt.

Damit sind es drei Formen, nicht zwei: eine Funktion ohne Weg dorthin · ein Befundweg, den
heute nichts auslöst · **und eine, der die Probe zuvorkommt.**

## Die sechs, die blind bleiben — drei Klassen, keine Restmenge

* **Hinter einer Betriebsartweiche**: `zaehle-pflichten.py` (`--spalten`, `--haengend`),
  `zaehle-bereichspflichten.py` (`--selbstprobe`). Der gespurte Lauf nimmt sie nicht. *Sie zu
  markieren hieße, die Blindheit zu verstecken statt sie aufzuheben.*
* **Kein Fixturblock, weil es keinen geben kann**: bei `pruefe-notation.py` ist der ganze
  Gegenstand erfundener Text, den der echte Prüfer frisst; bei
  `pruefe-uebersetzerfamilie.py` ist die „Sprechprobe" eine Vorbedingung an die Umgebung
  (*zwei Übersetzer derselben Familie sind einer*).
* **Gar keine Sprechprobe**: `zaehle-b3.py` darf das (`pruefe-waechter.ZAEHLER`).
  **`zaehle-empfindlichkeit.py` nicht** — und es besteht die Pflicht trotzdem.

### Der Befund über den Wächter: **`HAT_PROBE` lässt sich mit dem Wort bezahlen**

`pruefe-waechter.py` verlangt von jedem Nicht-Zähler eine Sprechprobe und prüft das mit
`HAT_PROBE = /[Ss]prechprobe|speech test|Gegenprobe|[Ss]elbsttest/` **über den ganzen
Dateitext.** In `zaehle-empfindlichkeit.py` steht das Wort in einem **gedruckten Satz über
den Gegenstand**:

```
print("   fuer sie ist die Uebersetzungsprobe die einzige Gegenprobe. Faellt die eine")
```

Eine Sprechprobe hat die Datei nicht. **Gemeldet, nicht geheilt:** eine schärfere Textregel
(nur Code, nicht Ausgabe) hätte Fehlalarme über jeder Probe, die ihr Wort nur im Kommentar
und im `print` trägt — und das sind fast alle. *Die schärfere Antwort ist nicht eine zweite
Textregel, sondern genau diese Spur: wer keine Marke und keinen Namen hat, fällt jetzt als
BLIND auf statt als sauber.*

## Die acht Schalenwächter: **abgesagt, und diesmal gerechnet**

Die erste Lesung schrieb *„für sie ist die Zahl kein Wert"* und ließ es dabei. Der Preis ist
jetzt gemessen — alle acht einmal gefahren, alle grün:

| | s | ruft |
|---|---:|---|
| `pruefe-lean-beweis.sh` | 78,3 | `lake` |
| `pruefe-emission.sh` | 33,5 | `cargo run` je Einheit, `cc` |
| `pruefe-p6-beweis.sh` | 19,3 | `isabelle` |
| `pruefe-beweise.sh` | 8,2 | `isabelle` (warm; kalt 33,0) |
| `pruefe-lean-programm.sh` | 2,6 | `lake` |
| `pruefe-sonden.sh` | 0,5 | `cc` |
| `pruefe-syntax.sh` | 0,3 | `cargo` |
| `zaehle-fallen.sh` | 0,0 | — |
| **zusammen** | **142,7** | **7 von 8 rufen `cargo`/`cc`/`isabelle`/`lake`** |

`zaehle-probenzweige.py` kostet heute **2 min 11 s** ohne die Abnahme. Die acht dazu wären
**+142,7 s** — und mit ihnen zöge die ganze Bau- und Beweiskette in ein Messwerkzeug ein,
das schon in `SCHWER` steht. `pruefe-emission.sh` steht dort **selbst**, und der Grund ist
der ORT und nicht die Zeit (`CLAUDE.md`).

**Und es wäre nicht ein Zusatz, sondern ein zweites Instrument.** `bash -x` misst Befehle;
die Rahmenvererbung dieser Messung — *wer von einer Probe gerufen wird, liegt auf der
Probenseite* — braucht `${BASH_LINENO[*]}` in `PS4` und eine Kellerrekonstruktion, mit
eigener Sprechprobe in beide Richtungen.

> **Die Absage steht jetzt in der Antwortzeile selbst und nicht in einer Fußnote.** `14 von
> 43` liest sich sonst wie eine Aussage über die Werkstatt; **43 von 52** ist die Zahl, für
> die sie gilt, und die neun fehlenden haben einen Preis mit Sekunden daran.
