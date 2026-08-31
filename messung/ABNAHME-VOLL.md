# Die volle Abnahme über 49 Wächter — erwartet, dann gemessen

**Was hier gemessen wird:** ob dieser Baum grün steht, wenn *alles* läuft. Das ist nie
gefragt worden. Neun `--voll`-Läufe am 2026-08-30/31; der letzte grüne um **02:52 über 27
Wächter**. Seither ist die Besetzung auf **49** gewachsen. Über 49 gab es **genau einen** Lauf
(17:34), und der endete in einer `TEILMESSUNG` an Stufe 9. Der Zweig der Schlusszeile ohne
Lücke (`92 von 92`) ist bis heute **nur durch die Sprechprobe belegt, nicht durch einen Lauf.**

* **Stand:** `5c9a4ed` (`master`), Arbeitsbaum vorher per `--ff-only` nachgezogen.
* **Wo:** `ki-pc-fisch-101:gabbro-v1`, beide Übertragungen (`-rlpgoD` für `cargo`, `-a` für
  `beweise/`), 15 Theorien am Platz nachgesehen. `free -g`: 110 gesamt, 64 verfügbar, 16 Kerne.
  **Der Rechner war nicht leer** — vier `run_agent.py` und ein Proxy liefen nebenher.
* **Start:** 2026-08-31 17:33:49, `nohup setsid python3 instrumente/abnahme.py --voll`.
* **Besetzung:** 49 (`ls instrumente/{pruefe,mutiere,zaehle}-*`), `OHNE_URTEIL` ist **leer** —
  es steht niemand mit Namen draußen.

---

## 1 — Die Erwartung, VOR dem Ergebnis aufgeschrieben

*Ein Ergebnis, das man erst hinterher erwartet hat, misst nichts.* Dieser Abschnitt ist
committet, **bevor** der Lauf seine erste Zeile ausgegeben hat.

### Sicher (Umgebung nachgesehen, nicht geraten)

| Wächter | erwartet | Grund |
|---|---|---|
| `pruefe-grammatiktafel.py` | **ROT** an `state` | gebucht, kein Befund |
| `zaehle-b3.py` | **NICHT FAHRBAR** | `../caprock-messbasis` gibt es auf `fisch` nicht (nachgesehen) |
| `zaehle-narrow.py` | **NICHT FAHRBAR** | `~/Dokumente/SEL4Lake/SEL4Lake` gibt es auf `fisch` nicht (nachgesehen) |

`NICHT FAHRBAR` lässt den Lauf grün — *ein Loch mit einem Namen*.

### Die Vorhersage, auf die es ankommt

**`pruefe-saetze.py` wird `ABBRUCH` melden, mit `das Binaerprogramm ist AELTER als N
Quelldatei(en)` — INNERHALB dieses Laufs, nicht erst im nächsten.**

`CLAUDE.md` bucht diesen Riegel als etwas, das den *nächsten* Lauf trifft. Das ist zu
schwach. Die Besetzung wird **alphabetisch** gefahren (`abnahme.py:besetzung`, `key=p.name`),
und damit steht `mutiere-pruefer.py` an **Platz 1** und `pruefe-saetze.py` achtzehn Plätze
später. Der Mutationslauf schreibt in jede Quelle unter `crates/*/src/` und stellt sie
byteweise zurück — *mit neuer `mtime`*. Also ist beim achtzehnten Wächter jede Quelle jünger
als das Binärprogramm, das der erste gebaut hat.

Der Riegel trifft nicht den nächsten Lauf. **Er trifft diesen, eine Stunde nach seinem
eigenen Start.** Das ist Ausgang (3): der Wächter misst die Messapparatur, nicht seinen
Gegenstand.

Und die Asymmetrie steht schon im Baum: `zaehle-absagen.py` stellt dieselbe Forderung, aber
wenn die Uhr „veraltet" sagt, **fragt er den Inhalt nach** (`zaehle-absagen.py:360`, *„When
the CLOCK says stale, ask the CONTENT"*). `pruefe-saetze.py:120` fragt nur die Uhr und bricht
ab. Zwei Wächter, ein Baum, eine Frage — und nur einer von beiden kann sie beantworten.

### Wo ich mir am wenigsten sicher bin

1. **Die Lean-Kette** (`pruefe-lean-beweis.sh`, `pruefe-lean-programm.sh`, `zaehle-lean.py`).
   `~/.elan/bin/lake` liegt auf `fisch` (nachgesehen), aber `.lake/` ist nicht mit
   übertragen worden — es wird **von Grund auf gebaut**, und zwar auf einem Rechner, auf dem
   vier fremde Agenten laufen. `FRIST_ABNAHME` sind 600 s. Der Kommentar in `abnahme.py`
   nennt genau diesen Fall schon einmal gemessen: 194 s und 205 s auf einem *leeren* `fisch`,
   und im `--voll`-Lauf über 300 s hinaus. **Ich erwarte hier am ehesten ein falsches
   `HAENGT`** — Ausgang (3), und es sagt etwas über die Maschine, nicht über den Baum.
2. **`pruefe-emission.sh`, Stufe 9 und 10.** Der eine Lauf über 49 endete dort in einer
   `TEILMESSUNG`. Ob der Baum seither geheilt ist oder nur nicht wieder gefragt wurde, weiß
   ich nicht. Ich erwarte, dass er wieder abschneidet, aber ich habe keinen Grund dafür
   außer dem letzten Mal.
3. **Die 18 `zaehle-*`.** Sie sind seit dem 2026-08-31 in der Abnahme und haben über einem
   *leeren* Baum sämtlich rot gemeldet. Über einem *vollen* hat sie noch niemand alle
   zusammen gefahren. Hier habe ich schlicht keine Erwartung, und das ist der ehrliche
   Eintrag.
4. **Ob der Lauf überhaupt durchkommt.** `FRIST_VOLL` sind 1800 s für den Mutationslauf; der
   braucht lokal 10 min 25 s über 340 Mutationen. `GEGENSTAND` nennt inzwischen **372**. Auf
   einem belasteten `fisch` ist 1800 s keine großzügige Frist.

### Was ich NICHT erwarte

Einen grünen Lauf. Nach neun Läufen an zwei Tagen, von denen der letzte grüne 22 Wächter
weniger kannte, wäre Grün die Überraschung.

---

## 2 — Was der Lauf gesagt hat

**Beendet 17:50:49, nach 17 Minuten.** Die Schlusszeile, wörtlich:

```
! ABNAHME ABGEBROCHEN: 1 Waechter haben KEIN Urteil geliefert.
   pruefe-luecken.py          [2]  und die naechste Messung liest eine Mischung.

und ausserdem 2 von 46 messenden Waechtern melden einen Befund.
   mutiere-pruefer.py         [1]  zwoelf Loecher offenstanden.
   pruefe-grammatiktafel.py   [1]  state            GEMESSEN an messung/proben/probe-vier-zellen.gab: der Erzeuger
```

Und die Arbeitsmenge daneben:

```
== Arbeitsmenge: 46 von 49 Waechtern haben GEMESSEN -- 44 gruen, 2 ROT, 0 TEILMESSUNG ==
   1 ABBRUCH, 2 nicht fahrbar, 0 ausgelassen
== Und ihr GEGENSTAND: hoechstens 91 von 92 gefaehrlichen Stellen besucht -- 99 % ==
```

**Die Antwort auf die Frage, die nie gestellt worden ist:** *nein, der Baum steht nicht
grün, wenn alles läuft* — aber knapper als die neun Läufe davor vermuten ließen. **44 von
46 messenden Wächtern sind grün.** Von den drei, die es nicht sind, ist einer gebucht, einer
misst die Übertragung statt den Baum, und beim dritten ist der gedruckte Grund vier Wochen
älter als der Lauf. **Kein einziger `TEILMESSUNG`** — der Zweig, an dem der Lauf um 17:34
noch hängenblieb, ist durch.

### Der Zweig ohne Lücke ist weiterhin NICHT durch einen Lauf belegt

`92 von 92` steht nach wie vor nur in der Sprechprobe. Dieser Lauf kam auf **91 von 92** —
die eine fehlende Stelle sitzt in `zaehle-narrow.py`, dessen Korpus es auf `fisch` nicht
gibt. *Solange ein fremder Baum im Register steht, kann kein Lauf auf diesem Rechner die
Schlusszeile ohne Lücke erreichen.* Der Zweig ist damit nicht ungetestet, sondern **auf
dieser Maschine unerreichbar** — das ist ein Befund über den Wächter, kein offener Punkt.

---

## 3 — Die drei, die nicht grün waren — wörtlich und eingeordnet

### (3a) `pruefe-luecken.py` — **ABBRUCH**, und der Wächter misst die ÜBERTRAGUNG

Zeile der Abnahme:

```
  ABBRUCH        pruefe-luecken.py             0.0 s [2]  und die naechste Messung liest eine Mischung.
```

**0,0 s** — er ist gar nicht erst angetreten. Nachgefahren auf `fisch`, seine ganze Absage:

```
ABBRUCH: `git` konnte `crates/` nicht ansehen -- es wurde NICHTS gemessen.
  Der Baum ist WEDER sauber noch schmutzig, sondern ungemessen -- so faellt
  `git status` auf einer per `rsync` uebertragenen Kopie (128, leere Ausgabe).
  Dieses Werkzeug SCHREIBT in Quellen und laeuft ohne diesen Nachweis nicht:
  ein Lauf, der auf halbem Weg stirbt, laesst eine verdrehte Quelle stehen,
  und die naechste Messung liest eine Mischung.
```

**Ausgang (3): der Wächter misst etwas anderes als seinen Gegenstand.** Und zwar
strukturell, nicht zufällig:

* Der Arbeitsbaum eines Agenten ist ein `git worktree`. Dort ist `.git` eine **Datei**, kein
  Verzeichnis, und ihr ganzer Inhalt lautet
  `gitdir: /home/simon/Dokumente/Gabbro/.git/worktrees/agent-a3f6841b8d13471c0`.
* `rsync` überträgt diesen Zeiger — nicht sein Ziel. Auf `fisch` zeigt er ins Leere, und
  `git status` endet mit **128 und leerer Ausgabe**.
* `CLAUDE.md` schickt genau diesen Wächter auf den Server (*„baut dreizehnmal neu — gehört
  auf den Server"*).

> **Die Übertragung, die ihn dorthin bringt, ist dieselbe, die seine Vorbedingung zerstört.**
> Aus einem Arbeitsbaum heraus ist `pruefe-luecken.py` auf `ki-pc-fisch-101` **nicht
> fahrbar** — und die Abnahme bucht das als `ABBRUCH`, was den ganzen Lauf mit
> Rücklaufwert 2 abschließt.

*Der Wächter hat recht* — er darf nicht in Quellen schreiben, ohne den Baum vorher als
sauber zu kennen. Falsch ist nicht sein Riegel, sondern dass niemand ihm sagt, dass er auf
einer Kopie steht. Dieselbe Klasse wie `W16`: **ein Messgerät, das die Herkunft seiner Probe
nicht kennt.**

### (3b) `zaehle-b3.py` — dieselbe Wurzel, eine Ebene höher, und diesmal STILL

Nicht rot, aber es gehört daneben:

```
  NICHT FAHRBAR  zaehle-b3.py                  0.0 s      fremder Korpus fehlt: die Caprock-Messbasis (Zweig arch/x86_64) (/home/simon/Dokumente/caprock-messbasis)
```

**Der Lauf fand auf `fisch` statt und nennt einen Pfad auf dem Arbeitsrechner.**
`hauptauscheckung()` liest denselben `.git`-Zeiger und leitet daraus
`/home/simon/Dokumente/Gabbro` ab; `../caprock-messbasis` landet dann bei
`/home/simon/Dokumente/…` — einem Verzeichnis auf einer **anderen Maschine**. Zum Vergleich
die Zeile darunter, die es richtig macht, weil sie mit `~` beginnt:

```
  NICHT FAHRBAR  zaehle-narrow.py              0.0 s      fremder Korpus fehlt: der zweite Korpus, SEL4Lake (/home/fisch/Dokumente/SEL4Lake/SEL4Lake)
```

Das Urteil ist trotzdem **richtig** (Caprock liegt auf `fisch` wirklich nicht), und der
Quelltext sagt selbst, dass er im Zweifel nach `NICHT FAHRBAR` irrt und nie nach Grün. Aber
die Heilung vom 2026-08-31 — *„Read from the `.git` marker, not from `git`"* — hat den
Arbeitsbaum-Fall geschlossen und dabei den **Maschinen-Fall geöffnet**: derselbe Zeiger, der
den Wächter im Arbeitsbaum rettet, verlegt ihn auf dem Server auf einen fremden Rechner.
Der Kommentar über der Funktion nennt die Klasse bereits beim Namen (*„Same class as the
guardian whose verdict hung on the MACHINE"*) — nur eben als das, was geheilt wurde, nicht
als das, was entstand.

**Ausgang (3), aber ohne Rückstand:** hier ist nichts zu heilen, was das Urteil ändert. Zu
buchen ist, dass **zwei Wächter aus einem Arbeitsbaum heraus auf dem Server grundsätzlich
kein Urteil liefern können** — und dass beide es aus demselben Grund tun.

### (3c) `pruefe-grammatiktafel.py` — **ROT** an `state`

```
  ROT            pruefe-grammatiktafel.py      3.4 s [1]  state            GEMESSEN an messung/proben/probe-vier-zellen.gab: der Erzeuger
```

**Ausgang (2): gebucht, kein Befund.** Vorher angekündigt, wie erwartet eingetroffen. Der
einzige der drei, der genau das war, was auf dem Zettel stand.

### (3d) `mutiere-pruefer.py` — **ROT**, und die gedruckte Zahl gehört zum 14. August

```
  ROT            mutiere-pruefer.py          523.6 s [1]  zwoelf Loecher offenstanden.
```

Wer diese Zeile liest, bucht **zwölf überlebende Mutationen von heute**. Es sind keine. Die
Abnahme zeigt in der Bemerkungsspalte die **letzte gedruckte Zeile** des Wächters, und
dessen letzte Zeile ist ein Halbsatz aus einem Fließtext (`mutiere-pruefer.py:4315`):

```
  Eine ueberlebende Mutation heisst: die Regel koennte ausfallen, ohne dass
  eine einzige Probe faellt. Das ist genau die Richtung, in der am 2026-08-14
  zwoelf Loecher offenstanden.
```

**Ein Datum vom 14. August, in der Zusammenfassung eines Laufs vom 31. August.** Die echte
Zahl steht weiter oben, in der Überschrift `== UEBERLEBT ==`, und wird von der Abnahme
weggeworfen.

**Ausgang (3) — und zwar an der ABNAHME, nicht am Mutationslauf.** `abnahme.py` nimmt
`kopf[-1]` als Bemerkung. Für jeden Wächter, dessen Ausgabe mit Prosa endet statt mit einer
Bilanz, druckt die Abnahme damit einen Satz, der wie ein Messwert aussieht und keiner ist.
*Genau `W25` an der Stelle, die W25 zitiert:* **eine Zahl belegt ihren Nenner, nicht ihre
Beschriftung** — hier belegt sie nicht einmal ihr Jahr.

Nachgemessen, indem der Mutationslauf einzeln gefahren und seine ganze Ausgabe gelesen wurde:

<!-- UEBERLEBT -->

---

## 4 — Was ich falsch vorhergesagt habe

**Die Vorhersage, auf die es ankam, war falsch.** `pruefe-saetze.py` kam grün durch, in
0,0 s, mitten im selben Lauf, in dem `mutiere-pruefer.py` achtzehn Plätze vorher jede Quelle
neu geschrieben hatte.

Der Grund, gemessen und nicht vermutet — auf `fisch`, unmittelbar nach dem Lauf:

```
target/debug/gabbro                     2026-08-31 17:42:55.359356866
crates/gabbro-check/src/emit.rs         2026-08-31 17:42:31.101078332
```

**Das Binärprogramm ist 24 Sekunden JÜNGER als die zuletzt zurückgestellte Quelle.** Meine
Argumentation über die alphabetische Reihenfolge war richtig; meine Annahme über die
Reihenfolge *innerhalb* des Mutationslaufs war falsch. Er stellt nicht nach dem letzten Bau
zurück, sondern baut nach der letzten Rückstellung.

*Das ist der Wert der vorher aufgeschriebenen Erwartung:* die Vorhersage war präzise genug,
um an einem einzigen Zeitstempel zu scheitern, und das Scheitern hat den Mechanismus
freigelegt, der in `CLAUDE.md` falsch beschrieben ist.

Was **richtig** vorhergesagt war: `pruefe-grammatiktafel.py` rot an `state`, `zaehle-b3.py`
und `zaehle-narrow.py` nicht fahrbar. Und die Unsicherheiten haben sich auf eine
angenehme Weise aufgelöst — dazu unten.

---

## 5 — Der Riegel nach `--voll`: er schnappte NICHT zu

`CLAUDE.md` sagt: *„Nach `abnahme.py --voll` ist die naechste `abnahme.py` ROT, und das ist
kein Befund."* **Gefahren, und so kam es nicht.** Die Schlusszeile des Nachlaufs (Schnellauf,
unmittelbar nach dem vollen, im selben Verzeichnis):

```
! ABNAHME ROT: 1 von 44 messenden Waechtern melden einen Befund.
   pruefe-grammatiktafel.py   [1]  state            GEMESSEN an messung/proben/probe-vier-zellen.gab: der Erzeuger
```

Rot — aber **an der gebuchten Stelle und an keiner anderen**. `pruefe-saetze.py` steht in der
Liste als `gruen`, `0.0 s`, `[0]`. Der beschriebene `ABBRUCH: das Binaerprogramm ist AELTER`
kam nicht.

### Der Riegel existiert — er wird nur nicht ausgelöst

Beides einzeln nachgefahren, damit die Aussage in beide Richtungen belegt ist:

```
$ touch crates/gabbro-check/src/saetze.rs && ./instrumente/pruefe-saetze.py
EXIT NACH TOUCH=2
ABBRUCH: das Binaerprogramm ist AELTER als 1 Quelldatei(en) -- saetze.rs.
  Die beanspruchten Kennungen kaemen dann aus dem alten Baum und die vorhandenen aus dem neuen.
  Das ist eine MISCHUNG und keine Zaehlung -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).

$ cargo build && ./instrumente/pruefe-saetze.py
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.61s
EXIT NACH BAU=0
```

**Der Mechanismus ist heil, die Heilung ist ein Bau, und beides ist jetzt gemessen.** Falsch
ist allein der Auslöser: `--voll` stellt ihn nicht her, weil der Mutationslauf **nach** der
letzten Rückstellung baut.

### Und der Absatz widerspricht schon seiner eigenen Messung

`CLAUDE.md` schreibt neben die Regel: *„ein Lauf rot direkt nach `--voll`, fuenf Laeufe gruen
danach"*. Das ist **ein roter Lauf von sechs** — und darüber steht eine Regel im Indikativ
(*„ist ROT"*). Die Beobachtung stimmt vermutlich; sie hatte nur nie den Auslöser, den der
Satz ihr zuschreibt. Ein `touch`, ein `git merge` oder ein `rsync -rlpgoD` erzeugen genau
diesen Zustand — der Mutationslauf, den der Absatz beschuldigt, hebt ihn wieder auf.

> **Zu ändern ist der Absatz in `CLAUDE.md`, nicht der Wächter.** Er gehört einer anderen
> Bahn; der Vorschlag steht hier und nicht dort.

---

## 6 — Wo ich unsicher war, und wie es ausging

| Unsicherheit | Ausgang |
|---|---|
| **Lean-Kette: falsches `HAENGT` unter Last** | **Nein — grün, und die Zahl fehlte bisher.** `pruefe-lean-beweis.sh` brauchte **381,2 s** bei `load average` 10–15 auf 16 Kernen. `TODO.md` bucht seit dem 2026-08-30: *„niemand weiß, wie lange der Wächter unter Last wirklich braucht"* und verlangt ausdrücklich *„eine Messung unter Last, keine größere Zahl"*. **Hier ist sie.** 381 s gegen `FRIST_ABNAHME` = 600 s — 64 % der Frist, gegen 194/205 s im Leerlauf. Der Faktor unter Last ist **1,9**, nicht die 1,5, gegen die die Frist gesetzt wurde. `pruefe-lean-programm.sh` lief in 11,9 s. |
| **`pruefe-emission.sh` schneidet wieder an Stufe 9 ab** | **Nein — grün in 21,9 s, `0 TEILMESSUNG` im ganzen Lauf.** Der Zweig, an dem der 17:34-Lauf hängenblieb, ist durch. Damit sind auch die **45 gefährlichen Stellen** dieses Wächters — knapp die Hälfte aller 92 — zum ersten Mal in einem vollständigen Lauf besucht worden. |
| **Die 20 `zaehle-*` über einem vollen Baum** | **Alle grün** außer den zwei mit fehlendem Fremdkorpus. Über einem leeren Baum hatte keiner ein grünes Urteil gegeben; über einem vollen geben es alle. |
| **Ob der Lauf überhaupt durchkommt** | **Ja, 17 Minuten.** Der Mutationslauf brauchte **523,6 s** (8 min 44 s) auf `fisch` unter Fremdlast — gegen 10 min 25 s lokal in `CLAUDE.md`. `FRIST_VOLL` = 1800 s war nicht knapp. |

**Beide Übertragungen haben getragen:** `pruefe-beweise.sh` grün in 23,2 s über alle 15
Theorien, kein `OHNE NACHWEIS`.

