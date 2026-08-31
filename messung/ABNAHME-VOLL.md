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

*(wird nach dem Lauf gefüllt — wörtlich, je roter Wächter mit seinem Ausgang)*
