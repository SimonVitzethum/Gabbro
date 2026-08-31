# Drei Register über einer Regel: **83 gegen 88**, und die Grenze steht jetzt in der DATEI

*Gemessen am 2026-08-31 auf `ki-pc-fisch-101` (`gabbro-r2`, `gcc 13.3.0`, 16 Kerne), über
den Stand `893e53a`. Ein Durchgang über **alle** `.gab` des Baumes, ohne eine Zeile am Baum
zu ändern.*

Die Regel stand an zwei Orten und lautete an beiden gleich:

> **Jede Datei, die emittiert, muss auch übersetzen.**

`pruefe-emission.sh` Stufe 9 sagt `83 von 83`. `pruefe-grammatiktafel.py` sagt `87 von 88`.
**Beide Zahlen sind richtig** — und der Unterschied ist keine Rundung, sondern ein Glob.

> **Der Ausgang in einer Zeile:** die Reichweite ist ausgedehnt (109 → 431 Dateien, 83 → 88
> emittierende), **die Ausnahmeliste ist leer geblieben**, und die Grenze steht nicht mehr an
> einem Verzeichnis, sondern an der Zeile `-- erwartet: cc`, mit der eine Datei selbst sagt,
> dass ihr C fallen soll. Der dritte Halter, der diese Zeile schon las, stand die ganze Zeit
> in `crates/gabbro-check/tests/beispiele.rs` — **§6.**

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

### Und es sind DREI Register, nicht zwei

Die Suche nach dem zweiten Halter hat einen dritten gefunden, und er ist der interessanteste:

| | Ort | Reichweite | was er verlangt |
|---|---|---|---|
| 1 | `pruefe-emission.sh` Stufe 9 | 109 Dateien → heute der ganze Baum | emittiert ⇒ `cc` nimmt an |
| 2 | `pruefe-grammatiktafel.py` | ganzer Baum | emittiert ⇒ `cc` nimmt an *(Tor zu `gesenkt`)* |
| 3 | `crates/…/tests/beispiele.rs` | `beispiele/gift/` | `-- erwartet: cc` ⇒ Prüfer schweigt **und** `cc` lehnt ab |

**Der dritte verlangt für `gift/413` das GEGENTEIL des ersten.** Genau eine Datei trägt heute
`-- erwartet: cc` — die Zeile ist in derselben Nacht entstanden, mit der Probe. Damit ist die
Frage nach der Ausdehnung keine Reichweitenfrage mehr, sondern eine nach dem **Vorzeichen**.

## 7. Der gewählte Ausgang: die Reichweite ist der ganze Baum, und die Grenze steht in der DATEI

Nicht Verzeichnis gegen Verzeichnis, sondern die Erklärung, die die Datei über sich selbst
abgibt:

```
-- erwartet: cc      das C MUSS fallen.  Faellt es nicht, beisst die Probe nicht mehr.
alles andere         das C MUSS stehen.
```

**Die Ausnahmeliste bleibt leer — und das ist kein Kunstgriff, sondern die Folge.** Ein
Eintrag in `ausnahme_grund()` ist ein *Befund mit Adresse*, der einmal abläuft;
`-- erwartet: cc` ist keiner — es ist die **Zusage der Datei**, dass ihr C fallen soll. Eine
Liste hätte außerdem **einen Eintrag je `-- erwartet: cc`-Probe** gebraucht, also ein zweites
Register des Giftkorpus — *genau das `W7`, gegen das diese Ausdehnung gebaut ist.* Dieselbe
Bewegung wie am 2026-08-20: **die REGEL, nicht die Liste.**

### Was daran neu MISST, und nicht nur dieselbe Zahl breiter macht

Die Umkehrung hat eine zweite Richtung, die es vorher nirgends gab: **eine `-- erwartet: cc`-Probe,
deren C plötzlich übersetzt, ist rot.** Entweder ist der Erzeugerfehler geheilt — dann gehört
die Probe fort — oder sie trifft nicht mehr. *Eine Probe, die nicht mehr beißen kann, liest
sich wie eine, die es nie konnte.*

### Die Marken: sechs statt zwei, und eine davon zeigt nach unten

| Wurzel | Marke | Richtung | warum |
|---|---:|---|---|
| `beispiele/` | 54 | Ratsche (Boden) | eine Datei weniger = der Erzeuger hat eine Form verloren |
| `messung/*/` | 29 | Ratsche | dito |
| `messungen/` | 2 | Ratsche | neu |
| `programmlogik/` | 1 | Ratsche | neu |
| **`beispiele/gift/`** | **2** | **DECKE** | eine Datei weniger = **der Prüfer fängt eine mehr, bevor sie emittiert** |
| sonst | 0 | exakt | eine neue Wurzel, die emittiert, meldet sich selbst |
| `-- erwartet: cc` | 1 | exakt | fällt sie auf 0, misst der umgekehrte Zweig **nichts** |

> **Die Richtung ist der Ertrag, nicht die Zahl.** In `beispiele/` ist eine verlorene Datei ein
> Schaden, in `gift/` ein Gewinn — am 2026-08-31 ist genau das passiert:
> `gift/45-pub-wo-es-nicht-steht.gab` fiel durch den neuen Pass `P041` aus der Emission. *Wer
> dort dieselbe Ratsche hängt wie nebenan, meldet die gute Arbeit als Bruch.*

### Und die letzte Marke ist die Lehre aus §9.4 der Grammatiktafel

`MARKE_UMGEKEHRT = 1` zählt die lebenden umgekehrten Proben. Fällt sie auf 0, läuft der
`-- erwartet: cc`-Zweig über keine einzige Datei mehr und ist grün, ohne etwas gesagt zu
haben. *Das ist der Fall, an dem die Sprechprobe der Grammatiktafel am selben Tag gestorben
ist: die Arbeit, die den Baum verbessert, hat den Wächter abgeschaltet.* **Hier fällt es auf.**

## 8. Gemessen, nicht behauptet: die drei neuen Zweige gehen ROT

*Alle drei auf `ki-pc-fisch-101` gefahren, jeweils am unveränderten Wächter, Rücklaufwert `1`.*

| Sprechprobe | Eingriff | was der Wächter sagt |
|---|---|---|
| neue Wurzel | `probe-neue-wurzel/x.gab` angelegt (Kopie von `03-format`) | `NEUE WURZEL EMITTIERT: 1 … gebucht sind 0` |
| Probe beißt nicht | `-- erwartet: cc` vor `messungen/narrow.gab` gesetzt | `PROBE BEISST NICHT MEHR: … cc nimmt das C an` |
| Probe verschwindet | `gift/413` weggenommen | `FUND: 1 statt 2 …` **und** `UMGEKEHRTE PROBEN: 0 statt 1` |

Und der Preis in Zeit: **16,6 s → 21,1 s** (`ki-pc-fisch-101`, ganzer `pruefe-emission.sh`)
für 322 Dateien mehr Reichweite. `FRIST_VOLL` ist 1800 s.

Der grüne Lauf liest sich jetzt so:

```
umgekehrte Probe  beispiele/gift/413-format-feld-heisst-gueltig.gab -- `-- erwartet: cc`, und cc lehnt ab. Sie beisst:
    regel.c:23:20: error: redefinition of 'Eintrag_gueltig'
87 von 87 emittierenden Dateien uebersetzen; 0 benannte Ausnahmen,
1 umgekehrte Proben (`-- erwartet: cc`) -- zusammen 88, die emittieren
(54 beispiele/, 2 beispiele/gift/, 29 messung/*/, 2 messungen/, 1 programmlogik/, 0 sonst)
```

## 9. Welcher ist der Gegenstand und welcher die Gegenprobe?

Die Frage ist jetzt beantwortbar, weil die Reichweiten gleich sind:

* **`pruefe-emission.sh` Stufe 9 ist der GEGENSTAND.** Er trägt die Regel, er kennt beide
  Vorzeichen, und er hat die Marken. Er ist grün oder rot **wegen dieser Regel**.
* **`pruefe-grammatiktafel.py` ist die GEGENPROBE.** Dort ist das C-Tor kein Selbstzweck,
  sondern die Vorbedingung für `gesenkt`: eine Zelle gilt erst als abgesenkt, wenn das C steht.
  Es misst dieselbe Sache mit **anderer Apparatur** — Python statt Shell, `-O0` **und** `-O2`
  statt `-O0`, Rohr statt Datei — und beantwortet damit eine andere Frage.
* **`tests/beispiele.rs` ist die Gegenprobe des Vorzeichens.** Er verlangt für `-- erwartet: cc`
  beide Hälften, und er läuft in `cargo test` statt im Schnelllauf.

*Zwei Register über derselben Sache sind nur dann keins, wenn eines das andere prüft.* Hier
sind es drei, mit drei verschiedenen Apparaturen, und die Reichweite ist bei zweien
buchstäblich dieselbe Menge — **das ist der Zustand, in dem eine Abweichung ein Befund ist und
kein Reichweitenunterschied.**

## 10. Was diese Messung NICHT sagt

* **Nichts über den Erzeugerfehler selbst.** `emit.rs:3369` bildet den Namen; die Heilung
  gehört zu `crates/` und nicht hierher. **Wird er geheilt, geht Stufe 9 rot** — mit
  `PROBE BEISST NICHT MEHR`, und das ist die richtige Farbe: die Probe gehört dann fort.
* **Nichts darüber, ob die 315 aus dem richtigen Grund abgewiesen werden.** Diese Messung
  fragt nur, ob sie emittieren.
* **Nichts über `cc` als Maßstab.** Gemessen mit `gcc 13.3.0`. `GRAMMATIKTAFEL.md` §7 hat
  dieselbe Menge an zwei Übersetzern gemessen; diese Messung hat das nicht wiederholt.
* **Nichts über die 315.** Dass sie nicht emittieren, heißt, dass der Prüfer sie abweist —
  *warum* er es tut und ob mit dem richtigen Code, misst `zaehle-absagen.py` und nicht diese
  Tafel.
