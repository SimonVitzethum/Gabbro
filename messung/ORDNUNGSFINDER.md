# Der Ordnungsfinder — die Paarung hatte eine Form und keinen Finder

*Entschieden am 2026-08-28. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **Der Befund zuerst, und er steht wörtlich in
> [`ORDNUNGSSTICHPROBE-BEFUND.md`](ORDNUNGSSTICHPROBE-BEFUND.md) §5.1:**
>
> > *„§1s drei Typregeln können ein S nicht **finden**. Sie prüfen Paarungen; eine Stelle,
> > die `publishes nothing`/`relaxed` erklärt, geht durch. Wer dieses Feld als Z deklariert,
> > bekommt keinen Fehler — er bekommt einen Übersetzer, der schweigt."*
>
> **Acht Kennungen prüfen heute die Paarung** (`V001`–`V008`, `paarung.rs`), und **alle acht
> setzen voraus, dass jemand sie hingeschrieben hat.** `V001` will zu einem `publishes` ein
> `awaits`, `V002` umgekehrt, `V004`/`V005` wollen die Ordnung dazu, `V006`/`V007` die
> Reihenfolge, `V008` die Obermenge. *Keine von ihnen fragt, ob eine Paarung FEHLT.*

**Eine Form, die schweigt, sagt jahrelang ja.** Genau derselbe Befund wie bei `H007`
(`protects`, nie genommen), bei `@version` und bei `raw fn` — ein Wort, das eine Disziplin
verspricht und von niemandem gelesen wird.

---

## 1. Die zwei Gestalten, die der Befund ausgeschrieben hat

Sie sind nicht erfunden; sie stehen mit Datei und Zeile im Bericht.

### 1.1 Nr. 34 — `aarch64/mmu.rs:800`, das Tor ohne Paarung

```rust
817  pub fn seal_cache_granule()   { CWG_SEALED.store(true, Release); }   // nur Kern 0
821  pub fn dma_granule() -> u64 {
822      if !CWG_SEALED.load(Acquire) { return CWG_ARCH_MAX; }   // <- das TOR
826      match CWG_MAX.load(Relaxed) { … }                       // <- die NUTZLAST dahinter
830  }
```

**`CWG_SEALED` ist als Fall „ohne Nutzlast" geschrieben, und hinter seinem Tor liegt eine.**
`dma_granule()` gattert `install_dma_cap` — eine Autoritätsprüfung, keine Diagnose. Das ist
die Gestalt: *ein Wert aus einem lastfreien Atomic entscheidet, und hinter der Entscheidung
wird ein anderer geteilter Platz gelesen.*

### 1.2 Nr. 34 noch einmal — die Paarung, die typprüft und nicht trägt

Der Bericht schreibt sie ebenfalls aus:

> *„Man könnte `CWG_SEALED = true publishes { CWG_MAX }` hinschreiben, und §1s Regel 1
> (statischer Namensvergleich) liesse es **durch**. Es wäre trotzdem falsch: das `release`
> von Kern 0 veröffentlicht **die Schreibzugriffe von Kern 0**, nicht das `fetch_max` von
> Kern 5."*

**Der Namensvergleich fragt, WAS veröffentlicht wird, und nie, WER es geschrieben hat.**

---

## 2. Die Messung, die entscheidet

Zwei Zahlen, und die zweite ist die, die einen ganzen Zuschnitt umbringt.

### 2.1 Wie kommt im Korpus ein Wert aus einem Atomic heraus?

```bash
$ python3 messung/ordnung/tore.py | tail -4
korpus  Bindungen aus einem atomic: {'awaits': 10, 'exchange': 10, 'schlicht': 0}
korpus  davon gattern einen Zweig:  {'awaits':  9, 'exchange':  4, 'schlicht': 0}
gift    Bindungen aus einem atomic: {'awaits':  5, 'exchange':  2, 'schlicht': 1}
gift    davon gattern einen Zweig:  {'awaits':  4, 'exchange':  0, 'schlicht': 1}
```

**20 Bindungen im Korpus, und NULL davon ist eine schlichte Lesung.** Jede geht entweder über
`awaits` (die Paarung steht) oder über `exchange` (die dritte Form der Paarung, mit eigenem
`publishes`/`awaits`-Platz).

> **Die Trennung Korpus/Gift ist keine Kosmetik, und die erste Fassung dieser Zahl hatte sie
> nicht.** Sie warf beide Töpfe zusammen und las sich als *„26 Bindungen, 0 schlichte"* —
> richtig in dem Augenblick, in dem sie genommen wurde, und **falsch, sobald die Giftprobe
> dieser Entscheidung im Baum stand**: die eine schlichte Lesung, die der Baum heute trägt,
> ist `beispiele/gift/301`. *Eine Messung, die die eigene Gegenprobe mitzählt, misst sich
> selbst.* Die Zahl, die die Entscheidung trägt, ist die des Korpus.

> **Das ist ein Befund für sich, und er schneidet in beide Richtungen.** Er sagt: die Gestalt
> aus §1.1 kommt im eigenen Korpus **nicht vor** — eine Regel darauf kann dort keinen
> Fehlalarm erzeugen. Er sagt aber auch: **der Korpus misst sie nicht.** Die Regel hängt
> danach an ihrer Giftprobe und an nichts sonst, und genau so steht sie im `vorbehalt`.

### 2.2 Was der starke Zuschnitt kosten würde

Der naheliegende starke Zuschnitt lautet: *jede Lesung eines geteilten veränderlichen
Platzes steht unter einer Sperre oder hinter einem `awaits`.* Gemessen über die sauberen
Beispiele:

```bash
$ python3 messung/ordnung/ungeordnet.py | tail -2
Lesungen geteilter Plaetze insgesamt: 71
davon weder unter Sperre noch hinter `awaits`: 43
```

43 ist die rohe Zahl; sie enthält Deklarationszeilen, `ensures`/`floor`-Klauseln und die
Nennung einer Nutzlast in einem `publishes`. **Nach Abzug all dessen bleiben 18 echte
Rumpflesungen**, und sie stehen hier einzeln, damit die Zahl nachprüfbar ist statt geglaubt:

```
06:88 tiefe_max · 08:142 kernlast · 27:34 frei · 27:48 frei · 28:35 hinterlegt
28:44 hinterlegt · 39:127 erledigt · 39:136 erledigt · 41:188 frei · 41:206 gestellt
41:207 gestellt · 41:231 uebertragen · 42:234 gesehen · 42:275 gesehen · 42:311 gesehen
42:314 gesehen · 43:85 frei · 49:86 ZUSTAND
```

**Achtzehn Fehlalarme über einem Korpus, der nach Bauart richtig ist.** Damit ist der starke
Zuschnitt nicht bezweifelt, sondern widerlegt — dieselbe Bewegung wie bei den elf
`bool`-Feldnamen in [`OPS-ERZEUGER.md`](OPS-ERZEUGER.md) §2: *eine Namensheuristik ist damit
widerlegt, nicht bezweifelt.*

---

## 3. Die drei Formen, beide Seiten je Form

### (a) Die Pflicht an der Deklaration — jedes `atomic` muss `publishes` oder `publishes nothing` tragen

| | |
|---|---|
| **dafür** | keine Analyse, keine Zeile Datenfluss. Rein deklarativ, sofort gebaut |
| **dagegen** | **sie prüft die Deklaration gegen sich selbst.** Wer `publishes nothing` schreibt, wird geglaubt — und das ist wörtlich die Lage, die der Befund als *„einen Übersetzer, der schweigt"* benennt. *Sie findet ein fehlendes WORT, nicht eine fehlende Paarung.* Und sie steht ohnehin schon halb da: `V004`/`V005` |

### (b) Der starke Zuschnitt — jede Lesung eines geteilten Platzes braucht Sperre oder `awaits`

| | |
|---|---|
| **dafür** | **er fände jede fehlende Paarung, nicht nur die gegatterten.** Fail-closed im stärksten Sinn: nicht erklärt heisst abgelehnt |
| **dagegen** | **18 Fehlalarme über `beispiele/`** (§2.2, Stellen einzeln genannt). Ein Prüfer, der den eigenen Korpus achtzehnmal falsch anklagt, wird abgeschaltet, nicht befolgt — und dann prüft er nichts. *Das ist der Preis, den `H007` nicht zahlen musste und dieser hier zahlen müsste* |

### (c) Das TOR — ein lastfreies Atomic, dessen Wert einen Zweig gattert, hinter dem ein fremder geteilter Platz gelesen wird

| | |
|---|---|
| **dafür** | **es ist genau die Gestalt der beiden gefundenen Stellen** (§1.1, und Nr. 26 `loader.rs` hat sie ebenso: der Schlüssel gattert, die Nutzlast liegt dahinter). Syntaktisch entscheidbar, kein Speichermodell. **0 Fehlalarme über dem Korpus** (§2.1: es gibt dort keine schlichte Atomlesung), und der Ausweg ist kein Schweigen, sondern ein Satz: die Nutzlast benennen, die Sperre nehmen, oder `observed by` erklären |
| **dagegen** | **es fängt nur, was durch ein TOR läuft.** Eine fehlende Paarung ohne Verzweigung sieht es nicht, und eine Nutzlast, die erst ein Gerufener liest, auch nicht. *Und der Korpus misst es nicht* (§2.1) — die Regel hängt an ihrer Giftprobe |

---

## 4. Die Entscheidung: **(c)**, das Tor — und (b) fällt an einer Zahl

**Der Grund ist die Messung, nicht der Geschmack.** (b) ist die bessere Regel und kostet 18
Fehlalarme; (c) ist die schmalere Regel und kostet keinen. Zwischen einer Regel, die alles
findet und nicht laufen kann, und einer, die die gefundene Klasse findet und läuft, ist die
zweite die, die etwas prüft.

> **Und die Grenze gehört in den Satz, nicht neben ihn.** (c) sagt nicht *„hier fehlt keine
> Paarung"*, sondern *„hier fehlt eine"* — es ist eine Regel, die verpflichtet und nicht
> freispricht (W10). Wer sie als Vollständigkeit liest, liest sie falsch, und der
> `vorbehalt` in `saetze.rs` sagt es mit denselben Worten.

### Die Form — **kein neues Wort**

`V009` braucht keine Grammatik: es liest, was schon dasteht (`atomic`, `publishes nothing`,
`if`, `match`, `narrow`). *Der Grundsatz aus [`SCHLEIFENINVARIANTE.md`](SCHLEIFENINVARIANTE.md)
§3 gilt hier ohne Abwägung — es gibt gar keinen Begriff, den ein Wort tragen müsste.*

**Der Zuschnitt, ausgeschrieben.** `V009` sagt ab, wenn **alles** davon gilt:

1. ein `let x = A;` bindet eine **schlichte** Lesung eines deklarierten `atomic A` — kein
   `awaits`, kein `exchange` (oder `A` steht unmittelbar in der Bedingung);
2. **`A` trägt im ganzen Programm keine Nutzlast**: kein `publishes { … }` und kein `awaits`
   auf `A`;
3. `x` **gattert** einen Zweig — es steht in der Bedingung eines `if`/`match`/`narrow`;
4. in diesem Zweig wird ein **anderer** geteilter veränderlicher Platz **gelesen**
   (`static mut`, ein anderes `atomic`, ein `accumulates`) — nicht `A` selbst;
5. diese Lesung steht **nicht** unter `locks`/`observes`, und der Platz wird von **dieser**
   Funktion **nicht geschrieben**.

**Bedingung 4 („ein ANDERER Platz") ist die, die §5.2 des Befundes eingebaut trägt.** Die
beiden Einmal-Latches (`AGG_COHERENT`, `ECAM_BASE`) lesen hinter ihrem Tor **sich selbst** —
*„der Wert IST die Auskunft"*. Sie fallen damit nicht, und zwar aus dem richtigen Grund.

**Bedingung 5 („diese Funktion schreibt ihn nicht") hat der Korpus erzwungen.** Ohne sie
fiele `beispiele/42`:310 —

```gabbro
let alt = ANFRAGEN exchange update(x) { … } publishes nothing;
…
if alt >= VOLL { return gesehen; }        -- `gesehen` ist ein static mut
```

— und es wäre falsch: `gesehen` ist der **eigene** Wert dieses Rumpfes, drei Zeilen weiter
oben geschrieben, keine fremde Nutzlast. *Die Bedingung kam aus dem Korpus, nicht aus dem
Entwurf* — derselbe Weg wie bei «B41b».

> **Und die Aufzählung der Rümpfe hat einen Tag später einen Nachtrag bekommen:** `V009` lief
> zuerst nur über `ItemArt::Funktion`, und damit war der `can_fail`-Rumpf einer Probe für ihn
> nicht da. **Wörtlich die Lücke, die `V001` am 2026-08-20 bezahlt hat** und die im Modulkopf
> von `paarung.rs` seither steht. Ein `check` ist der eine Ort, an dem eine falsifizierbare
> Zusage über die MASCHINE steht — und eine Ordnungsaussage ist genau das.

---

## 5. Der zweite Befund: der Namensvergleich kennt den Schreiber nicht

Das ist eine eigene Entscheidung und darum ein eigener Abschnitt.

### Die zwei Formen

#### (a) Die Nutzlast muss im RUMPF des Veröffentlichers geschrieben stehen

| | |
|---|---|
| **dafür** | die schärfste Fassung, ein Blick auf einen Rumpf |
| **dagegen** | **`beispiele/14` fällt sofort.** Dort veröffentlicht `melden(b)` die Nutzlast `b.daten`, und geschrieben wird sie von keiner Zeile dieser Datei — sie kommt vom Rufer. `V006` hat diese Grenze schon gezogen: *„Eine Nutzlast, die im Rumpf gar nicht geschrieben wird, ist kein Fehler — sie kann von einem Gerufenen kommen."* Zwei Regeln mit zwei verschiedenen Antworten auf dieselbe Frage |

#### (b) Die Nutzlast muss von diesem Veröffentlicher **oder einem seiner Gerufenen** geschrieben werden — und nur dann, wenn sie im Programm überhaupt geschrieben wird

| | |
|---|---|
| **dafür** | **es ist genau die Aussage des Befundes:** *„das `release` von Kern 0 veröffentlicht die Schreibzugriffe von Kern 0."* Ein Schreiber ausserhalb der eigenen Rufhülle ist ein anderer Kern, und dann trägt die Ordnung nicht. Die Rufhülle steht schon da (`aufrufgraph.rs`), und ihre Unvollständigkeit ist schon behandelt (`V003`) |
| **dagegen** | die Hülle ist **statisch**: zwei Kerne, die dieselbe Funktion laufen, sind für sie ein Schreiber. *Die Regel fängt den fremden NAMEN, nicht den fremden KERN* — und der Befund ist ein Fall, in dem beides zusammenfällt. Was sie nicht fängt, steht im `vorbehalt` |

### Die Entscheidung: **(b)** — `V010`

**Und sie trägt eine Verengung, die der Korpus erzwungen hat:** gemessen wird nur, wenn der
**Grundname der Nutzlast ein modulweiter geteilter Name** ist (`static mut`, `atomic`,
`accumulates`, `table`). Ein Parameter heisst in zwei Funktionen gleich, ohne derselbe zu
sein — `b.daten` in `beispiele/14` ist der Fall, und ein Grundnamenvergleich über Parameter
würde zwei fremde `b` für eines halten.

**Gegenprobe über dem Korpus:** jede der acht Veröffentlichungen mit Nutzlast schreibt sie im
**eigenen Rumpf** — die Schreibzeile steht jedes Mal wenige Zeilen über dem `publishes`:

```
05:50 farbbericht · 39:166 bericht · 41:213 deskring_gesehen · 41:240 arbeitsmenge
42:182 stand · 42:258 stand · 42:363 stand · 43:66 hoechststand
```

Die beiden Treiberstellen (`14`:41 `b.daten`, `virtio-net`:237 `deskring_gesehen`) haben im
Programm **gar keinen** Schreiber und fallen darum aus der Regel heraus. **Null Absagen.**

---

## 6. Der dritte Befund: ein Fach heisst falsch

§1 nennt die lastfreie Kategorie **„counters"**, und der Befund zeigt an zwei von elf
Stellen, dass der Name nicht trifft: `AGG_COHERENT` und `ECAM_BASE` sind **Einmal-Latches**,
keine Zähler. §5.2 rechnet vor, was daran hängt:

| Lesart | P | Z | S | **X** | Urteil über §1 |
|---|---:|---:|---:|---:|---|
| operativ („trägt keine Nutzlast") | 6 | 11 | 1 | **0** | §1 trägt |
| wörtlich („Zähler / Statistik / Kennzahl") | 6 | 9 | 1 | **2** | §1 **widerlegt** |

**Ein Substantiv entscheidet über zwei X.** Das ist kein Wortstreit; das ist die Frage, ob
die Stichprobe §1 bestätigt oder umwirft.

### Die zwei Formen

#### (a) Ein neues Sprachwort — `latch` neben `nothing`

| | |
|---|---|
| **dafür** | die zwei Sorten stünden getrennt da, und jede hätte ihren Namen |
| **dagegen** | **es ist kein zweiter Begriff.** Beide sind *„ein Zugriff ohne getrennte Nutzlast"* — dieselbe Aussage, anderes Möbel. `SCHLEIFENINVARIANTE.md` §3: *„Ein zweites Wort für einen vorhandenen Begriff ist teurer als eine zweite Fundstelle für ein vorhandenes Wort."* Und `publishes nothing` **ist** das vorhandene Wort: es sagt schon genau das |

#### (b) Das Fach nach seiner eigenen Prüffrage benennen — **„ohne Nutzlast"**

| | |
|---|---|
| **dafür** | **das Protokoll stellt in der Fachspalte eine FRAGE** (*„Trägt er KEINE Nutzlast?"*), und die Beispiele dahinter sind Erläuterung. Der Name folgt der Frage statt einem der Beispiele. Er trifft alle elf statt neun, und **er nimmt der Gabelung den Boden** — bei dieser Lesart gibt es kein X. Kein neues Wort, keine Grammatik, kein Eintrag in der Wortschatztafel |
| **dagegen** | der Name ist länger und weniger anschaulich als „Zähler". *Ein Fach, das man nicht in ein Substantiv bekommt, ist ein Fach, über das man nachdenken muss* — und genau das ist hier erwünscht |

### Die Entscheidung: **(b)**, und **kein neues Sprachwort**

`SPRACHE.md` Teil II §1 sagt danach *„payload-free"* statt *„(counters)"*, und die
Akzeptanzzeile in §5 sagt *„a pairing, a payload-free access or a named seq case"*. **Die
Sprache ändert sich nicht** — `publishes nothing` heisst weiter `publishes nothing`, und
`pruefe-wortschatz.py` zählt weiter 195.

---

## 7. Was diese Entscheidungen NICHT kaufen

* **Nicht, dass eine fehlende Paarung jetzt gefunden wird.** `V009` findet **eine Gestalt**
  davon — die mit einem Tor. §2.2 rechnet vor, was die vollständige Regel kosten würde, und
  die Zahl ist 18.
* **Nicht, dass der Korpus die Regel misst.** Er enthält null schlichte Atomlesungen (§2.1).
  `V009` hängt an `beispiele/gift/301` und an nichts sonst — das steht als `gemessen_an` im
  Passregister und ist der schwächste Stand, den ein `Gemessen` haben kann.
* **Nicht, dass `V010` den fremden KERN sieht.** Es sieht den fremden **Namen**. Zwei Kerne
  in derselben Funktion sind für die Rufhülle ein Schreiber, und das bleibt so, solange es
  keine Aussage über Fäden gibt.
* **Nicht, dass die Umbenennung eine Messung ändert.** Die 39 Stellen des Befundes bleiben,
  wo sie sind; was sich ändert, ist die Lesart, unter der 0 statt 2 X herauskommen — und der
  Bericht führt beide Zahlen weiter nebeneinander.
* **Nicht, dass `seq`-Fälle jetzt gefunden werden.** `V009` sagt *„hier fehlt eine
  Erklärung"*, nicht *„hier gehört `seq` hin"*. Welche der drei Antworten richtig ist,
  entscheidet der Schreiber; der Prüfer erzwingt nur, dass eine dasteht.

---

## 8. Nachziehen

```bash
python3 messung/ordnung/tore.py          # Korpus: 20 Bindungen, 0 schlichte Lesungen
python3 messung/ordnung/ungeordnet.py    # 71 Lesungen geteilter Plaetze, 43 roh ungeordnet

# die beiden Giftproben -- je EIN Fehler, und sonst nichts
./target/debug/gabbro pruefe beispiele/gift/301-tor-ohne-paarung.gab    # V009
./target/debug/gabbro pruefe beispiele/gift/302-fremder-schreiber.gab   # V010

# und die Gegenrichtung: der ganze Korpus, 93 Dateien
for f in $(find beispiele messung passlogik programmlogik sonden -name '*.gab' \
           | grep -v /gift/); do ./target/debug/gabbro pruefe "$f"; done \
  | grep -cE 'V009|V010'                 # 0
```

**Gemessen am 2026-08-28 mit dem gebauten Prüfer:** 93 Korpusdateien, **0 `V009`, 0 `V010`**;
in den 287 Giftproben feuern die beiden neuen Kennungen ausschliesslich in `301` und `302`.
`cargo test`: 215 grün. Die beiden Mutationen (`kein-tor-wird-gebunden`,
`fremder-schreiber-egal`) werden von genau ihrer Giftprobe gefangen — von Hand nachgefahren,
weil der volle Mutationslauf an drei **vorgefundenen** toten Ankern in `emit.rs` gar nicht
erst anläuft.
