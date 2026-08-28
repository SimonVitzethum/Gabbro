# Die Absenkung — der Posten, den `PLAN-AUTONOM.md` §7 ausdrücklich aus dem Plan heraushält

*Gemessen am 2026-08-28. Jede Zahl nennt den Befehl, der sie nachrechnet. Gebaut wurde auf
`ki-pc-fisch-101:gabbro-L` und `gabbro-L-beweise`, gegen `master` @ `8476205`.*

> **Dies ist ein Entscheidungsdokument nach `PLAN-AUTONOM.md` §1.3 — mit EINER ausdrücklich
> benannten Abweichung, und sie steht in Abschnitt 4.** Punkt 3 des vorgeschriebenen Aufbaus
> lautet *„Die Entscheidung mit ihrem Grund"*. Diese Entscheidung fällt hier nicht. §7 sagt,
> warum: *„Wer anfängt, eine C-Semantik zu schreiben, hat die Entscheidung getroffen, ohne sie
> zu stellen."* Statt der Entscheidung stehen an ihrer Stelle **die Kriterien, die sie
> entscheiden würden, jedes mit der Messung, die es beantwortet** — und wo eine Messung heute
> schon vorliegt, steht sie daneben.
>
> *Eine Abweichung vom vorgeschriebenen Aufbau, die im Dokument benannt ist, ist etwas anderes
> als eine stille.*

---

## 1. Der Befund

### 1.1 `H = 5` ist seit heute **vollständig** die Absenkung

```bash
./instrumente/zaehle-pflichten.py --haengend
```

```
  je Fragment (verankert + Absenkung):
    F1   0 + 1 = 1
    F3   0 + 1 = 1
    F5   0 + 1 = 1
    F6   0 + 1 = 1
    F9   0 + 1 = 1

  verankert         0
  Absenkung         5   eine Zeile je Fragment, in `The tenth event`;
                        GEMESSEN sind F2, F4, F7, F8, F10
  ---------------------
  H                 5
```

**Nicht eine einzige verankerte Klempnereipflicht ist mehr offen.** Was von `H` übrig ist,
ist eine Zeile je Fragment mit demselben Inhalt: *das erzeugte C rechnet, was das Fragment
sagt* — an der Ausführung gemessen. `K100`s erstes Tor steht damit auf einem einzigen Posten,
und dieser Posten ist der hier.

### 1.2 `A8`: **welche** achtzehn — und die Zahl ist eine Handzählung von vor vierzehn Tagen

`dokumente/PLAN.md`:859 bucht `A8` als **„18 claims open"**. Die achtzehn sind auffindbar, und
sie stehen an genau einer Stelle: die Tabelle **„The complete conversion"** in
`dokumente/SPRACHE.md`, Kopfzeile 2617, Zeilen 2621–2638, letzte Spalte `lowering`.

```bash
sed -n '/^### The complete conversion/,/^---$/p' dokumente/SPRACHE.md | grep -c '^| [0-9]'
# 18
grep -n "Eighteen conversions" dokumente/SPRACHE.md
# 2663:* **Paper, not compiler.** Eighteen conversions on paper are eighteen claims about lowerability.
```

Das Dokument sagt es also selbst: *achtzehn Umwandlungen auf Papier sind achtzehn
Behauptungen über Absenkbarkeit.*

**Drei Befunde über die Zahl selbst, und alle drei gehören zum Gegenstand:**

| | |
|---|---|
| **Sie ist nie nachgerechnet worden** | eingeführt am 2026-08-14 (`df2fe7d`), seither nur übersetzt (`50f65a7`). `git log -S "claims open" -- dokumente/PLAN.md` findet keine Änderung der Zahl |
| **Kein Werkzeug zählt sie** | `grep -rn "claims open" dokumente/ instrumente/` liefert **eine** Fundstelle, und das ist die Buchung selbst. `zaehle-pflichten.py` zählt eine Absenkungsspalte, aber je Fragment mit Decke 10 — eine andere Größe |
| **`pruefe-zahlen.py` kann sie nicht einmal als unbewacht melden** | sein Reichweitenzähler verlangt eine **fett** gesetzte Zahl in einer Tabellenzelle; `A8`s Zelle schreibt `18 claims open` ohne Fettung. `sed -n '859p' dokumente/PLAN.md \| grep -c '\|\s*\*\*[0-9]'` → `0` |

> **Eine Behauptung, die niemand auflisten kann, ist keine Arbeitsmenge** — und eine, die kein
> Wächter sieht, ist auch keine Ratsche. Beides trifft hier zu.

### 1.3 Die erzeugten Formen, und für welche es einen Absenkungsbeweis gibt

```bash
ssh ki-pc-fisch-101 'cd gabbro-L && ./instrumente/pruefe-emission.sh 2>&1 | tail -5'
```

```
== EMISSION: ALL PASS -- 24 durchgestochen, 52 von 52 uebersetzen ==
  Und was das NICHT heisst: DURCHGESTOCHEN sind 24 -- erzeugt, uebersetzt,
  AUSGEFUEHRT und mit einer Handschrift verglichen. Die Regel darueber ist
  schwaecher: sie fragt nur, ob der C-Uebersetzer die Ausgabe annimmt.
```

**§7 behauptet: für keine erzeugte Form gibt es einen Absenkungsbeweis. Das war heute Morgen
richtig und ist es seit heute Nachmittag nicht mehr — an genau einer Form, und der Beweis
sagt, dass die Behauptung falsch ist.** Siehe Abschnitt 2; hier steht der Bestand.

| erzeugte Form | Schablone | Stand | Absenkungsbeweis |
|---|---|---|---|
| `table … count N` (Feld) | `table.absenkung` (S16) | bewiesen | **nein** — der Beweis handelt von der ZAHL, nicht von der Auslieferung |
| `ops insert` | `table.ops.erhaltung` (S6) | **getragen, unbewiesen** | nein |
| `ops remove` | dieselbe | **getragen, unbewiesen** | nein |
| `ops relabel` | dieselbe | **getragen, unbewiesen** | **seit heute, und er hat ZWEI Zweige** (`beweise/Absenkung_Parametrisch.thy`) |
| `option index into T` | `option.sonderwert` (S2) | **getragen, unbewiesen** | nein |
| `P(a: …, b: …)` (Verbundruf) | `verbund.konstruktor` (S19) | bewiesen | nein |
| `format` (Byteleser) | `format.roundtrip` (S12) | bewiesen | nein |
| `device`/`bank` | `device.konstruktor` (S14) | bewiesen | nein |
| `accumulates` | `accumulates.monoid` (S10) | bewiesen | nein |
| Baugatter (`when <const>`) | **keine** | — | nein, **und die behauptete Absenkung ist widerlegt** (§1.6) |
| `retires` | **keine** | — | nein |

```bash
ssh ki-pc-fisch-101 'cd gabbro-L && ./target/debug/gabbro schablonen | tail -8'
# -- 21 templates, 11 of them unproved, 10 machine-checked.
# --   of those CARRIED unproved (the compiler rests on them): 2
# --   of those PREMISES WITHOUT A PASS (tooth 3): 6 -- a proof nothing establishes.
```

**`L = 2`, und beide Getragenen sind die interessanten.** `option.sonderwert` hat eine
Theorie, die von sich selbst sagt, die Schablone bleibe unbewiesen; `table.ops.erhaltung` hat
vier Voraussetzungen, alle mit einem Leser — und was fehlt, ist genau der Schritt vom Modell
zum erzeugten C.

> **Ein getragener unbewiesener Satz ist etwas anderes als ein entworfener**, und das Register
> unterscheidet es an einer einzigen Stelle: `Stand::Getragen` gegen `Stand::Entworfen`.
> Neun Schablonen sind entworfen und kosten heute nichts. **Zwei sind getragen — auf sie
> stützt sich jeder Lauf des Übersetzers, jetzt.**

### 1.4 Die Bewegung aus `Table_Absenkung.thy`:36 — gemessen, und sie ist nicht die häufigste

`beweise/Table_Absenkung.thy`:35–36:

> *Ein C-Feld der Laenge `m` hat die gueltigen Indizes `{i. i < m}` — das ist die
> Sprachdefinition von C und keine Annahme dieses Beweises.*

Das ist eine **Bewegung**: eine Voraussetzung wird aus dem Beweis geschoben, indem sie zur
Definition von etwas anderem erklärt wird. Ausgezählt über alle vierzehn Theorien
(`beweise/*.thy`, jede ganz gelesen; gezählt werden Fundstellen im **Fließtext**, nicht
`assumes`-Zeilen):

| Gestalt | Zahl | Adressat |
|---|---:|---|
| **(a)** „das ist die Sprachdefinition von X" | 5 | C (2), Gabbro selbst (2), C11 6.7.3.1 (1) |
| **(b)** „das ist eine PRÄMISSE und keine Lücke" | 5 | niemand — als Preis benannt |
| **(c)** „das ist die Sache von `emit.rs` / des Erzeugers" | **21** | der Erzeuger |
| **(d)** „das ist die Sache des Prüfers / eines Passes" | 8 | Rust-Regeln |
| **(g)** „das ist die Axiomschicht / die Maschine / das Datenblatt" | 6 | Hardware, Speichermodell |
| **(h)** „das ist die Sache einer ANDEREN Schablone" | 5 | Nachbarbeweis |
| **Summe der Delegationen** | **50** | |
| **(f)** HYPOTHESE im Satz — die ehrliche Form, **getrennt gezählt** | 14 Stellen / 84 `assumes` | — |

```bash
grep -n "Sprachdefinition\|SPRACHENTSCHEIDUNG\|schliesst die SPRACHE aus\|C11 6.7.3.1" beweise/*.thy
grep -n "faellt in die Bruecke\|Dieselbe Bruecke" beweise/*.thy
grep -c "assumes" beweise/*.thy | awk -F: '{s+=$2} END {print s}'   # 94 (84 vor der neuen Theorie)
```

> **Das ist der Befund, um dessentwillen diese Zählung überhaupt gemacht wurde: an C wird
> VIERMAL delegiert, an den Erzeuger EINUNDZWANZIGMAL.** Die häufigste Bewegung im Ordner ist
> nicht *„das ist die Sprachdefinition von C"*, sondern **„das ist eine Aussage über `emit.rs`,
> und sie fällt in die Brücke"** — wörtlich viermal identisch wiederholt
> (`Table_Absenkung`:140, `Accumulates_Monoid`:227, `Verbund_Konstruktor`:128,
> `Format_Roundtrip`:165), und `Device_Konstruktor`:138 sagt selbst *„Dieselbe Bruecke wie bei
> jedem Eintrag dieses Registers"*.
>
> **Damit ist die Gabel aus §7 kleiner als sie aussieht.** Sie entscheidet vier Delegationen.
> Die einundzwanzig entscheidet sie nicht — die Brücke steht auf **jedem** Weg, und sie ist
> derselbe Bau.

### 1.5 `K100.4 stark`: was heute die Aufzählung ist — und sie ist an einer Stelle **blind**

`K100.4` ist als Weg (b) gebaut: `gabbro zeugnis <datei>` zählt je Übersetzungseinheit auf,
worauf die Übersetzung ruht — fünf Abschnitte: Annahmen, Schablonen, direkte Absenkung,
Gelöschtes, Fremdes. *„Es beweist die Übersetzung nicht; es zählt auf, worauf sie ruht."*

**Und genau diese Aufzählung sieht die neuesten erzeugten Formen nicht.** Zwei Dateien, ein
Zeilenunterschied:

```bash
# /tmp/mit.gab und /tmp/ohne.gab unterscheiden sich in EINER Zeile: `ops insert, remove, relabel;`
ssh ki-pc-fisch-101 'cd gabbro-L && \
  ./target/debug/gabbro emit /tmp/ohne.gab | wc -l && \
  ./target/debug/gabbro emit /tmp/mit.gab  | wc -l && \
  ./target/debug/gabbro emit /tmp/mit.gab  | grep -c "^static void Baum_" && \
  diff <(./target/debug/gabbro zeugnis /tmp/ohne.gab | tail -n +2) \
       <(./target/debug/gabbro zeugnis /tmp/mit.gab  | tail -n +2)'
```

```
26                        <- C-Zeilen ohne `ops`
73                        <- C-Zeilen mit `ops`
6                         <- drei erzeugte Operationen (Prototyp + Rumpf)
                          <- LEERER DIFF: die Zeugnisse sind IDENTISCH
```

Das Zeugnis meldet in beiden Fällen `1 templates (0 of them UNPROVED)` und nennt
`table.absenkung`. **`table.ops.erhaltung` — die Schablone, auf die diese siebenundvierzig
zusätzlichen C-Zeilen ruhen und die GETRAGEN UND UNBEWIESEN im Register steht — kommt im
Zeugnis nicht vor.**

```bash
grep -c 'table.ops.erhaltung' crates/gabbro-check/src/zeugnis.rs
# 0
```

**Und `UNZUGEORDNET` ist nicht gefallen.** Der Riegel dafür steht (`zeugnis.rs`:613: *„Kein
Auffangzweig. Ein Item, das hier nicht steht, ist keines, das der Erzeuger stillschweigend
mitnimmt"*) — aber er greift auf der Ebene der **Items**. `ops` ist eine Klausel INNERHALB
eines `table`, und das `table` hat seine Einordnung. *Der Erzeuger ist innerhalb eines schon
eingeordneten Items gewachsen, und der Wächter, der genau diesen Fall fangen sollte, sieht
ihn nicht.* Dieselbe Klasse wie `W16`.

> **`K100.4` schwach ist heute nicht die Aufzählung, für die es gehalten wird.** Es zählt auf,
> was die Zweitlesung kennt — und die Zweitlesung ist elf Tage jünger als ihr Gegenstand.

### 1.6 Die achtzehn heute — und mindestens eine ist nicht offen, sondern **widerlegt**

Nachgerechnet an Erzeuger und Korpus (§1.2 nennt die Fundstelle der Tabelle):

* **Nr. 4** *„`move_cap` — node relabelling"*, behauptete Absenkung **„pointer rehanging"**:
  **eingelöst.** `emit.rs::ops` erzeugt seit dem 2026-08-28 abends
  `T_relabel(T *t, uint32_t s, uint32_t p) { t->slots[s].elter = p; }` — und das ist wörtlich
  das Umhängen eines Zeigers. *Der Posten stand vierzehn Tage als Behauptung und ist gebaut,
  ohne dass `A8` es erfahren hat.*
* **Nr. 18** *„conditional compilation (335 `cfg` sites)"*, behauptete Absenkung **`#if`**:
  **widerlegt.** Gebaut ist ein Filter **vor** dem Erzeuger (`gatter.rs::ohne_gatter`), und
  `pruefe-emission.sh` sagt in seinem Kommentar aus, warum das kein Schönheitsfehler ist:
  *„Ein Gatter, das im C landet, ist kein Gatter — ein `#if` hätte den ganzen Block
  mitgeliefert und nur den Präprozessor darüber entscheiden lassen."* Gemessen:
  0 Gerüstnamen im Auslieferungs-C, 16 im Prüfbau-C, 39 Zeilen gegen 77.

```bash
ssh ki-pc-fisch-101 'cd gabbro-L && ./instrumente/pruefe-emission.sh 2>&1 | grep -A3 "Baugatter"'
```

> **Eine widerlegte Behauptung ist teurer als eine offene.** Eine offene sagt „das ist noch
> nicht gemacht"; eine widerlegte sagt etwas Falsches über etwas Fertiges — und `A8`s Zelle
> zählt beide als dieselbe Einheit. *Die achtzehn sind keine Arbeitsmenge, sie sind eine
> Mischung aus Arbeitsmenge, Erledigtem und Irrtum, und niemand hat sie getrennt.*

### 1.7 Und die drei jüngsten erzeugten Formen sind **nicht durchgestochen**

```bash
grep -c 'relabel' instrumente/pruefe-emission.sh        # 0
grep -ln "^    ops " beispiele/*.gab messung/fragmente/*.gab   # beispiele/47-ops-wortmenge.gab
```

**`ops` steht an genau einer Korpusstelle, und die ist unter den 24 Durchstichen nicht
dabei.** `insert`, `remove` und `relabel` werden erzeugt und übersetzt (sie sind unter den 52),
aber **nie ausgeführt und nie mit einer Handschrift verglichen** — genau die schwächere Aussage,
die `pruefe-emission.sh` in seiner eigenen Schlusszeile von der stärkeren trennt.

*Das ist die Zeile, an der Abschnitt 3 später hängt.*

---

## 2. Der Satz, den alle drei Wege brauchen — und was er gefunden hat

**Gebaut: `beweise/Absenkung_Parametrisch.thy`** (600 Zeilen, maschinell geprüft
2026-08-28 auf `ki-pc-fisch-101:gabbro-L-beweise`, 14 Theorien, 14 s Wanduhr).

§7 nennt die Lücke wörtlich: *„Dass `t->slots[s].elter = p;` die Funktion `umhaengen` IST,
steht in keinem Satz."* Der Satz steht jetzt — **parametrisch über der Zielsemantik**, also in
einer Gestalt, die unter allen drei Formen dieselbe ist.

### 2.1 Die sechs benannten Eigenschaften — das ist die fehlende Aufzählung

Keine von ihnen nennt C, und keine nennt eine Maschine.

| | Eigenschaft | wo sie herkäme |
|---|---|---|
| `E1` | **Rahmen** — ein Schreiben ändert genau einen Ort | C: Objektmodell + effektive Typen · Maschine: Adressarithmetik |
| `E2` | **Treffer** — was geschrieben wurde, liest sich zurück | C: die Zuweisung · Maschine: der Speicherbefehl |
| `E3` | **Zuweisung** — die eine Anweisung IST das Schreiben an den Elternort | **die Zeile, in der die Absenkung wohnt** |
| `E4` | **getrennt** — verschiedene Plätze, verschiedene Elternorte | C: **Sprachregel** · Maschine: **Lemma** |
| `E5` | **geschieden** — ein Elternort ist nie ein Belegungsort | dito |
| `E6` | **deutungstreu** — das Wort eines gültigen Index liest sich als dieser Index | `option.sonderwert` (S2), getragen und unbewiesen |

### 2.2 Der Befund: der Satz „das Erzeugte berechnet die Modellfunktion" ist **falsch**

| Satz | Aussage |
|---|---|
| `absenkung_am_belegten_platz` | das Erzeugte berechnet `umhaengen` — **nur am BELEGTEN Platz** |
| `absenkung_geht_am_freien_platz_auseinander` | am FREIEN Platz gehen sie **auseinander**: das Modell macht ihn belegt, das erzeugte C lässt ihn frei |
| `absenkung_relabel` | die ehrliche Fassung hat **zwei Zweige** |
| `relabel_erhaelt_wohlgeformt` | die **Invariante** senkt unbedingt ab — und ihre zwei Zweige halten aus **verschiedenen Gründen** |

**Der Erzeuger weiß es und schreibt es als Prosa in einen Kommentar** (`emit.rs`, `fn ops`):
*„Where that differs is a FREE `s`: the model makes it occupied, the C leaves it free … an
all-statement over a smaller set does not fall."* Das Argument stimmt — **und es ist ein
Argument über eine ERHALTUNG und nicht über eine Gleichheit.** Der Registereintrag daneben
sagt `relabel` = `umhaengen`, ohne Einschränkung; die Zeile ist um ein Wort zu stark und ist
im selben Lauf berichtigt worden.

**Zwei Gegenbeispiele, weil eine nie gefallene Voraussetzung eine Zierde ist (R11):**

* ohne `E4` teilen sich zwei Plätze ihr Elternfeld, und das Erzeugnis hängt **zwei** um, wo
  das Modell einen umhängt (`aliasbruch_bricht_die_absenkung`);
* ohne `E6` liegt der Sonderwert im Bereich, und der Platz wird still zur **Wurzel** —
  **`wohlgeformt` hält dabei weiter** (`sonderwert_bricht_die_absenkung`). *Das ist das
  Argument dafür, dass die Gleichheit die Erhaltung nicht ersetzt: die Erhaltung sieht diesen
  Bruch nicht.*

### 2.3 Woran die Parametrisierung **nicht** durchhält — die drei Nähte

§7 sagt, eine solche Stelle sei der wertvollste Befund. Hier stehen drei, und die zweite ist
die harte. Sie stehen ausgeschrieben im M-2-Abschnitt der Theorie.

1. **`E4`/`E5` sind auf den Wegen VERSCHIEDENE Arten von Aussage.** Unter einer
   Maschinensemantik ist `ort i = basis + versatz + i * groesse`, und `E4` fällt aus
   `groesse > 0` und `i, j < N` — **ein Lemma.** Unter einer C-Semantik ist `ort i` gar keine
   Zahl, sondern ein Ort im Objektmodell, und dass zwei Feldbezeichner verschiedene Orte
   bezeichnen, ist eine **Sprachregel**. *Der eine Weg beweist `E4`, der andere erbt sie.
   Beide bekommen den Satz — aber der Posten steht auf verschiedenen Seiten der Rechnung.*

2. **`lies` und `schreib` sind hier TOTAL, und das überlebt keine C-Semantik.** Ein Zugriff
   außerhalb des Feldes trifft auf einer Maschine eine andere Adresse, und man kann
   *hinschreiben*, welche. In C ist derselbe Zugriff **undefiniertes Verhalten** — kein Wert
   und kein Zustand, sondern die Auskunft, dass das ganze Programm keine Bedeutung hat,
   rückwirkend. *Ein partieller `schreib` wäre darstellbar; was NICHT darstellbar ist, ist die
   Rückwirkung.* **Damit ist schon die Signatur von `schreib` eine halbe Entscheidung.**
   **Die Parametrisierung hält für die KORREKTHEIT und bricht an der DEFINIERTHEIT.**

3. **`restrict` hat auf der Maschinenseite kein Gegenstück.** *„Diese beiden Zeiger überlappen
   nicht"* ist auf der Maschine eine **Prämisse**, aus der man rechnen darf; in C ist es ein
   **Versprechen**, das der Übersetzer ausnutzen darf und dessen Bruch wieder undefiniertes
   Verhalten ist. **Dieselbe Zeile Quelltext ist auf dem einen Weg eine Annahme und auf dem
   anderen eine Lizenz.** (`restrict.alleinzugriff`, S1 — von dieser Theorie nicht berührt,
   weil `relabel` einen einzigen Zeiger nimmt.)

---

## 3. Drei Formen, jede mit beiden Seiten

> **§7 stellt die Sache als Gabelung dar. Sie ist eine Dreiteilung** — und §1.3 verlangt
> *„mindestens zwei Formen"*, nicht *„genau zwei"*. Ein Dokument, das zwei gegeneinanderstellt,
> wo drei stehen, entscheidet die Gabelung, statt sie zu stellen.
>
> **Und §7s eigene Beschreibung von Form 2 wird hier berichtigt.** *„C streichen"* ist als
> Name **falsch**: der Weg streicht C nicht, er **ersetzt es durch eine Maschinensemantik je
> Architektur**, und zwar ohne fremde Vorlage. Der Satz *„man erbt nichts"* stimmt damit nur
> für die **Herkunft**, nicht für den **Aufwand** — statt einer geerbten Semantik steht dort
> eine selbstgeschriebene, je Architektur. *Das ist eine andere Rechnung als die, die §7s
> Formulierung nahelegt, und sie geht in die teure Richtung.*

### Form 1 — **C beweisen**: eine C-Semantik hinschreiben und die Absenkung dagegen beweisen

**Dafür**

* **`E3` wird einmal eingelöst, für alle Formen, aus einem Dokument.** Das ist die Zeile, in
  der die Absenkung wohnt (§2.1); jede weitere erzeugte Form erbt die Einlösung.
* **Die vier C-Delegationen hören auf, Delegationen zu sein** (§1.4): `Table_Absenkung`:36,
  `Table_Absenkung`:146–151, `Restrict_Alleinzugriff`:15–17 und :49 werden Sätze.
* **`restrict` bekommt seinen Träger.** S1 ist die einzige Schablone, deren Gegenstand
  wörtlich eine C-Regel ist (C11 6.7.3.1) — auf keinem anderen Weg hat sie einen Ort.
* **Die Form ist bekannt.** CompCert hat sie; man erfindet die Disziplin nicht, man wendet sie
  an. Und der ganze vorhandene Erzeuger (52 emittierende Dateien) bleibt, wie er ist.
* **Die Messapparatur bleibt.** 24 Durchstiche laufen durch `cc -Werror` bei `-O0` **und**
  `-O2` plus UBSan; die `-O0`/`-O2`-Differenz ist der Fingerabdruck von UB und fängt eine
  ganze Klasse. *Das ist geliehene Arbeit von Übersetzerbauern, und sie ist nicht klein.*

**Dagegen**

* **Man erbt C — und was man dabei zuerst erbt, ist die Undefiniertheit.** Naht 2 aus §2.3:
  jeder Satz trägt danach eine Definiertheitsprämisse, die **nicht** vom Programm handelt,
  sondern von der Sprache. *Die heutige Theorie kommt ohne aus, weil `schreib` total ist —
  und diese Totalität ist die Vereinfachung, die eine C-Semantik gerade wegnimmt.*
* **Die einundzwanzig Erzeuger-Delegationen fallen dadurch NICHT.** Eine C-Semantik sagt, was
  C bedeutet; sie sagt nicht, dass `emit.rs` dieses C herstellt. **Die Brücke bleibt vollständig
  stehen** (§1.4) — und sie ist mit 21 zu 4 der größere Posten.
* **`restrict` bleibt unangenehm, auch mit Semantik.** Eine Lizenz, deren Bruch das Programm
  bedeutungslos macht, ist etwas, das man einem Prüfer beweisen muss, bevor man sie ausspricht
  — nicht etwas, das man aus ihr folgert.
* **Der Ordner nennt selbst keine Zahl dafür.** `PLAN.md`: *„I do not have a defensible
  estimate, and an invented one would be worse than none."* Das ist keine Ausrede, es ist die
  einzige ehrliche Auskunft — **und sie gilt für Form 1 genauso wie für Form 2.**

### Form 2 — **C ersetzen**: ein Übersetzer, der direkt Binärcode erzeugt, mit einer Maschinensemantik je Architektur

**Dafür**

* **`E4`/`E5` werden Lemmas statt Sprachregeln** (Naht 1). Das ist gemessen und nicht
  vermutet: `aliasbruch_bricht_die_absenkung` zeigt, was ohne sie passiert, und auf der
  Maschinenseite fällt sie aus `groesse > 0` und `i, j < N`.
* **Keine geerbte Undefiniertheit.** Ein Zugriff außerhalb des Feldes trifft *irgendeine*
  Adresse, und man kann hinschreiben, welche. Die ganze Prämissenklasse aus Naht 2 entfällt —
  *und das ist der einzige Posten, bei dem Form 2 strukturell billiger ist und nicht nur
  anders.*
* **`restrict` verschwindet als Begriff** und bleibt als Prämisse übrig. Prämissen kann dieser
  Ordner tragen — er tut es an 94 `assumes`-Zeilen.
* **`aarch64` ist versiegelt** (`CLAUDE.md`: *„blockiert — Abstammung", kein dritter Anlauf*).
  **Unter dem Siegel heißt „je Architektur" heute: EINE.** *Das ist die einzige Stelle im
  ganzen Ordner, an der die Versiegelung ein Aktivposten ist und kein Verlust.*
* **Das Zeugnis hat schon die richtige Gestalt.** `gabbro zeugnis` ist als *„ein bewiesener
  Prüfer je Übersetzung"* gedacht; nur seine Zweitlesung hinkt (§1.5).

**Dagegen**

* **„Man erbt nichts" stimmt nur für die Herkunft.** Statt einer geerbten Semantik steht dort
  eine **selbstgeschriebene** — und niemand in diesem Ordner hat je eine geschrieben. Form 1
  erbt ein Dokument mit vierzig Jahren Fehlerkorrektur; Form 2 schreibt eines ohne.
* **Der Verlust von `cc` ist der Verlust der MESSAPPARATUR, nicht nur des Ziels.** Die 24
  Durchstiche, die `-O0`/`-O2`-Differenz, UBSan, `-Werror`, der Binder, die
  `.gabi`-Bibliothekskette — alles davon ist C-Gerät. **Wer C streicht, streicht die einzige
  Stelle, an der dieser Ordner heute *Ausführung* gegen *Handschrift* hält.** Und das ist
  genau die Stelle, von der `pruefe-emission.sh` sagt, sie mache die anderen drei erst zu
  einer Aussage.
* **Der ganze vorhandene Erzeuger ist ein C-Erzeuger.** 52 emittierende Dateien, `emit.rs` mit
  1634 deutschen Kommentarzeilen allein, die ABI-Kette, die Lizenzzeile im erzeugten C.
* **Die einundzwanzig Erzeuger-Delegationen fallen auch hier nicht.** Dieselbe Brücke, nur mit
  einem anderen Ufer.

### Form 3 — **Zeugenpaare je Absenkung, wegwerfbar**: die Behauptung wird prüfbar, ohne dass eine Semantik hingeschrieben wird

Statt einer Semantik, gegen die bewiesen wird, je Absenkung ein **Zeugenpaar**: ein
Beleg dafür, dass die behauptete Absenkung tut, was sie behauptet, und ein Beleg dafür, dass
sie es nicht mehr tut, wenn man sie beschädigt. Die Zeugen sind **wegwerfbar** — kein Bestand,
der gepflegt wird, sondern ein Beleg je Lauf.

**Dafür**

* **Die Form existiert schon, und sie ist gemessen.** `pruefe-emission.sh::lauf` nimmt genau
  ein Zeugenpaar entgegen:

  ```bash
  lauf() {   # $1 Name  $2 Quelle  $3 Treiber  $4 Erwartet  $5 Gift-sed  $6 Zeugnis
  ```

  `$4` ist der positive Zeuge (die Ausführung ergibt *das*), `$5` der negative (ein `sed`, das
  das erzeugte C beschädigt — das Ergebnis **muss** sich ändern). **24 solche Paare stehen
  heute im Baum.** Form 3 ist keine neue Maschine, sie ist die Verallgemeinerung einer
  vorhandenen von *je Übersetzungseinheit* auf *je Absenkungsbehauptung*.
* **Die achtzehn hören auf, Behauptungen zu sein, ohne dass die Richtungsentscheidung fällt.**
  Und das ist keine Vermutung: **Nr. 18 ist heute schon widerlegt** (§1.6), und die
  Widerlegung hat keine Semantik gekostet — sie hat einen Blick in `gatter.rs` gekostet. Ein
  Zeugenpaar hätte sie am ersten Tag gefunden.
* **Es ist der einzige der drei Wege, der die Gabel STEHEN LÄSST.** Wer ihn geht, hat nichts
  entschieden — und das ist hier ein Vorzug und kein Mangel, weil die Entscheidung heute nicht
  informiert getroffen werden kann.
* **Er ist heute unterversorgt, und die Lücke ist beziffert.** `ops` steht an **einer**
  Korpusstelle und ist **nicht** durchgestochen (§1.7). Die drei neuesten erzeugten Formen
  haben null Zeugen. *Der billigste nächste Schritt dieses ganzen Dokuments liegt hier.*
* **Der Satz aus Teil 2 sagt einem Zeugenpaar, WAS es bezeugen soll.** `E1`–`E6` sind sechs
  prüfbare Aussagen, und `absenkung_geht_am_freien_platz_auseinander` sagt, dass der freie
  Platz der Fall ist, den man anfassen muss. *Ohne den Satz ist ein Zeugenpaar ein Beispiel;
  mit ihm ist es eine Probe.*

**Dagegen**

* **Kein `K100.4 stark`, und `K100.4` sagt es selbst.** *„Ein Zeugnis über DIESE Übersetzung
  ist keine Aussage über ALLE Eingaben … dies ist die aufzählende Vorstufe davon, und sie ist
  als Vorstufe benannt."* Ein Zeuge je Lauf ist kein maschinengeprüftes Zeugnis je
  Übersetzung. **Das ist bestätigt und nicht übernommen: es steht im Werkzeug.**
* **Ein Zeugenpaar kann widerlegen, nicht bestätigen — und das ist heute messbar.** Die
  Abweichung am freien Platz (§2.2) steht seit dem Vormittag des 2026-08-28 im Baum;
  `pruefe-emission.sh` meldet `ALL PASS` mit 24 Durchstichen. Sie ist von einem **Satz**
  gefunden worden, nicht von einer Probe. *Ein Zeugenpaar über `relabel`, das nur belegte
  Plätze anfasst, wäre grün — und hätte nichts gesagt.*
* **Wegwerfbar ist der Zeuge, nicht seine Vorschrift.** Der negative Zeuge in
  `pruefe-emission.sh` ist ein `sed` auf erzeugtem C
  (`s/\.erstes_kind; _h1 = false/.elter; _h1 = false/`). Ändert der Erzeuger seine Ausgabe,
  greift das `sed` ins Leere und die Probe wird **still** wertlos — **dieselbe Klasse wie die
  drei toten Anker in `emit.rs`, und die ist heute nachweisbar**: Schritt 0 hat sie geheilt,
  `./instrumente/mutiere-pruefer.py --anker` meldet jetzt `332 von 332`. *Vorher meldete er
  `FEHLT` und der Mutationslauf lief gar nicht an.* **Wegwerfbarkeit ist eine Eigenschaft des
  Zeugen und keine des Wächters, der ihn fordert.**
* **Die Vertrauensfläche schrumpft um keine Zeile.** `L` bleibt 2, die einundzwanzig
  Erzeuger-Delegationen bleiben einundzwanzig, `H` bleibt 5.

---

## 4. Statt der Entscheidung: **die Kriterien, die sie entscheiden würden**

> **Hier weicht dieses Dokument vom vorgeschriebenen Aufbau ab, und die Abweichung ist der
> Punkt.** §1.3 verlangt an dieser Stelle *„die Entscheidung mit ihrem Grund"*. Diese
> Entscheidung gehört dem Menschen — §7 sagt, warum: wer anfängt, eine der beiden Semantiken
> zu schreiben, hat sie getroffen, ohne sie zu stellen. **Der Riegel gilt in beide Richtungen:
> eine Maschinensemantik hinzuschreiben ist dieselbe Handlung wie eine C-Semantik
> hinzuschreiben.**
>
> Es stehen daher **sechs Kriterien**, jedes mit der Messung, die es beantwortet — und drei
> davon sind heute schon beantwortet.

### K1 — Wie groß ist die Zielsemantik-Fläche gegen die Brückenfläche?

**Heute beantwortet:** 4 zu 21 (§1.4). Die Gabel entscheidet vier Delegationen; die Brücke
steht auf jedem Weg und ist der fünffach größere Posten.

**Was das Kriterium entscheidet:** hält das Verhältnis über alle erzeugten Formen, dann ist
die Semantikfrage **nicht die erste Entscheidung**, sondern die zweite — und die erste heißt
*wie wird die Brücke gebaut*, mit derselben Antwort auf allen drei Wegen.

**Die Messung, die es abschließt:** den parametrischen Satz aus Teil 2 auch für `insert` und
`remove` schreiben und die benannten Eigenschaften **danach sortieren, ob sie eine Aussage
über die Zielsprache oder eine über den Erzeuger sind.** *Bei `relabel` sind es 6 zu 0 — und
das ist genau die falsche Zahl, um daraus etwas zu schließen, weil `E3` allein die ganze
Erzeugerseite trägt.*

### K2 — Hält die Parametrisierung über alle erzeugten Formen, oder bricht sie an derselben Naht?

**Heute halb beantwortet:** für `relabel` hält sie für die Korrektheit und bricht an der
Definiertheit (Naht 2, §2.3). Für `insert`, `remove`, den Verbundruf, `format` und das
Baugatter ist sie **ungemessen**.

**Was das Kriterium entscheidet:** bricht sie bei einer zweiten Form an **derselben** Naht,
dann ist C's Undefiniertheit der bezifferte Preis von Form 1, und Form 2 hat zum ersten Mal
ein Argument, das nicht aus dem Bauch kommt. Bricht sie an einer **anderen** Naht, ist das
eine dritte Stelle, an der die Wege auseinandergehen — und jede davon ist mehr wert als eine
Schätzung.

**Die Messung:** `insert` ist die nächste, und sie ist billig — zwei Anweisungen statt einer,
also **eine siebte Eigenschaft: die Hintereinanderausführung.** Ob die sich parametrisch
hinschreiben lässt, ohne eine Auswertungsreihenfolge festzulegen, ist die Frage, an der Naht 2
ein zweites Mal zieht.

### K3 — Was kostet der Verlust von `cc`?

**Heute beantwortet, und die Antwort ist unbequem:** 24 Durchstiche, zehn Stufen je Lauf,
`-Werror` bei `-O0` und `-O2`, UBSan, Binder, `.gabi`-Kette — **das ist die einzige Stelle,
an der dieser Ordner Ausführung gegen Handschrift hält**, und sie ist vollständig C-Gerät.

**Was das Kriterium entscheidet:** Form 2 muss nicht nur ein Ziel ersetzen, sondern eine
Falsifikationsapparatur. *Ein Ordner, dessen Messgerät verschwindet, misst das Folgende ohne
Messgerät* — genau die Klasse, gegen die Schritt 0 dieses Plans steht.

**Die Messung, die es schärft:** `pruefe-emission.sh` durchgehen und je Stufe entscheiden, ob
sie eine Aussage über das PROGRAMM ist oder eine über `cc`. Die erste Sorte überlebt Form 2,
die zweite nicht. *Der Verdacht nach einem Durchgang: Stufe 1b (Bitgleichheit), Stufe 4
(Ergebnisvergleich) und Stufe 8 (verfälschtes C fällt) überleben; Stufen 3, 5, 9, 10 nicht.*

### K4 — Findet ein Zeugenpaar, was ein Satz findet?

**Heute beantwortet, und die Antwort ist NEIN — mit einem Vorbehalt, der zählt.** Die
Abweichung am freien Platz stand seit dem Vormittag im Baum, `pruefe-emission.sh` meldete
`ALL PASS`, und ein Satz hat sie am Nachmittag gefunden.

**Der Vorbehalt:** das ist heute keine Aussage über Zeugenpaare, sondern über ihre **Deckung**
— `ops` ist an null Stellen durchgestochen (§1.7). *Ein Zeuge, den es nicht gibt, ist kein
blinder Zeuge.*

**Die Messung, die es entscheidet:** einen Durchstich für `beispiele/47-ops-wortmenge.gab`
bauen — er ist billig, er fehlt ohnehin, und er beantwortet die Frage in beide Richtungen.
**Findet er die Abweichung am freien Platz von selbst, ist Form 3 stärker als sie hier
dasteht. Findet er sie nur, weil der Satz aus Teil 2 sagt, wo man hinsehen muss, dann ist
Form 3 kein Ersatz für einen Satz, sondern seine Ausführung** — und das entscheidet, ob sie
eine dritte Form ist oder eine Ergänzung zu den ersten beiden.

### K5 — Wie viele der achtzehn sind heute noch Behauptungen?

**Heute unvollständig beantwortet:** mindestens eine ist **eingelöst** (Nr. 4), mindestens eine
ist **widerlegt** (Nr. 18). Die übrigen sechzehn sind nicht nachgerechnet.

**Was das Kriterium entscheidet:** ist die Zahl seit dem 2026-08-14 stark gefallen, dann ist
`A8` nicht die Größe, die §7 unterstellt, und die Entscheidung ist kleiner als sie aussieht.
Stehen noch fünfzehn, dann ist sie es.

**Die Messung:** die achtzehn Zeilen einzeln gegen `emit.rs` halten — je Zeile drei Fragen:
existiert die Form, senkt der Erzeuger sie ab, **stimmt die behauptete Absenkung mit der
gebauten überein**. Nr. 18 zeigt, dass die dritte Frage die tragende ist.

**Und ein Riegel, der aus dieser Messung fällt, unabhängig vom Ausgang:** die achtzehn
brauchen einen Wächter. Heute zählt sie niemand, und `pruefe-zahlen.py` kann sie nicht einmal
als unbewacht melden (§1.2).

### K6 — Wie viele Architekturen hat Form 2 wirklich zu bezahlen?

**Heute beantwortet:** **eine.** `aarch64` ist versiegelt (*„blockiert — Abstammung"*, kein
dritter Anlauf), `x86_64` ist die Messbasis.

**Was das Kriterium entscheidet:** *„eine Maschinensemantik je Architektur"* liest sich wie
ein unbegrenzter Posten und ist unter dem heutigen Siegel ein einmaliger. **Das ist der
einzige Punkt, an dem Form 2s Preis systematisch überschätzt wird** — und er gehört genannt,
weil das Dokument sonst „C streichen" mit „zu teuer" abtäte, und *ein Dokument, das das tut,
hat nichts entschieden und nichts vorbereitet.*

**Die Gegenrechnung, die dazugehört:** das Siegel ist eine Entscheidung über die Herkunft
eines Codebestands, keine über die Zukunft der Sprache. Wer Form 2 wählt, weil heute eine
Architektur zählt, hat die Portabilität stillschweigend mitentschieden — und **das** ist die
Stelle, an der Form 2 eine zweite Entscheidung enthält, die niemand gestellt hat.

---

## 5. Was die Entscheidung NICHT kauft — für alle drei Richtungen getrennt

### Form 1 („C beweisen") kauft nicht

* **Die Brücke.** 21 der 50 Delegationen adressieren `emit.rs`; eine C-Semantik berührt keine
  davon. *Sie sagt, was C bedeutet, nicht dass dieses C erzeugt wurde.*
* **`H = 0`.** Die fünf offenen Zeilen verlangen *„das erzeugte C rechnet, was das Fragment
  sagt", an der Ausführung gemessen* — eine Semantik rechnet nicht.
* **`L → 0`.** `option.sonderwert` und `table.ops.erhaltung` bleiben getragen und unbewiesen,
  bis jemand die Auslieferung beweist, nicht die Sprache.
* **Die 24 Durchstiche werden keine Beweise.** Sie bleiben, was sie sind, und die Schlusszeile
  von `pruefe-emission.sh` bleibt wörtlich richtig.

### Form 2 („C ersetzen") kauft nicht

* **Freiheit von einer Semantik.** Es kauft eine **selbstgeschriebene**. Der Unterschied ist
  die Herkunft, nicht der Umfang — und ohne fremde Vorlage geht die Rechnung in die teure
  Richtung.
* **Die Brücke.** Dieselben 21, nur mit einem anderen Ufer.
* **Die Messapparatur.** Sie **verliert** sie (K3). Das ist der einzige Posten, bei dem eine
  der drei Formen etwas Vorhandenes zerstört, statt nur etwas Neues zu verlangen.
* **Portabilität.** Unter dem heutigen Siegel kostet sie eine Architektur; ohne das Siegel
  kostet sie eine je Ziel, und das Siegel ist widerrufbar.

### Form 3 („Zeugenpaare") kauft nicht

* **`K100.4 stark`.** Ein Zeuge je Lauf ist kein maschinengeprüftes Zeugnis je Übersetzung —
  und das steht nicht als Vermutung hier, sondern als Selbstauskunft des Werkzeugs.
* **Eine kleinere Vertrauensfläche.** `L` bleibt 2, `H` bleibt 5, die 21 bleiben 21.
* **Den Satz.** Und das ist der Posten, den dieses Dokument am schärfsten belegen kann: die
  einzige heute bekannte Abweichung zwischen erzeugtem C und Modell ist von einem **Satz**
  gefunden worden, während `ALL PASS` danebenstand.
* **Die Entscheidung.** Es **verschiebt** sie — und das ist genau seine Aufgabe. Der Preis
  einer Verschiebung ist nur dann null, wenn sie befristet ist. *Eine unbefristete Verschiebung
  ist eine Entscheidung mit einem anderen Namen.*

---

## 6. Was in diesem Lauf ausdrücklich NICHT getan wurde

* **Keine C-Semantik.** Keine Auswertungsreihenfolge, kein Speichermodell, kein
  Aliasingregelwerk, kein `volatile`, kein Ganzzahlüberlauf.
* **Keine Maschinensemantik.** Der Riegel gilt in beide Richtungen; die Gegenbeispiele in
  `Absenkung_Parametrisch.thy` arbeiten über einem Zustand, der eine Abbildung von Zahlen auf
  Zahlen ist, und die Theorie sagt an Ort und Stelle, dass das **keine** Maschinensemantik ist.
* **Keine Schablone geschoben.** `L` steht unverändert bei 2, `table.ops.erhaltung` bleibt
  `Getragen`. K100s zweites Tor ist nicht berührt.
* **Kein `insert`, kein `remove`.** Der parametrische Satz steht für `relabel` und für sonst
  nichts. `insert` verlangt eine siebte Eigenschaft (die Hintereinanderausführung), und die ist
  der nächste Ort, an dem Naht 2 zieht.
* **Die achtzehn sind nicht einzeln nachgerechnet.** Zwei sind es (Nr. 4, Nr. 18), und sie
  reichen, um zu zeigen, dass die Zahl eine Mischung ist. *Sechzehn stehen offen, und das ist
  K5.*
