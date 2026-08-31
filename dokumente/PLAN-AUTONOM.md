# Der autonome Plan — zwei Bahnen, sieben Schritte

*Geschrieben am 2026-08-28, nach sieben Bauten an einem Tag. **Er ist so geschnitten, dass
zwei Agenten ihn nebeneinander abarbeiten können, ohne sich in die Quere zu kommen** — und
jeder Schritt ist so geschrieben, dass ein Agent ihn ohne Rückfrage ausführen kann.*

> **Was dieser Plan NICHT enthält, und der Grund steht unten in §7:** die Absenkung. Weder A8
> noch die Brücke vom Modell zum erzeugten C. *Das ist kein Vergessen — es ist der eine
> Posten, der nicht in Tagen gerechnet wird, und ein Plan, der ihn zwischen Grammatikzeilen
> einreiht, hat ihn falsch dargestellt.*

---

## 0. Der Stand, gegen den geplant wird

Alles am 2026-08-28 gemessen. **Die Zahlen mit `*` sind Ratschenmarken — sie stehen im
Werkzeug und werden dort gelesen, nicht von hier abgeschrieben.**

```
Rumpfkanal        89 von 273 Routinen · ohne die 92 Fremdruempfe: 89 von 181   (49 %)
Schablonen        21, davon 11 unbewiesen · L = 2 getragen · Zahn 3 = 6
«B»-Luecken       11 offen von 41 gefuehrten                    (30 geschlossen)
Emission          ALL PASS -- 24 durchgestochen, 52 von 52 uebersetzen
Anker             323 von 326    (die drei toten liegen in `emit.rs`)
Testsammlungen    15, alle gruen
```

| Ratsche | Werkzeug | heute\* |
|---|---|---|
| Kennungen ohne Satz | `pruefe-saetze.py` | `MARKE = 45` |
| hängende Prämissen (Zahn 3) | `pruefe-schablonen.py` | `MARKE = 6` |
| emittierende Dateien | `pruefe-emission.sh` | `MARKE_EMIT = 52` |
| deutsche Kommentarzeilen | `pruefe-englisch.py` | Prüfer 7910, Instrumente 1072 |

**Fünf Wächter sind vorgefunden rot und gehören niemandem aus den heutigen Bauten:**
`pruefe-klauseln.py` · `pruefe-vergabe.py` · `pruefe-todo.py` · `pruefe-zahlen.py` ·
`pruefe-zitate.py`. *Schritt 0 räumt sie ab; bis dahin sind sie kein Befund gegen einen Bau.*

---

## 1. Die Regeln, die für JEDEN Schritt gelten

**Ein Agent, der diese Liste nicht zuerst liest, produziert einen Lauf, den jemand von Hand
nachrechnen muss.** Sie ist die Zusammenfassung dessen, was heute siebenmal getragen hat.

### 1.1 Rechnen und Übertragen

* **Alles, was rechnet, läuft per SSH auf `ki-pc-fisch-101`** (`CLAUDE.md`). `cargo build`,
  `cargo test`, `pruefe-emission.sh`, `pruefe-luecken.py`, `isabelle build`.
* **Jede Bahn hat ihr EIGENES Serververzeichnis.** Bahn A: `gabbro-A`. Bahn B: `gabbro-B`.
  Schritt 0: `gabbro-0`. **Niemals `gabbro-baum` oder das Verzeichnis der anderen Bahn** — am
  2026-08-21 hat eine Kollision zwei grüne Testsammlungen rot gemeldet, und das war kein
  Befund.
* **`rsync -rlpgoD --delete`, NICHT `-a`.** Der Grund steht in `CLAUDE.md` und ist kein
  Schönheitsfehler: `-a` erhält Zeitstempel, und `cargo` entscheidet Aktualität nach
  Zeitstempel — die Folge ist ein Bau aus einer Mischung, der plausibel aussieht.
* **Der Arbeitsbaum steht vor Laufbeginn auf `master`** (`--ff-only`). Ein Zweig, der drei
  Commits zurückliegt, misst gegen einen Stand, den es nicht mehr gibt.
* **Isabelle**: `rsync -a beweise/ ki-pc-fisch-101:gabbro-<bahn>-beweise/` und dort bauen.
  **Kein AFP.** Lokal nicht — der lokale Wachhund macht aus einem Speicherabbruch etwas, das
  wie ein gescheiterter Beweis aussieht.

### 1.2 Vor dem ersten Bau: zwei Fragen, immer

**W24 — parst die naheliegende Form heute schon?** Schreib sie hin, lass sie durch den
**unveränderten** Prüfer laufen. Parst sie? Und wenn nein: fällt sie am Parser, oder an etwas
dahinter? *Das hat am 2026-08-28 viermal die Frage umgedreht — dreimal fehlte nicht die Form,
sondern der Gerufene oder ein Leser, und zweimal war der Lückeneintrag selbst falsch.*

**W23 — enthält meine Grundgesamtheit meine eigenen Proben?** `beispiele/gift/` gehört in
**keine** Bedarfsmessung, nur in Trefferzählungen. Wo beide Töpfe gebraucht werden, getrennt
ausweisen, nicht summieren.

### 1.3 Wenn eine Entscheidung ansteht

**Erst ein Entscheidungsdokument nach `messung/`**, dann der Bau. Aufbau, verbindlich:

1. **Der Befund**, mit dem Befehl, der ihn nachrechnet.
2. **Mindestens zwei Formen, beide Seiten je Form** — dafür *und* dagegen, je Form.
3. **Die Entscheidung mit ihrem Grund**, und der Grund ist der Begriff, nicht der Preis.
4. **Was die Entscheidung NICHT kauft.**

Vorbilder, alle vom 2026-08-28: `messung/OPS-ERZEUGER.md` · `messung/BAUGATTER.md` ·
`messung/OPS-RELABEL.md` · `messung/ZWEI-ORTE.md` · `messung/BOOT-S3.md`.

**Kein neues Wort ohne Prüfung gegen `messung/SCHLEIFENINVARIANTE.md` §3:** *ein zweites Wort
für einen vorhandenen Begriff ist teurer als eine zweite Fundstelle für ein vorhandenes Wort.*
Ein neues Wort kostet `kw.rs`, die Tabelle in `SYNTAX.md` (~Zeile 100), `pruefe-wortschatz.py`,
`tests/wortschatz.rs` und die Terminalzählung — und `tests/wortschatz.rs` fällt sofort, wenn
die Tabelle fehlt.

**Regel A: kein Konstrukt ohne gemessenen Bedarf.** Wenn die Messung zeigt, dass der Bedarf
fehlt, ist die **benannte Absage** das Ergebnis und kein Fehlschlag.

### 1.4 Was jeder Bau mitbringt

* **Eine Kennung** je Regel. Freie Kennung mit `./instrumente/pruefe-kennungen.py` suchen.
* **Eine Giftprobe** in `beispiele/gift/`, erste Zeile `-- erwartet: <Kennung>`.
  **Nummernbereiche, damit die Bahnen sich nicht überschreiben:**
  Schritt 0: 361–399 · **Bahn A: 401–449** · **Bahn B: 451–499** · Schritt 6: 501–.
  *Eine Regel, die nie hat nein sagen sehen, ist eine Zierde (R11).*
* **Ein `Satz` in `crates/gabbro-check/src/saetze.rs`**, mit `vorbehalt` — was sie NICHT
  prüft, ausgeschrieben. Sonst steigt `pruefe-saetze.py` über seine Marke.
* **Eine Korpusstelle** in `beispiele/`, die die neue Form zum ersten Mal schreibt.
* **Eine Mutation** in `instrumente/mutiere-pruefer.py`, wenn die Regel eine Fläche hat, die
  still ausfallen kann. Der volle Lauf ist ab Schritt 0 wieder möglich; bis dahin die Mutation
  von Hand fahren und das Ergebnis melden.
* **Grammatik in `dokumente/SYNTAX.md`**, wenn die Form neu ist.

### 1.5 Ratschen

**Eine Ratsche, deren Marke man hochzieht, wenn sie klemmt, ist keine.** Fällt eine, wird die
Ursache geheilt — nicht die Marke bewegt. **Fällt sie in die gute Richtung, ist das trotzdem
ein Befund**, und die Marke wird mit ausgeschriebenem Grund nachgezogen.

**K100s zweites Tor:** eine Schablone darf nicht von *entworfen* auf *getragen* wandern, ohne
dass der Beweis vorher steht. Wenn ein Bau eine Erzeugerpflicht schafft, gehört sie ins
Register (`crates/gabbro-check/src/schablonen.rs`) — und wenn der Übersetzer sich darauf
stützt, **erst der Isabelle-Lauf.** Präzedenzfall: `verbund.konstruktor`, *„so kam der Beweis
zuerst"*.

### 1.6 Zusammenführen ohne Kollision

**Diese Dateien berührt jede Bahn:** `saetze.rs` · `mutiere-pruefer.py` · `kw.rs` ·
`SYNTAX.md` · `pruefe-schablonen.py`. **Regel: immer ANS ENDE der jeweiligen Liste anfügen,
nie in die Mitte.** Dann sind die Konflikte additiv und in einer Minute aufzulösen.

**Bahn A fasst nicht an:** `lean.rs`, `programmlogik/`, `m1.rs`.
**Bahn B fasst nicht an:** `m3.rs`, `geraete*`, `abi.rs`, `phasen.rs`.

### 1.7 Die Abnahme, am Ende JEDES Schritts — **EIN Befehl**

```bash
cargo test                     # alle Sammlungen gruen
./instrumente/abnahme.py       # ALLE Waechter, je Waechter ein Urteil
```

`abnahme.py` liest das **Verzeichnis** (`instrumente/pruefe-*`, `mutiere-*`, `zaehle-*`) und
fährt jeden Wächter. Je Wächter steht da: **grün · ROT · TEILMESSUNG · ABBRUCH · NICHT
FAHRBAR · ausgelassen**. Daneben steht die **Arbeitsmenge** — wie viele gefahren wurden —,
und *ein Lauf, der null fährt, ist rot* (W17).
`--voll` nimmt die vier teuren dazu (`mutiere-pruefer.py`, `pruefe-beweise.sh`,
`pruefe-emission.sh`, `pruefe-luecken.py`); der Schnellauf **nennt sie, statt sie
wegzulassen**, und fährt von `mutiere-pruefer.py` die kostenlose Hälfte `--anker` mit.

> **Und seit dem 2026-08-31 steht die Arbeitsmenge nicht mehr allein da.** Sie zählt
> Wächter, und der Baum ist nicht in Wächtern gemessen: der Schnelllauf fuhr *45 von 49
> Wächtern* und sah dabei **höchstens 45 der 92 gefährlichen Stellen** — 45 davon liegen in
> `pruefe-emission.sh` allein. Die zweite Zeile nennt jetzt beides, und jeder ausgelassene
> Wächter steht mit seinem Gegenstand daneben (101 Übersetzungseinheiten, 372 Mutationen,
> 15 Verdrehungen, 15 Theorien). *Grün mit benannter Lücke bleibt grün — es sagt nur, wie
> viel dieses Grün abdeckt.* Ausgeschrieben in `messung/RUECKLAUFWERTE.md`.

> **Bis zum 2026-08-30 stand hier eine Liste mit elf Namen, und es gab 26 Wächter.** Sieben
> standen in KEINER Liste und in keinem Sammellauf — `pruefe-abstieg.py`,
> `pruefe-aufloesung.py`, `pruefe-reichweite.py`, `pruefe-widerruf.py`,
> `pruefe-lean-beweis.sh`, `pruefe-lean-programm.sh`, `pruefe-p6-beweis.sh`. **Zwei rote
> Ratschen liefen darunter zwei Tage lang durch vier Zusammenführungen.**
>
> *Ein Wächter, den niemand fährt, ist von einem, den es nicht gibt, nicht zu unterscheiden.*
> **Darum steht hier kein Name mehr:** eine Liste veraltet lautlos, ein Verzeichnis nicht. Ein
> neuer Wächter ist am Tag seiner Entstehung in der Abnahme, ohne dass jemand daran denkt.

**Ein Absturz ist keine Absage.** `pruefe-wortschatz.py` stirbt ohne Dateiargument mit
`IndexError` und sieht dabei aus wie ein Befund — `abnahme.py` stellt das Argument aus
`pruefe-waechter.py:ARGUMENTE` und sagt, dass es das getan hat. Ein Wächter, der abstürzt und
**nicht** dort angemeldet ist, ist ROT: *ein angemeldetes Loch hat einen Namen, ein
unangemeldetes ist eine Behauptung.*

**Und der Bericht nennt vier Dinge, immer:** was gebaut wurde · die Giftproben **mit ihrer
gemessenen Ausgabe** · die Abnahmezahlen · **und ausdrücklich, was NICHT gebaut wurde und
warum.** Der letzte Punkt ist der wertvollste; heute stand die härteste Pointe jedes Laufs
darin.

### 1.8 Wenn ein Schritt sich als Berichtigung entpuppt

**Das ist der gute Fall und kein Fehlschlag.** Am 2026-08-28 waren drei von zehn Posten keine
Bauten, sondern falsche Einträge («B17», `breaking`, `when`). Dann gilt:

* Die falsche Zeile wird **berichtigt, nicht übermalt** — mit Datum, mit der alten Fassung
  durchgestrichen daneben.
* **Eine Zahl, die durch eine Berichtigung fällt, ist keine Arbeit** und wird so gebucht.
  Ebenso in die andere Richtung: eine Berichtigung, die eine Zahl HEBT, wird genauso gebucht.
* Der Schritt endet trotzdem mit einem Commit und einem Bericht.

---

# Schritt 0 — die Messapparatur *(seriell, EIN Agent, vor allen anderen)*

**Warum zuerst:** an diesem Tag hat zweimal ein Wächter grün gemeldet, während sein Gegenstand
kaputt war — einmal, weil der Nenner schrumpfte, einmal, weil eine Ratsche nicht gehalten
wurde. **Solange drei Anker tot sind, läuft der volle Mutationslauf gar nicht an**, und jede
Deckungszahl ist eine Teilmessung. *Wer sein Messgerät nicht zuerst repariert, misst alles
Folgende mit dem kaputten.*

### 0.1 Die drei toten Anker in `emit.rs`

```
dma-wird-abgesenkt · geraetegriff-ohne-basis · ausdrucksform-heisst-wieder-ausdrucksform
```

Ein Anker ist eine **wörtliche Quellzeile**, an der eine Mutation greift; ist sie durch ein
Refactoring verschwunden oder mehrdeutig geworden, meldet `--anker` `FEHLT`. **Repointen, nicht
löschen** — *eine gelöschte Mutation verkleinert den Nenner und liest sich wie Deckung.* Such
die Stelle, die die Mutation treffen wollte, und schreib den Anker auf die heutige Zeile um.
Danach: **`./instrumente/mutiere-pruefer.py` vollständig fahren** (≈ 2 min 20 s lokal; `crates/`
muss sauber sein) und die Fangquote im Bericht nennen — es ist der erste volle Lauf seit
mehreren Tagen.

### 0.2 Die fünf roten Wächter

Je Wächter: **Ursache messen, dann entscheiden.** Drei Ausgänge, und der dritte ist häufiger,
als er aussieht:

1. **Ein echter Rückstand** → heilen.
2. **Eine Marke, die nachgezogen gehört** → mit ausgeschriebenem Grund nachziehen.
3. **Der Wächter misst etwas anderes als seinen Gegenstand** → dann ist der Wächter der
   Befund (W16/W21), und die Heilung gehört ins Werkzeug.

`pruefe-todo.py` meldet *„README sauber: N Befunde — falsches Rot"*: das ist seine eigene
**Sprechprobe**, und sie sagt, dass er auf einer sauberen Vorlage anschlägt. **Das ist Ausgang
3.** `pruefe-klauseln.py` meldet *„diese Zeilen sind GESTIEGEN — ein Pass liest sie jetzt"*:
Ausgang 1, ein Eintrag gehört gelöscht.

**Abnahme Schritt 0:** alle zehn Wächter grün · voller Mutationslauf mit genannter Quote ·
`--anker` ohne `FEHLT`.

---

# Bahn A — Gerät und Eintritt

*Die drei letzten Klempnereilücken. Sie sind die einzigen offenen `K`-Zeilen in
`dokumente/PFLICHTEN.md`; alles andere Offene ist `L` — Logik, die der Mensch schreibt.*

**Dateien dieser Bahn:** `crates/gabbro-check/src/m3.rs`, `geraete*.rs`, `abi.rs`,
`phasen.rs` · `dokumente/SYNTAX.md` (§ Gerät) · `beispiele/02-geraet.gab`,
`beispiele/08-*.gab` · `messung/TRAEGER-UND-HARDWARE.md`.

## A1 — «B18»: `device` kennt keine Phasen

**Der Befund steht in `dokumente/PFLICHTEN.md` und trägt eine BEZAHLTE Falle.** Das Fragment
schreibt die gewünschte Form selbst hin, als Kommentar, weil es sie nicht schreiben kann:

```gabbro
reg USED_IDX : u16 wrapping @0x202 class rw in Setup, r in Live
```

Und die Zeile darunter sagt, warum eine feste Klasse falsch wäre: **`class r` allein wäre hier
falsch — es verböte genau das Nullen, das die bezahlte Falle entschärft.**

Dazu die zweite Fundstelle, gemessen am 2026-08-26: `L101` wurde als *tragend* gebucht und
trägt nicht. Eine Funktion ohne jede Marke in der Signatur schreibt das Register:

```
impl fn heimlich(q : ptr<dma, rw> Virtq) effects { writes q } costs <= 4 ops
    { q.USED_IDX = 7; }        ->  8 Items, 0 Fehler, 0 Hinweise
```

**Eine lineare Marke ist eine Erlaubnis, die niemand halten MUSS.** `L101` hält, dass wer sie
hat, sie weitergibt — nicht, dass wer schreibt, sie haben muss.

**Zu klären, bevor gebaut wird:** wo steht die Phase — am Register, am Gerät, an der Funktion?
Und woher weiß ein Pass, in welcher Phase eine Aufrufstelle steht? *Die Phasenordnung an
linearen Geistmarken (`phasen.rs`, `O001`–`O012`) ist der nächstliegende Träger und schon
gebaut* — prüfe zuerst, ob sie reicht, bevor ein zweiter Mechanismus entsteht.

**W24-Vorlauf ist Pflicht:** schreib die Zeile aus dem Fragment hin und miss, woran sie fällt.

## A2 — «B26»: das Geräteversprechen senkt nicht ab

**Halb geschlossen am 2026-08-24, und die Zeile sagt selbst, welche Hälfte.** `requires` am
Register wird seither **gezählt** (`gabbro pflichten` führt es als `D`, Geräteversprechen) —
aber es trägt **keinen Falsifikator** und **senkt nicht ab**.

**Warum eine Tatsache daraus falsch wäre:** das Register ist volatil, und ein feindliches Gerät
darf alles melden. *Aus dem Versprechen eine Tatsache zu machen, wäre der «B33»-Fehler noch
einmal.* Die Zeile nennt die Form, die es schließen würde:

```gabbro
requires <bedingung> else <grund>        -- macht die Lesung fehlbar
let q = d.REG else (e) { … }             -- und diese Form trägt der Erzeuger schon
```

**Und `H` fällt dadurch NICHT um eins**, solange nur gebucht wird: *eine Buchung ist keine
Erledigung, und einen Dekrement mit Buchführung zu kaufen ist genau das, wogegen K100s zweites
Tor steht.* Der Bau muss also die **Absenkung** liefern, nicht die Zählung.

## A3 — «B27»: die Registerbelegung am Eintritt

**Die eine Stelle, an der die vertraute Fläche schrumpfen könnte, und sie hat keinen Träger.**
`arch ident` existiert, die Registerbelegung nicht; der Posten steht im Register als *„die
vertraute Fläche schrumpft nicht, sie wandert in eine `prim`-Deklaration ohne Inhalt."*

`entry … regs in { … } regs out { … } preserves { … } clobbers { … } stack … dispatch …` steht
in `SPRACHE.md` Teil II §2 mit voller Grammatik und ist in `beispiele/07` geschrieben. **Miss
zuerst, was davon einen Leser hat** — `entry` ist ein Kandidat für dieselbe Klasse wie `when`
und `raw fn`: eine Form mit Produktion, Parser und AST, deren Klauseln kein Pass liest.

> **Wenn sich das bestätigt, ist A3 kein Bau, sondern die vierte Klausel ohne Leser** — und
> das Schließen ist billiger als das Erfinden.

**ERLEDIGT am 2026-08-30, und es war weder ein Bau noch die vierte Klausel**
([`messung/EINTRITTSBELEGUNG.md`](../messung/EINTRITTSBELEGUNG.md)). Gemessen wurde, dass
«B27» gar nicht von `entry` handelt — die `entry`-Klauseln haben Leser — sondern von der
Gegenrichtung: dem `prim fn`-Systemaufruf. **Und der Korpus hat davon genau EINE Stelle**,
im Fragment, das die Lücke meldet; er schreibt Systemaufrufe längst als `asm`-Rumpf.

*Regel A: kein Konstrukt ohne gemessenen Bedarf.* Ein Pass gegen eine Registertabelle je
`arch` wäre nicht falsch — er hat **null gemessenen Bedarf**, und eine Tabelle je
Architektur ist Pflege. **Entscheidung: Delegation an `cc`, mit Namen im Zeugnis.**

Die Belegung steht in C-Zwangsbuchstaben und erreicht den Übersetzer ungelesen. Das steht
seit heute in Abschnitt E des Zeugnisses, **neben** den `ASSEMBLY`-Zeilen:
`REGISTER ALLOCATION -- delegated to `cc`, NOT checked here («B27»)`.

> **Eine benannte Delegation ist die ehrliche Buchung; eine stillschweigende ist keine.**
> Sie schrumpft die vertrauenswürdige Fläche nicht, und die Zeile sagt genau das: wer zwei
> Buchstaben vertauscht, bekommt ein übersetzbares, falsches Programm.

## A4 — Bahn A abschließen

Register nachziehen (`PFLICHTEN.md`, `MESSUNGEN.md`), `H` neu ableiten mit
`./instrumente/zaehle-pflichten.py`, und **im Bericht die Arithmetik ausschreiben**: welcher
Punkt fiel durch Bau, welcher durch Berichtigung, welcher gar nicht.

---

# Bahn B — Rumpf, Ruf und Ausdruck

*Die größte echte Absage des Beweiskanals und die Logiklücken, die Programme unschreibbar
machen.*

**Dateien dieser Bahn:** `crates/gabbro-check/src/lean.rs`, `m1.rs`, `pflichten.rs` ·
`programmlogik/Gabbro/Body.lean`, `programmlogik/beispiel/` · `dokumente/SYNTAX.md`
(§ Ausdruck, § Schleife) · `instrumente/zaehle-lean.py`.

## B1 — Das kompositionale Ruf-Tor *(der größte Posten dieser Bahn)*

```
$ ssh ki-pc-fisch-101 'cd gabbro-B && for f in beispiele/*.gab messung/*/*.gab; do
    ./target/debug/gabbro lean "$f" 2>/dev/null; done \
  | grep -oE "^-- REFUSED  [^ ]+  \([a-z-]+\)" | grep -oE "\([a-z-]+\)" | sort | uniq -c | sort -rn'
```

Heute: **17 `call-not-compositional`**, gewachsen von 11, weil die neuen `ops`-Rufe
hineinlaufen. Nach den Schleifen die größte Absage, die **keine Korpusarbeit** ist.

**Der Gegenstand:** ein Ruf im Rumpf wird über den **Vertrag** des Gerufenen behandelt — seine
Vorbedingung als Beweisziel an der Stelle, seine Nachbedingung als **Hypothese** danach.
`Body.lean` trägt die Form schon: `Env : String → State → State × Option Value`, und `call`,
`bindCall`, `retCall` stehen als `Stmt`-Konstruktoren. **Was fehlt, ist die Erzeugerseite in
`lean.rs`** — und die Regel, die dabei nicht gebrochen werden darf:

> **Ein Vertrag ist eine HYPOTHESE, niemals ein Axiom.** Wer die Nachbedingung des Gerufenen
> als Axiom einträgt, hat einen Beweiser gebaut, der jeden Unsinn schließt, sobald ein
> `ensures` falsch ist. Sie gehört als Voraussetzung in den Satz, nicht in die Umgebung.

**Sonde in beide Richtungen**, ohne die der Schritt nicht abgenommen wird: ein Satz über einem
Rumpf mit Ruf muss **einmal grün** gesehen worden sein und **einmal rot**, und das Rot muss aus
der *verletzten Vorbedingung* kommen und nicht aus einem hängengebliebenen Ziel. *Am
2026-08-28 fiel eine Giftprobe zuerst in der falschen Farbe — richtig rot, falscher Grund.*

**Erwartete Wirkung:** 17 Absagen fallen, und die Rumpfdeckung steigt von 89 auf ~106 von 181.
**Nenne die Zahl vorher und nachher, mit dem Befehl daneben.**

## B2 — «B10»/«B11»: die Dienstschleife mit benanntem Ausgang

Zwei Zeilen in `PFLICHTEN.md`, und beide sagen dasselbe:

* *„der Schnellpfad nimmt den ERSTEN lebenden Empfänger und hört auf"* — `traverse` liefert
  keinen Wert und kennt kein `break`; `by consuming` leert die ganze Schlange. **Nicht
  Umständlichkeit: ein anderes Programm.**
* *„die Dienstschleife hat einen BENANNTEN Ausgang"* — ohne ihn nur `exit()`, und die
  Aufräumzusage wandert an zwei Stellen. **Wörtlich die Klasse, die C8 bezahlt hat.**

`leaves` und `leave` stehen im Wortschatz (`kw.rs`), `forever … leaves <identlist>` steht in
der Grammatik. **W24-Vorlauf ist hier besonders wichtig:** es kann sein, dass die Form parst
und der Ausgang nur keinen Leser hat — das wäre die fünfte Instanz derselben Klasse.

**Und der Rumpfkanal führt `non-local-exit` als eigene Absage.** Wenn `leave` einen Leser
bekommt, gehört die Absage dort geprüft: entweder sie fällt, oder sie benennt, was eine
Schleifensemantik zusätzlich liefern müsste.

## B3 — Die vier Ausdruckslücken

Ein Schritt, vier Posten, alle klein — **aber jeder mit W24-Vorlauf**, weil heute zwei von
dieser Sorte sich als Berichtigungen erwiesen haben.

| | |
|---|---|
| **«B6»** | ~~`result` in `ensures`. `old(place)` gibt es, ein `result` nicht. Der Rumpfkanal führt `result-in-ensures` als eigene Absage mit dem Vermerk *„ein Tor entfernt, nicht weit"*~~ — **GESCHLOSSEN.** Das Tor ist am 2026-08-28 gebaut (`bindLocal … "result" v`), und am 2026-08-30 ist der Name nachgezogen: was noch absagt, ist `result` im **Rumpf** und heißt `result-in-body` (`messung/ERGEBNIS-ZWEI-NAMEN.md`) |
| **«B14»** | `option` steht nur im `slottype`, nicht im `typeexpr`. *„nie gelesen" von „null" zu unterscheiden* ist genau die Lesart, gegen die zwei Fragmente geschrieben sind |
| **«B12»** | keine Zahlbereichsdomäne; der Ersatz `elems of` hat zwei Lesarten und die Grammatik entscheidet keine. **Achtung: als *entschieden* gebucht am 2026-08-20** — prüfe zuerst, ob die Zeile noch stimmt |
| **«B31»** | `old` hängt unter `atompred`, nicht unter `primary`. Keine Differenzaussage schreibbar — *und das trifft jedes „nachher gegen vorher"* |

## B4 — «B13»: `count`, und der Beweis davor

**Gemessen am 2026-08-28** (`messung/AGGREGATION.md`): die trägerübergreifende Aussage geht
heute schon durch. Was fehlt, ist **eines**, und es fällt am **Wort**: `anzahl(o)` parst an
derselben Stelle, `count(o)` nicht — `count` ist reserviert und hat keine Produktion. **Es
kostet also keinen Wortschatz.**

**Teuer ist der Rest, und er kommt ZUERST:**

1. eine **Kostenregel** — sonst lügt `cost O(1)` bei geschachteltem `count`;
2. eine **Erzeugerschablone** mit ihrer Erhaltungsfrage, ins Register;
3. **das Isabelle-Gegenstück** — K100s zweites Tor steht davor.

*Wenn (3) nicht gelingt, endet der Schritt mit der benannten Absage und dem Beweisversuch
daneben. Das ist ein vollwertiges Ergebnis.*

## B5 — Die Korpusschleifen

**24 `loop`-Absagen, davon 22 Korpusschleifen ohne `invariant`.** Das ist stumpfe Arbeit und
gehört ans Ende der Bahn: je Schleife hinschreiben, was über ihr gilt. `M133` verlangt, dass
die Invariante mindestens einen Namen nennt — `invariant true` ist ein Versprechen über nichts.

**Kein Beweisziel wird dabei geschönt.** Wo eine Invariante nicht hinschreibbar ist, bleibt die
Schleife abgesagt, und der Bericht nennt sie mit Grund. *Eine erfundene Invariante, die durch
den Prüfer geht, ist schlimmer als eine fehlende.*

---

# Schritt 6 — Zusammenführung *(seriell, EIN Agent, nach beiden Bahnen)*

1. **Beide Bahnen auf `master` zusammenführen**, Konflikte nach §1.6 auflösen (additiv).
2. **Die volle Abnahme auf dem VERSCHMOLZENEN Stand fahren, nicht die gemeldeten Zahlen
   übernehmen.** Am 2026-08-28 hat genau dieser Schritt einen Regress gefunden, den kein
   Bericht nannte: die Emission fiel von 52 auf 51, und die Zeile las sich unverändert grün.
3. **Voller Mutationslauf** mit Quote.
4. **Register nachziehen:** `PFLICHTEN.md`, `MESSUNGEN.md`, `DONE.md`, `TODO.md`, und die
   K100-Standtabelle in `dokumente/PLAN.md` (`H`, `L`, `A`, zweiter Korpus).
5. **Rumpfdeckung neu messen** und mit dem Stand von heute vergleichen.

---

# 7. Was dieser Plan ausdrücklich NICHT enthält

**Die Absenkung — und sie ist größer als alles darüber zusammen.**

| | |
|---|---|
| **A8** | achtzehn C-Absenkungen stehen als **Behauptung** da, nicht als aufgeschriebene Absenkung |
| **die Brücke** | **keine erzeugte Form hat einen Absenkungsbeweis** — weder `insert` noch `remove` noch `relabel` noch das Baugatter noch `retires`. Dass `t->slots[s].elter = p;` die Funktion `umhaengen` **ist**, steht in keinem Satz |
| **K100.4 stark** | ein maschinengeprüftes Zeugnis je Übersetzung, statt einer Aufzählung dessen, worauf sie ruht |

`Table_Absenkung.thy` sagt es in eigenen Worten: es beruft sich für den Rest auf *„die
Sprachdefinition von C und keine Annahme dieses Beweises"*.

> **Alles in den Bahnen A und B ist begrenzte Arbeit** — Grammatikzeilen, Pässe, Giftproben,
> jedes Stück mit einem Ende. **Das hier ist eine Semantik**, und der Ordner weigert sich
> ausdrücklich, dafür eine Zahl zu nennen: *„I do not have a defensible estimate, and an
> invented one would be worse than none; which is why gates stand above instead of a date."*

**Und es gibt zwei Wege hindurch, die Alternativen sind und keine Ergänzungen:**

* **C beweisen** — eine C-Semantik hinschreiben und die Absenkung dagegen beweisen. Man erbt C.
* **C streichen** — ein Übersetzer in Gabbro, der direkt Binärcode erzeugt, mit einem
  **bewiesenen Prüfer je Übersetzung** statt einem Satz je Optimierung. Man erbt nichts.

*Wer anfängt, eine C-Semantik zu schreiben, hat die Entscheidung getroffen, ohne sie zu
stellen.* **Diese Entscheidung ist keine Agentenarbeit** und steht nicht in diesem Plan.

---

# 8. Der Zeitrahmen, und woran er hängt

**Bezugsgröße:** fünfzehn Tage vom ersten Commit bis heute, 545 Commits, 30 von 41
Lückeneinträgen geschlossen.

| | |
|---|---|
| Schritt 0 | **ein halber bis ein Tag** |
| Bahn A (A1–A4) | **zwei bis vier Tage** — drei Entscheidungen, und A3 könnte eine Berichtigung sein |
| Bahn B (B1–B5) | **drei bis fünf Tage** — B1 ist der größte Einzelposten, B5 ist stumpf |
| Schritt 6 | **ein halber Tag** |
| **zusammen, bei zwei Bahnen nebeneinander** | **vier bis sechs Tage** |

**Und die Warnung gehört daneben, weil sie an diesem Tag zweimal zugeschlagen hat:** die
fünfzehn Tage haben *gebaut*, was noch nicht existierte — dort ist Durchsatz die richtige
Größe. **Drei der zehn heutigen Posten waren Berichtigungen und gingen darum schnell**; das
wiederholt sich nicht auf Bestellung. Wer aus diesem Plan eine Zusage macht, hat die
Fortschreibung gemacht, gegen die die Tore stehen.
