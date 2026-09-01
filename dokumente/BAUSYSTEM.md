# Das Bausystem — die Rechnung vor dem Bau

*Gerechnet am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 12 GB verfügbar, 20 Kerne).
**Diese Rechnung steht vor der ersten Zeile Code**, und die Messungen darin sind gegen den
Baum gefahren und nicht geschätzt.*

Der Nutzer hat die Bauart gesetzt: **Cargo-artig mit Manifest, nicht Meson-artig als
Generator.** Die Gründe stehen in der Sprache und nicht im Geschmack:

* **`when TESTBUILD`** ist ein Sprachkonstrukt (`beispiele/52-baugatter.gab`), keine
  Übersetzerfahne.
* **`arch x86_64`** steht an `entry`, an `boot` und an `entrust` — gemessen: 11 Dateien tragen
  ein `entry`, und `arch x86_64` steht in **jeder** dieser Formen in der Quelle. *Die
  Zielarchitektur ist eine Aussage der Quelle.*
* **`gabbro emit a.gab b.gab` erzeugt schon EINE Übersetzungseinheit** — der Linkschritt ist in
  Wahrheit die Frage *welche Dateien bilden eine Einheit*.

---

## 1. Die Frage, die alles entscheidet: **was steht schon in der Quelle?**

`W7` sagt: *ein zweites Register über derselben Sache.* Ein Manifest, das die Abhängigkeiten
noch einmal aufschreibt, ist genau der Fehler — die `use`-Kanten stehen schon in den Dateien.

**Also die Gegenfrage:** was steht **nicht** in der Quelle, und ist deshalb unvermeidlich?

| Größe | steht in der Quelle? | wo |
|---|---|---|
| der Modulname einer Datei | **ja** | `module X { … }` |
| die Abhängigkeitskanten | **ja** | `use a::b::C;` |
| die Zielarchitektur | **ja** | `arch x86_64` an `entry`/`boot`/`entrust` |
| die bedingte Übersetzung | **ja** | `when TESTBUILD` |
| die Wirkungen, Kosten, Sperren | **ja** | `effects`/`costs`/`locks` |
| **welche Dateien es gibt** | **nein** | — eine Datei kennt ihre Geschwister nicht |
| **welche Dateien EINE Einheit bilden** | **nein** | — |
| **welcher fremde Übersetzer, mit welchen Fahnen** | **nein** | — keine Sprachfrage |
| **was das Erzeugnis ist** (Programm/Bibliothek) | **nein** | — |

**Vier Zeilen ohne Vertreter in der Quelle. Das ist das Manifest, und mehr nicht.**

## 2. Die Messung, die die naheliegende Abkürzung widerlegt

Die naheliegende Bauart wäre: *das Manifest nennt nur ein Verzeichnis, und der Modulname folgt
dem Dateinamen* — dann bräuchte es die Dateiliste auch nicht. **Gemessen über alle 491
`.gab`-Dateien:**

| Größe | Zahl |
|---|---|
| Dateien gesamt | **491** |
| ohne jedes `module` | **2** |
| mit `module` | **489** |
| davon: Dateiname **=** Modulname | **16** |
| davon: Dateiname **≠** Modulname | **473** |
| Dateien mit **mehr als einem** `module` | **9** |
| Modulnamen, die **mehr als eine** Datei führt | **14** |

Die Spitze der letzten Zeile: **`module gift` steht in 122 Dateien.** Dann `p` (5), `eins` (3),
`zwei` (3), und `speicher`, `geraet`, `mischt`, `nutzer`, `a`, `b` je zweimal.

> **Zwei Schlüsse, beide gemessen und nicht gewählt:**
>
> 1. **Eine Konvention „Modulname = Dateiname" ist widerlegt** — 473 Gegenbeispiele gegen 16
>    Treffer. Das Manifest muss die **Dateien** nennen.
> 2. **Eine GLOBALE Modul→Datei-Karte ist unmöglich.** `module gift` gehört 122 Dateien; eine
>    Karte über den ganzen Baum hätte 122 Kandidaten für einen Namen. **Ein Modulname ist nur
>    INNERHALB einer Einheit eindeutig** — und `N039` sagt genau das ab, wenn er es nicht ist.

**Daraus folgt die ganze Bauart:**

```
Das Manifest nennt DATEIEN je Einheit.
Der Bau LIEST die Dateien und rechnet daraus:
    Datei -> Modul     (aus `module`)
    Modul -> Einheit   (aus der Zuordnung oben)
    Einheit -> Einheit (aus `use`, über die Modulkarte)
```

*Die Kanten werden gerechnet, nie geschrieben.* Wer sie ins Manifest schriebe, hätte ein
zweites Register über den `use`-Zeilen — und das erste Mal, dass eine `use`-Zeile hinzukommt
und die Manifestzeile nicht, baut der Bau aus einer Mischung. **Dieselbe Klasse wie `rsync -a`
gegen `cargo`.**

## 3. Was das Manifest trägt — vier Zeilenarten

```
-- gabbro.bau -- das Baumanifest.
--
-- Was hier NICHT steht: Abhaengigkeiten, Architektur, Baugatter, Modulnamen.
-- Alles vier steht in den Quellen und wird von dort gelesen.

compiler cc -std=c11 -Wall -Wextra -Werror
out      target/bau

unit lager program
    programmlogik/beispiel/lager.gab
    programmlogik/beispiel/betrieb.gab
```

| Zeile | warum sie unvermeidlich ist |
|---|---|
| `compiler …` | der fremde Übersetzer und seine Fahnen — keine Sprachfrage |
| `out …` | wohin die Erzeugnisse gehen — keine Sprachfrage |
| `unit <name> <art>` | **welche Dateien eine Einheit bilden** — der eigentliche Linkschritt |
| eingerückte Pfade | die Dateien der Einheit — 473 Gegenbeispiele gegen jede Konvention |

**Kein Format zum zweiten Mal:** das ist bewusst *kein* Gabbro-Quelltext. `gabbro abi`
schreibt `.gabi` als gültigen Gabbro-Text, weil eine Schnittstelle **eine Einheit beschreibt**
und dieselben Pässe durchlaufen soll. Ein Baumanifest beschreibt keine Einheit — es hat kein
`module`, keine Wirkungen und keine Kosten. *Es als Gabbro zu schreiben hieße, Itemarten zu
erfinden, die die Sprache nicht hat*, und die Sprache um des Bausystems willen zu erweitern
ist die Richtung, gegen die W24 steht.

## 4. Inkrementell nach INHALT, nicht nach Zeitstempel

`CLAUDE.md` trägt **zwei** Fallen dieser Klasse, und beide in verschiedene Richtungen:

* `rsync -a` gegen `cargo`: der Zeitstempel **log**, und `cargo` baute aus einer Mischung.
* Der Riegel nach `abnahme.py --voll`: der Zeitstempel **sagte die Wahrheit** über etwas, das
  keine Rolle spielte, und meldete einen grünen Baum rot.

> *Ein Werkzeug, das die Zeit misst statt den Inhalt, irrt in beide Richtungen.*

**Also der Inhalt.** Je Einheit ein Abdruck über:

1. den Inhalt **jeder** Quelldatei der Einheit (in Manifestreihenfolge),
2. die Übersetzerzeile **mitsamt Fahnen** (eine andere Fahne ist ein anderes Erzeugnis),
3. den Baumodus (`--testbuild` oder nicht — `when TESTBUILD` hängt daran).

Stimmt der Abdruck mit dem der letzten Aufzeichnung überein **und liegt das Erzeugnis vor**,
wird nichts getan. *Das Vorliegen wird geprüft und nicht geglaubt* — sonst hätte ein
gelöschtes Erzeugnis mit gültiger Aufzeichnung genau die Lücke, gegen die der ganze Abschnitt
steht.

**Der Abdruck ist FNV-1a, 64 Bit, von Hand** — dieselbe Bauart wie `abdruck` in `main.rs`, nur
breiter. *Und er ist ausdrücklich nicht kryptographisch:* er schützt gegen ein **versehentlich**
unverändertes Erzeugnis, nicht gegen einen Angreifer, der eine Kollision sucht. Wer ihn für das
Zweite hielte, hätte eine Zusage, die niemand gegeben hat. 32 Bit wie in `abdruck` wären hier
zu schmal — der Abdruck steht dort in einer Ausgabe, die ein Mensch vergleicht, hier in einer
Entscheidung, die eine Maschine trifft.

## 5. Die Deckungszeile — was gebaut wurde UND was nicht angesehen wurde

`abnahme.py` und `gabbro pruefe` drucken beide, was sie **nicht** geprüft haben. Ein Bau, der
das nicht sagen kann, passt nicht in diesen Baum: *„nichts gefunden" und „nichts angesehen"
sehen sonst gleich aus.*

Der Bau druckt darum drei Zahlen und eine Liste:

```
built 1 unit(s), 0 up to date, 0 refused
NOT looked at: 489 `.gab` file(s) in this tree stand in no unit of this manifest
  the manifest is the reach -- a file no `unit` line names is not a file this build passed
```

**Die dritte Zeile ist die wichtige.** Sie ist `Falle 80` in Werkzeugform: eine Zahl über einen
Korpus, den man beim Bauen angesehen hat, ist keine Messung — und ein Bau, der 2 Dateien baut
und 489 nicht ansieht, darf nicht wie ein Bau über den Baum aussehen.

## 6. Was diese Rechnung NICHT entscheidet

* ~~**Wie eine Einheit gegen eine andere linkt.**~~ **Entschieden und gebaut am 2026-09-01:
  als `.gabi`-Vorspann.** Der Grund steht nicht im Geschmack, sondern in der Prüfung: ein
  C-Kopf trüge Typen und keine Verträge, und `effects`, `costs`, `requires` gingen genau da
  verloren, wo sie geprüft werden müssten. Siehe den Abschnitt *„Die Kante, gebaut und
  gelaufen"* am Ende.
* **Ob `arch` über eine Einheit hinweg widerspruchsfrei sein muss.** Zwei Dateien einer Einheit
  mit verschiedenen `arch` sind ungemessen.
* **Was bei einem Zyklus zwischen Einheiten geschieht.** Der Graph kann einen tragen; ob er
  abgesagt wird, steht offen.
* **Nichts davon sagt, dass die Einheiten dieses Baums richtig geschnitten sind.** Das Manifest
  sagt, was zusammengehört; **ob es zusammengehört, sagt kein Werkzeug.**

---

# Was davon LÄUFT (2026-08-31)

`gabbro build` (deutscher Zweitname `bau`), `crates/gabbro-cli/src/bau.rs`, 9 Proben grün.

> **Die Zahlen dieses Abschnitts sind die vom 2026-08-31 und werden nicht nachgezogen.** Der
> Korpus ist seither von 491 auf 525 `.gab`-Dateien gewachsen, also stimmt jede Zahl darunter
> als *Messung jenes Tages* und keine als Aussage über heute. *Eine Zahl, die man nachzieht,
> ohne sie neu zu messen, ist eine Behauptung mit einem Datum davor.* Was heute läuft, steht
> unter **„Die Kante, gebaut und gelaufen"** am Ende — mit eigenen Zahlen und eigenem Datum.

## Der Lauf über dem Beispiel

`programmlogik/beispiel/gabbro.bau` — **das Manifest nennt zwei Dateien und keine einzige
Abhängigkeit.** Die vier `use lager::…`-Zeilen stehen in `betrieb.gab`, und der Bau liest sie
dort.

```
$ gabbro build --dry-run programmlogik/beispiel/gabbro.bau
manifest programmlogik/beispiel/gabbro.bau
  compiler cc -std=c11 -Wall -Wextra -Werror
  out      target/bau-beispiel
  unit lager (2 file(s))
  0 computed edge(s) between units
built 0 unit(s), 0 up to date, 0 refused -- 2 file(s) named by this manifest
NOT looked at: 489 `.gab` file(s) in this tree stand in no unit of this manifest (491 in the tree)
  the manifest is the reach -- a file no `unit` line names is not a file this build passed

$ gabbro build programmlogik/beispiel/gabbro.bau
built    lager
$ gabbro build programmlogik/beispiel/gabbro.bau
current  lager  -- content unchanged, artefact present
```

Das erzeugte C ist **eine** Übersetzungseinheit aus zwei Dateien und geht durch
`cc -std=c11 -Wall -Wextra -Werror`. *Einzeln geprüft fällt `betrieb.gab` mit fünf Absagen.*

## Die vier Eigenschaften, jede mit einer Probe

| Eigenschaft | Probe |
|---|---|
| **`touch` baut NICHT neu** — dieselben Bytes, neue `mtime` | `inkrementell_nach_inhalt_und_nicht_nach_zeitstempel` |
| **ein gelöschtes Erzeugnis baut neu** — das Vorliegen wird geprüft, nicht geglaubt | dieselbe |
| **eine andere Übersetzerfahne baut neu** — `-O0` → `-O2`, kein Quellbyte bewegt | `eine_andere_uebersetzerfahne_baut_neu` |
| **der Graph wird gerechnet** — kein `use` im Manifest, und die Kanten stehen trotzdem | `der_graph_wird_gerechnet_und_nicht_gelesen` |

## Drei Giftmanifeste, alle abgesagt

| Probe | Absage | Rückgabe |
|---|---|---|
| derselbe Modulname in **zwei** Einheiten | *„module `a` is declared in unit `eins` AND in unit `zwei` — a `use` edge onto it would have two targets"* | 1 |
| eine Einheit **ohne Datei** | *„unit `leer` names no file — an empty unit builds nothing and says it built"* | 2 |
| eine Einheit, die **nicht durchgeht** | `REFUSED halb: 7 error(s) -- no C written` | 1 |

**Und die Absagen der dritten nennen `betrieb.gab:36:56`, nicht `<unit>:36:56`** — der Bau
rendert durch **dieselbe Versatzkarte** wie `pruefe --unit`, aus derselben Funktion
(`main.rs::zeige_je_stueck`). *Zwei Renderungen desselben geklebten Parses wären ein zweites
Register über derselben Sache.*

## Zwei Mutationen — und eine hat überlebt

| Nr. | Was beschädigt wird | gefangen von |
|---|---|---|
| **452** `bau-glaubt-das-erzeugnis` | das Vorliegen wird geglaubt statt geprüft | **1 Probe** |
| **453** `bau-vergisst-die-uebersetzerzeile` | die Übersetzerzeile fällt aus dem Abdruck | **anfangs 0 — ÜBERLEBT** |

> **`453` hat überlebt, und der Grund ist derselbe wie bei `451`: meine Proben sahen auf die
> falsche Hälfte.** Alle acht bewegten **Quellbytes** — und *Inhalt allein ist nicht die ganze
> Eingabe eines Baus.* Ein Wechsel von `-O0` auf `-O2` hätte „aktuell" gemeldet, und das
> Erzeugnis stünde unter einer Fahne, die niemand mehr genannt hat.
>
> `eine_andere_uebersetzerfahne_baut_neu` ist daraufhin geschrieben worden. **Zum zweiten Mal
> an diesem Tag hat eine überlebende Mutation eine blinde Probe benannt** — und beide Male war
> die Blindheit dieselbe: die Probe sah dorthin, wo ich den Fehler erwartet hatte.

---

# Die Kante, gebaut und gelaufen (2026-09-01, `OB5`)

**Der Posten war eine ÄNDERUNG und keine Zahl, und hier ist sie:**

```
$ gabbro build messung/einheit-proben/zwei-einheiten.bau
built    rechenwerk
built    haupt
$ target/bau-zwei/haupt ; echo $?
137
```

**137 = 100 + 37.** Die `100` ist eine `5000`, die ein **privater** Helfer der *anderen*
Einheit gedeckelt hat; die `37` ging unberührt durch. *Eine Zahl, für die beide Hälften der
Grenze stimmen müssen.*

```
rechenwerk (object)   prog-vorrat.gab + prog-werk.gab  ->  rechenwerk.o + rechenwerk.gabi
     ^                                                     als EINE Einheit geprueft,
     | use werk::ablegen, use werk::holen, use vorrat::Regal    uebersetzt UND beschrieben
haupt (program)       prog-haupt.gab                   ->  haupt.o, dann der BINDER
```

## Was der Bau dafür können musste — drei Dinge, und das dritte hat einen Preis

1. **`emit --unit` und `abi --unit`.** *Eine Einheit, die als Einheit PRÜFT, wurde nicht als
   Einheit ÜBERSETZT* — `pruefe --unit` klebte die Dateien, `emit` lief je Datei. Gemessen an
   denselben zwei Dateien: **sieben Absagen ohne die Fahne, null mit ihr.** Die Fähigkeit gab
   es, *in `bau.rs` eingebaut und ohne Namen auf der Kommandozeile* — die Gestalt, die ein
   fehlendes und ein verstecktes Merkmal teilen.
2. **Die Kante wird getragen, nicht nur gerechnet.** Vor jeder Einheit steht die `.gabi` von
   allem, worauf sie steht — **transitiv** und in Bauereihenfolge. *Nur direkte Kanten reichen
   nicht:* die Schnittstelle von `b` nennt einen Typ, den `a` erklärt, und eine Schnittstelle,
   die etwas nennt und nicht erklärt, ist genau das, was `N038` innen absagt.
3. **Die Abdrücke der Unterbauten gehen in den eigenen Abdruck.** Das war der Preis, und es
   ist die Falle, gegen die Abschnitt 4 steht: *eine Änderung im **privaten** Rumpf bewegt die
   `.gabi` nicht und das Objekt schon.* Gemessen: `return 100` → `return 99`, `.gabi`
   byteidentisch, `haupt` **gebaut** (nicht „current"), Ergebnis 136. Ohne die Kette wäre das
   Programm aktuell gemeldet worden — über einer Bibliothek, die es nicht mehr enthält.

## Acht Proben, fünf davon Gegenrichtung

| Probe | was sie hält |
|---|---|
| `das_zweieinheitenprogramm_uebersetzt_und_laeuft` | 1 gerechnete Kante, gebunden, `137` |
| `ohne_die_kante_faellt_das_programm` | dasselbe Programm ohne die Einheit darunter: `K003` |
| `ein_programm_ohne_main_faellt_an_der_eintrittsregel` | der Bindeschritt läuft und sagt wirklich ab |
| `was_pub_nicht_traegt_bindet_nicht` | `nm -g`: außen genau `ablegen holen` |
| `eine_aenderung_im_privaten_rumpf_baut_das_programm_neu` | die Abdruckkette |
| `der_treiber_druckt_und_wird_verglichen` | `100 37 100`, mit Sprechprobe |
| `die_effektableitung_sieht_ueber_die_grenze` | `identical`, und `E008` in der Gegenrichtung |
| `eine_annahme_traegt_nicht_ueber_die_grenze` | 1 Annahme diesseits, **0** jenseits |

## Die zwei Messungen, die vorher nicht zu stellen waren

### Die Effektableitung SIEHT über die Grenze

```
$ gabbro abi --vergleich --with target/bau-zwei/rechenwerk.gabi …/prog-haupt.gab
  identical      haupt::main
  units read  1        functions with `effects` and a body  1
  identical  1  100.0 %
```

`main` fasst selbst **keinen** Ort an — die zwei Wirkungen `reads Regal.slots` und
`writes Regal.slots` können nur aus den Verträgen der zwei Gerufenen stammen, und die kamen
aus der `.gabi`. **Und die Gegenrichtung ist der Befund, den `OB6` nicht finden konnte:** eine
Wirkung, die jenseits der Grenze getan und diesseits nicht erklärt wird, fällt an `E008` —
*weil geprüft wird, nicht weil geschwiegen wird.* Ohne die Brücke fällt dieselbe Datei an
`K003`, und über die Auslassung sagt niemand ein Wort.

> **Dabei fiel ein Fehler heraus, den es vor der Brücke nicht geben konnte.**
> `pruefe --with` (der Pfad je Datei) rendert gegen den **geklebten** Text und druckte den
> Dateinamen neben einer Zeilennummer der Verkettung: `…-die-grenze.gab:42:13` über einer
> Datei von 28 Zeilen. *Genau der Fehler, gegen den `Stueck` und `zeige_je_stueck` gebaut
> wurden* — einen Pfad neben dem, in dem sie standen. Er wurde erst sichtbar, als eine Absage
> zum ersten Mal aus einer `.gabi`-Brücke kam. Jetzt: `:17:13`.

### Eine `assume` trägt NICHT über die Grenze

```
$ gabbro annahmen …/prog-vorrat.gab   ->  -- 1 Annahmen   fach_zahl_passt_in_den_index
$ gabbro annahmen …/prog-haupt.gab    ->  -- 0 Annahmen
$ grep -c assume target/bau-zwei/rechenwerk.gabi  ->  0
```

**Das ist eine Entscheidung und kein Loch** — `abi.rs` sagt sie in seinem eigenen Kopf: eine
Bibliothek, die ihre `assume`-Zeilen mitschickt, zwingt jedem Importeur ihre Maschine auf, und
ein `override` beim Import ist keine Ersetzung, sondern eine **Beweispflicht** («ABI4»).

> **Was daran der Befund ist: an der Grenze sagt nichts, dass sie getroffen wurde.** Die
> Bibliothek ist unter einer Annahme bewiesen, das Programm unter keiner, `gabbro pruefe`
> geht mit `0 errors, 0 hints` durch und nennt das Wort nicht. *`OB8` sagt „Plattformannahmen
> pro Programm NULL — heute sechs von sechs"; jetzt gibt es einen Ort, an dem eine Annahme
> einmal stehen könnte, und sie trägt nicht dorthin.* Die Importform aus `§32` ist damit
> **nicht unmöglich, sondern ungebaut** — die Brücke steht, nur geht diese Fracht nicht
> darüber.

## Und ein Gabbro-Programm kann nicht drucken

Das Ergebnis verlässt `haupt` als Rückgabewert von `main`, und das ist keine Bequemlichkeit:

```
error: [N041] `putchar` is a name C has already taken
  = `putchar` is a built-in function of the C implementation
```

`printf`, `puts` und `putchar` stehen alle drei in der Tafel von `cnamen.rs`. **Der Wächter
hat recht, und er hat keine Ausnahme für eine ABSICHTLICHE fremde Bindung** — genau die, für
die `extern fn` da ist. Was gedruckt wird, druckt ein C-Treiber daneben, gebunden gegen das
`rechenwerk.o` dieses Baus, in der Gestalt von `pruefe-emission.sh` Stufe 10:
**`100 37 100`**, mit Sprechprobe. *Der Treiber ist das Messgerät und nicht Teil des
Programms.*

*Abgelehnt und nicht gebaut:* `extern fn write` — der Name ist frei — mit einem
`ptr<normal, r> Puffer` statt `const void *`. Das bindet und rechnet, und es ist eine
**unverträgliche Deklaration einer externen Funktion**, also undefiniert. Ein
Vorzeigebeispiel, das der C-Norm widerspricht, ist keines.

## Was NICHT läuft

* **~~Kein `main` in der Sprache~~ **ERLEDIGT 2026-09-01**: kein Wort dazu, aber eine Regel — ein `unit … program` ohne genau einen `pub fn main` fällt jetzt IM PRÜFER statt am Binder. Vormals: kein `main` in der Sprache, und kein Wort darüber.** `main` ist ein gewöhnlicher `pub fn`,
  dessen Name zufällig der ist, den der Binder sucht. Nichts prüft, dass ein
  `unit … program` genau einen hat — das tut der Binder, drei Werkzeuge später.
* **Ein Zyklus ZWISCHEN Einheiten ist weiter ungemessen.** Der Sortierer sagt ihn beim Namen
  ab, und es gibt kein Manifest, das einen trägt.
* **`arch` über eine Einheitengrenze ist ungemessen.** Zwei Einheiten mit verschiedenem `arch`
  mischt heute niemand, und die `.gabi` trägt kein `arch`.
* **Sperrränge über die Grenze:** sie *reisen* seit dem 2026-08-21, und `H012` fällt über eine
  Einheitengrenze — aber **nicht über eine BAU-Grenze**: `zwei-einheiten.bau` hat keinen Ring,
  also ist der Fall im Bau ungemessen.
* **Parallelität gibt es nicht.** Die Einheiten laufen der Reihe nach.
* **`--testbuild` geht in den Abdruck, aber keine Probe fährt es.**
* **Kein Fremdobjekt im Manifest.** Ein `program`, dessen `extern fn` von einer C-Datei
  bedient wird, ist nicht baubar — der Treiber oben wird von der Probe gebunden, nicht vom
  Bau.
