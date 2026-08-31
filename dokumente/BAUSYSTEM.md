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

* **Wie eine Einheit gegen eine andere linkt.** Der Graph wird gerechnet; ob die Kante als
  `.gabi`-Vorspann (`--with`) oder als C-Kopf getragen wird, ist offen.
* **Ob `arch` über eine Einheit hinweg widerspruchsfrei sein muss.** Zwei Dateien einer Einheit
  mit verschiedenen `arch` sind ungemessen.
* **Was bei einem Zyklus zwischen Einheiten geschieht.** Der Graph kann einen tragen; ob er
  abgesagt wird, steht offen.
* **Nichts davon sagt, dass die Einheiten dieses Baums richtig geschnitten sind.** Das Manifest
  sagt, was zusammengehört; **ob es zusammengehört, sagt kein Werkzeug.**

---

# Was davon LÄUFT (2026-08-31)

`gabbro build` (deutscher Zweitname `bau`), `crates/gabbro-cli/src/bau.rs`, 9 Proben grün.

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

## Was NICHT läuft

* **Kein Link zwischen zwei Einheiten.** Der Graph wird gerechnet und topologisch sortiert,
  und ein Zyklus wird beim Namen abgesagt — **aber es gibt kein Beispiel mit zwei Einheiten**,
  also ist die Kante **ungemessen**. `0 computed edge(s)` ist eine ehrliche Null und kein
  Beleg.
* **`--with` und der Bau kennen einander nicht.** Eine Einheit kann heute keine `.gabi` ziehen.
* **`unit … program` ist nie gelaufen.** Der Zweig existiert (`cc` ohne `-c`), aber das
  Beispiel ist ein `object`; ein `program` bräuchte ein `main`.
* **Parallelität gibt es nicht.** Die Einheiten laufen der Reihe nach.
* **`--testbuild` geht in den Abdruck, aber keine Probe fährt es.**
