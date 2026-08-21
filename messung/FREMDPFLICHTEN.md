# Vier Zustände einer fremden Pflicht — und der vierte hatte keinen Namen

> **Gemessen am 2026-08-21.** [`FREMDVERENGUNG.md`](FREMDVERENGUNG.md) zählt, wie viele
> ausgesprochene Fremdverträge im Rufer **etwas bewegen** (1 von 10). Dieser Bericht zählt
> die Stufe darunter: **wie viele fremde Rümpfe ihre Pflicht überhaupt aussprechen *könnten*.**
>
> Die Antwort verschiebt den Posten. Von 109 fremden Rümpfen haben **31 gar keinen Ort für
> die Zeile** — `lock`, `rcu`, `entry`, `boot` und `gabbro_kern` tragen kein `ensures`-Feld
> in der Grammatik. *Für sie ist „die Zeile hinschreiben" keine Sorgfaltsfrage, sondern eine
> Grammatikänderung.*

## Die Befehle

```
./instrumente/zaehle-fremdpflichten.py               -- die vier Zustände
./instrumente/zaehle-fremdpflichten.py --stellen     -- je fremder Rumpf eine Zeile
./instrumente/zaehle-fremdpflichten.py --sprechprobe -- nur die Sprechprobe, beide Richtungen
./instrumente/zaehle-fremdverengung.py               -- die Wirkungszahl (1 von 10)
gabbro zeugnis <datei.gab>                           -- dieselben Zahlen je Datei, Abschnitt E/F
```

Alles davon gehört auf `ki-pc-fisch-101` (`cargo run`, `CLAUDE.md`).

## Die Zahl

```
== Die vier Zustaende einer fremden Pflicht ==
  STUMM        31  (28 %)  kein Ort fuer die Zeile -- `lock`/`rcu`/`guest`/`entry`/`boot` ohne `ensures`-Feld
  SCHWEIGT     67  (61 %)  der Ort ist da, die Zeile fehlt
  UNGELESEN    10  ( 9 %)  die Zeile steht da, und kein Pass macht daraus eine Tatsache
  WIRKT         1  ( 1 %)  die Zeile wurde am Rufort eine Tatsache
              109  fremde Ruempfe in 57 Einheiten mit Zeugnis
```

| Zustand | vorher | nachher | Was er heißt |
|---|---|---|---|
| **STUMM** | 31 | 31 | Es gibt keine `FnDecl`, an die ein `ensures` gehängt werden könnte |
| **SCHWEIGT** | 68 | 67 | Ein `extern fn`/`asm fn` ist da, die Zeile fehlt |
| **UNGELESEN** | 9 | **10** | Die Zeile steht da — und kein Pass macht daraus eine Tatsache |
| **WIRKT** | 1 | 1 | Die Zeile wurde am Rufort eine Tatsache (`39-auftragsdienst`:127) |

*„vorher/nachher" ist die eine Zeile, die dieser Lauf geschrieben hat* — siehe
[Hälfte (a)](#hälfte-a-eine-zeile-geschrieben-und-sie-wird-nicht-gelesen). **Sie steht bewusst
in `UNGELESEN` und nicht in `WIRKT`.**

`UNGELESEN + WIRKT` ist dieselbe Zahl, die `zaehle-fremdverengung.py` als *„ausgesprochene
Verträge"* zählt (11 nach der Änderung), und das Werkzeug rechnet sie **gegen die Befundzeile
des Zeugnisses selbst** nach (`gegenrechnung`). *Stimmen die beiden nicht überein, bricht es
ab und nennt sich selbst als Fehlerquelle, nicht die Buchung.*

## Der Befund: die Sperre KANN ihre Pflicht nicht aussprechen

Das TODO sagt zu K100:

> *„die Sperre etwa schuldet gegenseitigen Ausschluss, Fortschritt und die Rangordnung, und
> keine Zeile sagt das heute"* — und daneben: *„Zwei Hälften: die Zeilen hinschreiben (kostet
> nichts) und den Prüfer sie tragen lassen."*

**Die erste Hälfte kostet nicht nichts. Sie geht nicht.** `LockDecl` (`ast.rs`:1394) hat die
Felder `name`, `schuetzt`, `rang`, `haltezeit`, `geteilte_haltezeit`, `maskiert` — **kein
`ensures`**. Und `zeugnis.rs`:491 schiebt den Eintrag von Hand in die Liste:

```rust
ItemArt::Lock(l) => {
    zaehle(&mut e, "lock");
    e.fremde.push((
        format!("{}_nimm / _gib (+ geteilt)", l.name.text),
        "der Rumpf einer Sperre -- gegenseitiger Ausschluss, Fortschritt, und dass \
         `rank` die Ordnung ist, die der Pruefer annimmt"
    ));
}
```

Der Eintrag läuft **nicht** durch `vertrag(f)` und erhöht **nicht** `fremde_mit_pflicht`. Die
Pflicht der Sperre steht damit als *deutscher Fließtext im Prüfer* — an genau einer Stelle,
von keinem Pass gelesen, und der Nutzer kann sie weder ändern noch verschärfen.

Dieselbe Lage bei fünf weiteren Bauformen. Die 31 zerlegen sich so:

| Bauform | Zahl | Befehl |
|---|---|---|
| `lock` | 20 | `grep -hcE "^\s*lock [A-Za-z_]" beispiele/*.gab messung/*/*.gab \| paste -sd+ \| bc` |
| `rcu` | 3 | `grep -hE "^\s*(rcu\|guest\|entry\|boot) [A-Za-z_]" beispiele/*.gab messung/*/*.gab \| awk '{print $1}' \| sort \| uniq -c` |
| `entry` | 3 | *(derselbe Befehl)* |
| `boot` | 1 | *(derselbe Befehl)* |
| `gabbro_kern` (aus `per cpu`) | 4 | `grep -lE "per cpu" beispiele/*.gab messung/*/*.gab \| wc -l` |
| **Summe** | **31** | = die `STUMM`-Zahl des Zählwerkzeugs |

> **Die ehrliche Bezugsgröße für „spricht seine Pflicht aus" ist damit 78, nicht 109.**
> 10 von 78 sprechen (13 %), nicht 10 von 109 (9 %). *Die Buchung war in dieser Richtung zu
> pessimistisch* — und in der anderen zu optimistisch, weil sie 31 Rümpfe als „schweigend"
> führte, die man nicht zum Reden bringen kann, ohne die Grammatik anzufassen.

## Was `M109` nicht sah — fünf blinde Zweige und eine Ausdrucksform

Der TODO-Posten verlangte *„die Quantorbinder und `Self` — die zwei Namensarten, die
`sammle_namen_pred` heute nicht kennt"*. Beim Nachmessen war `Self` die kleinere Hälfte.

**Gemessen vor der Änderung** (`gabbro pruefe` auf sechs erfundenen Einheiten):

| Nachbedingung | vorher | nachher |
|---|---|---|
| `ensures Self.slots[0].rest <= 4096` | `M109` „is not declared here" | **`M120`** |
| `ensures result <= lenof(Self)` | **0 Fehler** | **`M120`** |
| `ensures result <= sizeof(tippfehler)` | **0 Fehler** | `M109` |
| `ensures aligned(tippfehler, 8)` | **0 Fehler** | `M109` |
| `ensures result > 0 && tippfehler > 0` | **0 Fehler** | `M109` |
| `ensures !(tippfehler > 0)` | **0 Fehler** | `M109` |

**Fünf von sechs gingen still durch.** Zwei Ursachen, beide dieselbe Bauart:

1. **`PredArt::Klammer/Nicht/Und/Oder/Folgt` fielen in den Auffangzweig.** Damit war *jede
   zusammengesetzte Nachbedingung* ungeprüft — `M109` sah nur die atomare.
2. **`ExprArt::Eingebaut` ebenso.** `sizeof`, `lenof` und `aligned` tragen Namen; `aligned`
   trägt sogar zwei vollständige Ausdrucksbäume.

> **Und `M111` schwieg mit — das ist der teure Teil.** Seine Bedingung trägt
> `&& !namen.is_empty()`. Ein blinder Zweig sammelt keine Namen, also sah die Regel
> *„nichts zu sagen"* statt *„nichts gesehen"*. **Eine Blindheit, die sich als
> Unbedenklichkeit liest**, ist genau die Bewegung, gegen die W16 steht.

Seit dem 2026-08-21 trägt `sammle_namen_pred_geb` **keinen Auffangzweig mehr**: beide
`match`-Ketten sind vollständig. *Die nächste `PredArt`-Variante fällt nicht wieder still
hinein — sie bricht die Übersetzung.*

### `M120` — `Self` nennt den Träger, und eine Funktion ist keiner

`Self` steht im Korpus zwanzigmal, und **jedes Mal an einem Träger**: in der `invariant` einer
`table` (`forall s in slots of Self`, `beispiele/01`:70) oder an einem `format`
(`offset_into Self`, `lenof(Self)`, `beispiele/03`:18). An einer `fn` gibt es nichts, worauf
es zeigen könnte — `ensures` sitzt an einer Funktion, und eine Funktion steht nie in einer
`table`.

*Deshalb ist es eine eigene Absage und nicht `M109`.* `M109` sagte „is not declared here" und
schickte den Leser los, ein `Self` zu **erklären** — was die Sprache nicht zulässt. **Die
Absage war im Urteil richtig und im Rat falsch.**

Zwei Schreibweisen, und `typ_oder_ort` (`parse.rs`:1585) entscheidet zwischen ihnen am
nächsten Zeichen: **`Self` allein ist ein Typ, `Self.feld` ein Ort.** Beide müssen bei `M120`
ankommen, sonst fällt die eine und die andere nicht — was vor dem 2026-08-21 der Fall war.

## Hälfte (a): eine Zeile geschrieben — und sie wird nicht gelesen

Der K100-Posten hat zwei Hälften: *die Zeilen hinschreiben* und *den Prüfer sie tragen lassen.*
Die Warnung dazu ist scharf und richtig: **wer 70 Zeilen schreibt, die kein Pass liest, hat
die Zahl gehoben und nichts geändert.** Also wurde gesucht, wo eine Zeile *sowohl* durch das
Programm gerechtfertigt *als auch* von einem Pass gelesen wird.

**Gefunden wurde genau eine — und sie wird trotzdem nicht gelesen.**
`messung/fragmente/F10.gab`:21, der DTB-Leser:

```gabbro
extern fn naechstes_token(k : ptr<normal, r> DtbKopf, pos : u32) -> u32
    ensures result <= 9
    effects { reads k } costs <= 4 ops;
```

Die Schranke ist **nicht erfunden**: das Device-Tree-Format kennt genau fünf Token
(`FDT_BEGIN_NODE` 1 … `FDT_END` 9), und `@version 17` in derselben Datei nennt die Fassung,
die das festlegt. *Regel A ist erfüllt — die Zahl kommt aus dem Format, nicht aus dem Wunsch,
eine Kennzahl zu heben.*

Gemessen nach dem Einfügen:

```
$ gabbro zeugnis messung/fragmente/F10.gab
   2 foreign bodies (1 state their duty), 0 narrowings from foreign contracts
```

**Ausgesprochen: ja. Gelesen: nein.** Der Grund liegt am Ort des Rufs — er steht in der
`until`-Bedingung eines `retry`:

```gabbro
retry lesen until naechstes_token(k, 0) == 9
```

Nachgemessen an drei erfundenen Einheiten (`gabbro zeugnis`, jeweils dieselbe Klausel):

| Ort des Rufs | narrowings |
|---|---|
| `let t = tok();` | **1** |
| `if tok() == 9 { … }` | **2** |
| `retry lesen until tok() == 9` | **0** |

> **Die `until`-Bedingung eines `retry` wird von M1 nicht begangen.** Das ist dieselbe Bauart
> wie die fünf blinden `PredArt`-Zweige weiter oben — ein Zweig, den der Absteig nicht betritt
> — nur an einem anderen Konstrukt.

**Und es geht über die Verengung hinaus.** Ein Ruf an eine Funktion, die es *gar nicht gibt*,
fällt in einer `if`-Bedingung und fällt in einer `until`-Bedingung nicht:

```
if gibtsnicht() == 9 { … }
   -> Fehler: [K003] `nutze` promises costs, but `gibtsnicht` is not declared here

retry lesen until gibtsnicht() == 9 …
   -> 0 Fehler  (nur Hinweis E009 aus dem Wirkungsgraphen)
```

*Das ist ein eigener Posten und gehört nicht in diesen Bericht hinein, sondern in die
Übergabe* — `kosten.rs` ist nicht die Datei dieses Laufs. Er steht hier, weil er beim Messen
der einen geschriebenen Zeile herausfiel.

**Die Buchung dieser Zeile ist damit: `geschrieben, von keinem Pass gelesen` — Zustand
`UNGELESEN`, nicht `WIRKT`.** Genau die Trennung, für die das Zählwerkzeug gebaut wurde.

## NL.3 — die Ausnahme über Weltzustand, gemessen statt gemeint

Der Posten verlangt: *aufschreiben, bevor gebaut wird — und dazu die Zahl.* **Wie viele
nichtlokale Fakten würde eine Ausnahme von U4/U5 wiederbeleben, und an wie vielen Rufstellen?**

### Die Obergrenze der ganzen Frage

Gemessen mit einem Zähler in `aufruf_toetet_fakten` (temporärer Bau, `gabbro pruefe` über
`beispiele/*.gab messung/*/*.gab`):

```rust
fn aufruf_toetet_fakten(&self, lage: &mut Lage) {
    let _vorher = lage.fakten.len();
    lage.fakten.retain(|f| match f { … });
    eprintln!("MESSUNG_U4U5 {} {}", _vorher - lage.fakten.len(), self.rufer);
}
```

| | |
|---|---|
| **153** | Rufstellen, an denen U4/U5 überhaupt greift |
| **13** | Rufstellen, an denen mindestens ein nichtlokaler Fakt wirklich stirbt |
| **15** | nichtlokale Fakten, die im ganzen Korpus sterben |

**Mehr als 15 Fakten kann keine Ausnahme von U4/U5 je zurückgeben** — das ist alles, was die
Regel auf diesem Korpus überhaupt wegnimmt.

### Was die Ausnahme in ihrer gemeinten Form zurückgäbe: **null**

Die sechs Weltzustandsklauseln stehen alle in **einer** Datei, `beispiele/22-bootstrecke.gab`,
und werden alle aus **einer** Funktion gerufen, `hochlauf`. Gemessen:

```
$ grep "^MESSUNG_U4U5.* hochlauf$" msg.txt | sort | uniq -c
     12 MESSUNG_U4U5 0 hochlauf
```

**Zwölf Rufstellen, und an jeder sterben null Fakten.** Der Grund steht in derselben Datei:
die fünf Weltzustandsnamen (`mmu_an_zahl`, `caps_bereit`, `eps_bereit`, `gemeldet`, `faeden`)
werden **nirgends gelesen** — nicht in einer Bedingung, nicht in einem `requires`, nirgends.

```
$ grep -n "mmu_an_zahl\|caps_bereit\|eps_bereit\|gemeldet\|faeden" \
        beispiele/22-bootstrecke.gab | grep -v "^[0-9]*:--"
59:static mut mmu_an_zahl  : u32 = 0;      -- erklärt
77:    ensures  mmu_an_zahl == 1           -- versprochen
79:    effects  { … writes mmu_an_zahl }   -- geschrieben
                                            -- gelesen: NIRGENDS
```

> **Es gibt keine Stelle, an der die wiederbelebte Tatsache etwas entscheiden könnte.** Die
> Ausnahme, heute gebaut, veränderte an diesem Korpus **kein einziges Urteil** — sie kostete
> U4/U5 und kaufte null.

### Was daraus folgt — die Bedingung, die ein späterer Bau vorfinden soll

**Regel A ist nicht erfüllt: kein Konstrukt ohne ein Programm, das es gebraucht hat.** Der
Auslöser für den Bau ist damit benannt und messbar:

1. **Ein Programm im Korpus, das einen Weltzustandsnamen nach dem Ruf LIEST** — in einem
   `requires`, einer Bedingung oder einem `narrow`. Solange die Leseseite fehlt, ist die
   Ausnahme unbeobachtbar. *Der Zähler dafür steht: `MESSUNG_U4U5` an `hochlauf` müsste von
   0 abweichen.*
2. **Erst dann die Frage nach der Form** — und sie ist die schwierigere: ein `ensures` über
   einen globalen Platz gilt nur, solange **kein anderer** ihn schreibt. Ein zweiter Ruf, der
   `mmu_an_zahl` schreibt, macht die Tatsache falsch. Die Ausnahme braucht deshalb eine
   Rahmenbedingung (*„welche Rufe dürfen dazwischen stehen"*), und die hat U4/U5 heute
   gerade **nicht**, weil sie pauschal tötet.
3. **Die Obergrenze bleibt 15 Fakten an 13 Rufstellen** — auch bei perfekter Ausnahme. Das
   ist die Zahl, gegen die der Preis zu rechnen ist.

## Was diese Zahlen NICHT sagen

* **`UNGELESEN` heißt nicht „wirkungslos"**, sondern: an keiner Rufstelle *dieser Einheit*
  wurde daraus eine Tatsache. Eine Klausel an einer Funktion, die niemand ruft
  (`melde_roh`, `22-bootstrecke`:72), steht hier neben einer, die an jeder Rufstelle nichts
  bewegt (`41-handschlag`:101).
* **`STUMM` ist keine Anklage gegen die Bauform.** Eine Sperre *hat* eine Pflicht, und
  `zeugnis.rs` schreibt sie sogar auf. Gezählt wird, dass die Zeile nicht dort steht, wo der
  Nutzer sie schreiben und der Prüfer sie lesen könnte.
* **Die Aufschlüsselung von `UNGELESEN` nach `result` ist ein Textgriff**, kein Parser. Sie
  liest die `ensures`-Zeile aus der Quelle. Greift sie daneben, sagt sie es (`!! VOM
  TEXTGRIFF VERFEHLT`) statt in den häufigeren Topf zu fallen — *das war zuerst nicht so:
  `mmu_an` fiel still in „Weltzustand", weil `beispiele/22` seine eigene Deklaration in
  Zeile 26 noch einmal als Kommentar führt und der erste Treffer der Kommentar war.*
* **Die 15 gestorbenen Fakten sind über diesen Korpus gemessen**, nicht über Gabbro. Ein
  Programm mit mehr globalem Zustand hätte mehr.
* **Nichts hiervon sagt, ob eine Zusage STIMMT.** Nur, dass Gabbro sie glaubt.

## Die Proben, die rot werden können

Sechs Giftproben, jede fällt mit ihrem Code (`cargo test`,
`jedes_gift_faellt_mit_seinem_code`):

| Probe | Code | Was sie fängt |
|---|---|---|
| `223-self-im-ensures-ohne-traeger.gab` | `M120` | `Self` als Ort in einer Nachbedingung |
| `224-self-als-typ-in-lenof.gab` | `M120` | `Self` als **Typ** — die Schreibweise, die gar nicht fiel |
| `225-tippfehler-in-sizeof.gab` | `M109` | Tippfehler in `sizeof(...)` |
| `227-tippfehler-in-aligned.gab` | `M109` | Tippfehler in `aligned(...)` — zwei blinde Ausdrucksbäume |
| `228-tippfehler-hinter-dem-und.gab` | `M109` | rechte Hälfte eines `&&` |
| `229-tippfehler-unter-der-negation.gab` | `M109` | unter einem `!` — die im Korpus häufigere Form |

Und sechs Mutationen in `instrumente/mutiere-pruefer.py` (`# --- Stufe 6, Teil C ---`), jede
nimmt genau **einen** Zweig zurück:

```
self-im-ensures-geht-durch          self-als-typ-bleibt-unsichtbar
sizeof-und-lenof-bleiben-blind      aligned-bleibt-blind
und-oder-folgt-bleiben-blind        negation-und-klammer-bleiben-blind
```

Das Zählwerkzeug selbst trägt eine Sprechprobe über **vier** erfundene Einheiten, eine je
Zustand — der Unterschied zwischen `WIRKT` und `UNGELESEN` ist dabei **ein Zeichen** der
Untergrenze (`u32 in 0 ..` gegen `u32 in 1 ..`):

```
== Sprechprobe, in beide Richtungen -- eine Einheit je Zustand ==
  wirkt      erwartet WIRKT      gemessen ['WIRKT']      ok
  ungelesen  erwartet UNGELESEN  gemessen ['UNGELESEN']  ok
  schweigt   erwartet SCHWEIGT   gemessen ['SCHWEIGT']   ok
  stumm      erwartet STUMM      gemessen ['STUMM']      ok
  Gegenrechnung gegen die BEFUND-Zeile: stimmt
```

## Abweichungen von der Buchführung, nachgerechnet

| gebucht (TODO, Stufe 6) | gemessen | Befehl |
|---|---|---|
| 109 fremde Rümpfe | **109** — bestätigt | `./instrumente/zaehle-fremdpflichten.py` |
| 10 sprechen ihre Pflicht aus | **10** — bestätigt (11 nach dieser Stufe) | `./instrumente/zaehle-fremdpflichten.py` |
| 1 verengt wirklich | **1** — bestätigt | `./instrumente/zaehle-fremdverengung.py` |
| 6 nennen `result` nicht / 2 bewegen nichts / 1 ungerufen | **6 / 2 / 1** — bestätigt | `./instrumente/zaehle-fremdpflichten.py` |
| *„die Zeilen hinschreiben (kostet nichts)"* | **falsch für 31 von 109** | siehe oben, `LockDecl` hat kein `ensures`-Feld |
| *„`Self` … heute kein Fehlalarm"* | **bestätigt** — und die zweite Schreibweise fiel gar nicht | `beispiele/gift/224-*.gab` |
| *„`ensures mmu_an_zahl == 1` steht **siebenmal** in `beispiele/22`"* (NL.3 / «H2») | **sechsmal** — die siebte Klausel der Datei ist `melde_roh :: result <= 4096` und nennt `result` | `./instrumente/zaehle-fremdpflichten.py` |
| *„Von **28** fremden Deklarationen liefern nur 4 eine Ganzzahl"* («H2») | **veraltet** — heute 109 fremde Rümpfe, davon 78 mit einem Ort für die Zeile | `./instrumente/zaehle-fremdpflichten.py` |

**Die Buchführung dieses Ordners schönt nicht, sie veraltet.** In dieser Stufe stimmten die
Hauptzahlen alle; veraltet waren zwei Nebenzahlen, und falsch war ein **Satz**, keine Zahl:
*dass das Hinschreiben nichts kostet.* Für 31 von 109 Rümpfen kostet es eine Grammatikänderung
— und für die eine Zeile, die dieser Lauf geschrieben hat, kostete es einen Pass, der sie
liest und den es noch nicht gibt.
