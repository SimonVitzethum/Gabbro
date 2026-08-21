# Träger und Hardware — «B38» gebaut, «B39» gemessen und nicht gebaut

**Gemessen und gebaut am 2026-08-21.** Zwei Posten aus Welle 4, und sie enden verschieden:
**«B38» bekommt eine Regel (`H101`), «B39» bekommt eine Zahl und keinen Bau.**

> **Jede Zahl unten nennt den Befehl, der sie nachrechnet.** Wo ein Befehl `cargo` ruft,
> lief er auf `ki-pc-fisch-101:gabbro-e` — lokal fällt `rustc` unter die 1-GB-Grenze.

---

# Teil 1 — «B38»: die Nebenbedingung am benannten Träger

## Der Satz, um den es geht

`dokumente/FRAGMENTE.md` F8 misst fünf Werte, die im Planer eine **Sperrgrenze überqueren**
und danach unter einer anderen Sperre benutzt werden. Drei tragen das Muster *„die
Fortsetzung prüft neu"*; **zwei nicht** — sie ruhen auf der Interruptmaskierung, und das sind
die heißesten Pfade (`exit_current`, die IPC-Übergabe). Die ehrliche Form heißt darum

> *„jede Fortsetzung prüft neu **oder nennt, was sie stattdessen trägt** — und ein Träger
> `masks IRQ` zählt nur, wenn der Eintrittskontext `nested masked` trägt."*

**Die zweite Hälfte ist nicht schmückend.** Ohne sie sagt `masks IRQ` in einer Wirkungsliste,
dass die Funktion **maskiert** — nicht, dass sie **maskiert läuft**. Das ist die Zusicherung
aus **R15**: erfüllt, sobald der Prüfer schweigt.

## Zuerst gemessen: was steht heute im Korpus?

```
$ grep -rn "masks " --include=*.gab . | grep -v ":--" \
      | grep -v "ops masks irqs" | grep -v "rank 0 masks irqs"
$ grep -rn "^ *stack " --include=*.gab .
```

**Die drei Zahlen, nach denen der Auftrag verlangt** — Stand **vor** der neuen Giftprobe:

| | Zahl | wo |
|---|---:|---|
| Träger `masks X` in einer `effects`-Liste, ganzer Korpus | **4** | F08 · Gift 139 · 140 · 152 |
| davon an einem `entry` mit `nested masked` | **0** | — |
| davon an einem `entry` **ohne** `nested masked` | **1** | `beispiele/gift/152` (`nested never`) |
| davon von **keinem** `entry` erreicht | **3** | F08 · Gift 139 · 140 |
| in `beispiele/*.gab` (47 saubere Dateien) | **0** | — |

**Nach der Giftprobe sind es 5 Träger** — dieselbe Zählung, einer mehr. *Die Tabelle nennt
den Stand, auf dem die Entscheidung ruht; die 5 ist die Zahl, die der Befehl heute druckt:*

```
$ grep -rh "masks " --include=*.gab . | grep -v "^--" \
      | grep -v "ops masks irqs" | grep -v "rank 0 masks irqs" | wc -l
5
```

**`nested masked` hat null Fundstellen.** Neun `entry`-Deklarationen stehen im Korpus: sieben
`nested never`, eine `nested bounded 2`, eine ohne `nested`. *Das Wort steht seit jeher in der
Grammatik (`SYNTAX.md`:243) und hat nie ein Programm gehabt.*

```
$ grep -rh "^ *stack " --include=*.gab . | grep -c "nested masked"
0
```

> **Was diese Zahlen NICHT sagen.** Sie zählen `masks` als **Wirkung**. Die fünf
> `lock … masks irqs`-Zeilen (`beispiele/01`, `/05`, `caprock/kapraum`, `caprock/planer`,
> `fragmente/F01`) sind ein Sperrattribut, kein Träger, und stehen absichtlich nicht in
> der Tabelle.
>
> *Und dieses Attribut ist selbst unbewacht:* `./pruefe-klauseln.py` führt
> `maskiert / LockDecl` unter **UNGELESEN** — *„der Leser füllt sie, niemand sieht hin"*.
> **`H101` fasst es nicht an**, und das ist eine eigene Lücke mit einer eigenen Adresse.

## Und dann die Handprobe, die den Posten scharf macht

**Die Frage war nicht, ob die Kopplung fehlt, sondern was ihr Fehlen kostet.** Zwei Dateien,
Zeichen für Zeichen gleich bis auf `masks IRQ`:

```
$ ./target/debug/gabbro pruefe probe-schlupfloch.gab   # masks IRQ + assume ein_kern, nested never
  5 Items, 0 Fehler, 0 Hinweise
$ ./target/debug/gabbro pruefe probe-ohne-masks.gab    # dieselbe Datei OHNE masks IRQ
  [H013] this entry writes `z`, and nothing declares it shared
  5 Items, 1 Fehler, 0 Hinweise
```

**Ein Wort in der Wirkungsliste kaufte die Ausnahme von `H013`.** Der Weg schrieb einen
ungeschützten Weltzustand, der Eintritt trug `nested never` — und der Prüfer schwieg, weil
`geteilt.rs`:450-451 `crate::kontexte::ein_kern_deckt(maskiert, k)` fragt und `maskiert` allein aus
der Wirkungsliste kommt. *Die Ausnahme war käuflich.*

Dieselbe Messung noch einmal mit einer Datei, die im Baum steht — vor und nach dem Bau,
**dasselbe Binärprogramm nur einmal neu gebaut**:

```
vorher   $ ./target/debug/gabbro pruefe beispiele/gift/231-traeger-ohne-nested-masked.gab
           5 Items, 0 Fehler, 0 Hinweise
nachher  $ ./target/debug/gabbro pruefe beispiele/gift/231-traeger-ohne-nested-masked.gab
           [H101] `sc` reaches a carrier `masks IRQ` but does not declare `nested masked`
           5 Items, 1 Fehler, 0 Hinweise
```

## Was gebaut wurde — `H101`

`crates/gabbro-check/src/kontexte.rs`, verdrahtet in `lib.rs::pruefe` direkt hinter `geteilt`.
**Keine eigene Passnummer**: die Regel gehört zur Kontextmatrix («K5.3»), also in die Spalte
von Pass 12, nicht in eine neue. *Ein Pass, der sich in die Nummerierung einer Spezifikation
drängt, verschiebt jede Fundstelle, die auf sie zeigt.*

> **`H101` und nicht `H015`.** Alle `H0xx` gehören `geteilt.rs`; `pruefe-kennungen.py` verlangt
> eine Kennung je Datei. Der Hunderterbereich ist der vorhandene Weg dafür — `L001…L007`
> liegen in `geteilt.rs`, `L101…L109` in `m2.rs`.

**Die Regel, mechanisch:** für jeden Ausführungskontext wird die Hülle seiner `dispatch`-Wurzel
gerechnet. Nennt sie eine Wirkung `masks …` und trägt der Eintritt **nicht** `nested masked`,
fällt `H101` an der `entry`-Deklaration.

**`nested never` zählt ausdrücklich nicht.** `never` sagt, dass der Vektor sich nicht selbst
wieder betritt; `masked` sagt, in welchem **Zustand** er läuft. *Über eine Sperrgrenze trägt der
Zustand, nicht die Abwesenheit von Wiedereintritt.* Dieselbe Schnittkante wie bei `H005`: dort
entscheidet die Stärke des Zeugen, hier der Zustand am Eintritt.

**Und `H101` sagt über einer UNVOLLSTÄNDIGEN Hülle ab, `H013` nicht — mit Grund.** `H013` löst
auf **Abwesenheit** aus (nichts erklärt den Platz geteilt), und eine untere Schranke darf keine
Abwesenheit belegen (R16). `H101` löst auf **Anwesenheit** aus, und die Wirkungsmenge wächst nur:
was in der abgeschnittenen Hülle steht, steht auch in der vollen. *Die Gegenrichtung — ein Träger,
den die abgeschnittene Kante verbirgt — bleibt möglich, und darum druckt der Bericht die Zahl
`contexts with an incomplete hull` daneben.*

## Der Nebenbefund, und er ist die unangenehmere Hälfte

**Die von `H101` verlangte Abhilfe war nicht schreibbar.** `kontexte::erhebe` las
`entryextra` an genau einer Stelle:

```rust
nie_verschachtelt: matches!(e.verschachtelt, Some(Verschachtelt::Nie)),
```

`Verschachtelt::Maskiert` und `::Begrenzt` kannte außer dem Erzeuger niemand. Die Folge war ein
**Widerspruch**: `nested never` bekam die `H013`-Ausnahme, `nested masked` nicht — obwohl
`masked` genau die Prämisse der Ausnahme ausspricht und `never` sie nur nahelegt.

```
$ ./target/debug/gabbro pruefe probe-gedeckt.gab      # nested masked, vor der Zeile
  [H013] this entry writes `z`, and nothing declares it shared
$ ./target/debug/gabbro pruefe probe-gedeckt.gab      # nach der Zeile
  5 Items, 0 Fehler, 0 Hinweise
```

> **Eine Regel, deren Abhilfe eine andere Regel auslöst, ist keine Abhilfe.** `ein_kern_deckt`
> nimmt `nested masked` jetzt mit; die Ausnahme bleibt an `assume ein_kern` mit Falsifikator
> gebunden. **Genau die Lochform, vor der die Übergabe gewarnt hat:** ein `match`-Zweig, den
> kein Leser hatte.

## Die Zahl neben dem Urteil — und was sie NICHT sagt

`gabbro kontexte` druckt seit heute eine Trägerzeile, und zwar **vor** dem Abbruch bei null
Kontexten. Genau dort heißt sie etwas:

```
$ ./target/debug/gabbro kontexte messung/fragmente/F08.gab
contexts: 0   ·   assumption `ein_kern`: no -- nothing is exempt
carriers `masks …` declared: 1   ·   reached by a context: 0   ·   backed by `nested masked`: 0
                            ·   UNBACKED (H101): 0   ·   contexts with an incomplete hull: 0

  **1 declared carrier(s) are reached by NO visible context.** They are not
  cleared, they are unseen -- in a unit without an `entry` nobody asks (W10).
```

**Drei der vier gemessenen Träger stehen in Einheiten ohne `entry`.** `H101` schweigt dort, und
das ist keine Freisprechung: der Prüfer kann den Kontext nicht sehen. *Das ist dieselbe Grenze
wie `E009` an der Dateigrenze — sie verschwindet mit der ABI, nicht mit dieser Regel.*

**Und eine zweite Grenze, am Werkzeug selbst:** `gabbro kontexte` weigert sich über einer Datei
mit Fehlern („no register"). Die Trägerzeile ist damit **genau dort stumm, wo die Regel
beißt** — für die vier Gift-/Fehlerdateien musste die Zahl aus `grep` und `gabbro pruefe`
kommen. *Das ist die W1-Lücke des Berichts, und sie steht hier statt in einer Fußnote.*

## Beißt die Regel — und zerlegt sie den Korpus?

```
$ for f in beispiele/*.gab beispiele/gift/*.gab messung/*/*.gab messungen/*.gab; do
      ./target/debug/gabbro pruefe "$f" 2>&1 | grep -c "\[H101\]"; done
beispiele/gift/152-eintritt-maskiert-ohne-annahme.gab: 1
beispiele/gift/231-traeger-ohne-nested-masked.gab:     1
```

**Zwei Fundstellen, beide im Gift, null in den 47 sauberen Beispielen.** Die einzige
vorbestehende (`152`) war schon rot (`H013`); die Giftprobe prüft auf *enthält*, nicht auf
*genau*, also bleibt ihre Erwartung `H013` gültig. **Der Korpus wird nicht zerlegt.**

## Proben in beide Richtungen

| | wo | was |
|---|---|---|
| **Gift** | `beispiele/gift/231-traeger-ohne-nested-masked.gab` | `nested never` + Träger → `H101` |
| **Test, fallend** | `rechenwerk.rs::ein_traeger_masks_irq_verlangt_nested_masked` (1) | dasselbe als Einheitentest |
| **Test, schweigend** | dieselbe Probe (2) | `nested masked` → **gar keine** Absage, nicht bloß kein `H101` |
| **Test, abgrenzend** | dieselbe Probe (3) | ohne Träger fällt `H101` nicht, `H013` schon |
| **Test, Zahl** | `rechenwerk.rs::ein_unerreichter_traeger_wird_gezaehlt_statt_verschwiegen` | erklärt / erreicht / gedeckt |
| **Mutation** | `traeger-ohne-nested-masked-geht-durch` | `H101` verstummt |
| **Mutation** | `nested-masked-deckt-nicht-mehr` | die Abhilfe wird unschreibbar |

```
$ ssh ki-pc-fisch-101 'cd gabbro-e && cargo test'
  163 Tests, 0 fehlgeschlagen                       (vorher 161)
$ ssh ki-pc-fisch-101 'cd gabbro-e && python3 mutiere-pruefer.py'
  == 242 von 242 gueltigen Mutationen gefangen (100 %) ==      real 3m26s   (vorher 240)
```

---

# Teil 2 — «B39»: gemessen, **nicht gebaut**

## Der Kandidat

> `A`/`D` werden von der MMU selbst geschrieben — ein Schreiber, den keine `effects`-Zeile
> nennt. **Sobald Gruppen-`ops` die Seitenmaschinerie erreichen, kollidiert das
> Hardwareaxiom mit dem Schreibrechteversprechen:** die K-Bedingung verlangt, dass ALLE
> Schreibstellen erzeugt sind. Welche Felder einer `walk`-Deklaration
> **hardwareschreibbar** sind, gehörte an die Deklaration — Kandidatenzeile `hardware A, D;`,
> so wie `reserved` an ein `format`-Feld.

**Regel A verbietet den Bau ohne gemessenen Bedarf.** Also gemessen.

## 1. Tritt die Kollision heute ein? — **Nein, und sie kann es nicht**

| Frage | Zahl | Befehl / Fundstelle |
|---|---:|---|
| `walk`-Deklarationen im ganzen Korpus | **3** | `grep -rn "^walk \|^ *walk " --include=*.gab .` |
| `group`-Deklarationen | **6** | `grep -rn "^group \|^ *group " --include=*.gab .` |
| `group`, die einen `walk`-Träger nennt | **0** | alle sechs sind `over { Endpunkte, Faeden }` |
| `ops`-Klausel an einer `group` **in der Grammatik** | **gibt es nicht** | `SYNTAX.md`:1055 `gruppedecl` |
| `by ops` an einem `walk`-Feld **in der Grammatik** | **gibt es nicht** | `SYNTAX.md`:857 `walkdecl` — `node`/`down`/`leaf`/`invariant`, kein `slot` |
| `table`-Deklarationen mit `ops`-Klausel | **6** | `grep -rn "^ *ops [a-z]" --include=*.gab .` |

> **Die Kollision setzt zwei Formen voraus, die die Grammatik nicht hat.** `group` trägt
> Invarianten, keine Operationen; `walk` trägt `node`/`down`/`leaf`, keine `slot`-Felder und
> damit kein `by ops`. *Die K-Bedingung erreicht die Seitenmaschinerie heute an keiner
> einzigen Stelle — nicht selten, sondern gar nicht.*

## 2. Wo genau sieht `R001` die MMU nicht?

`R001` (`m3.rs`:393-440) fragt genau eines: steht ein **Funktionsparameter** als
`ptr<dma, …>` auf einer `table`, die `ops` deklariert? Zwei Bedingungen, und die
Seitenmaschinerie erfüllt keine.

```
$ ./target/debug/gabbro pruefe b39-c-walk-im-dma.gab   # walk-Traeger, ptr<dma, rw>
  6 Items, 0 Fehler, 0 Hinweise
$ ./target/debug/gabbro pruefe beispiele/gift/58-ops-traeger-im-dma-raum.gab   # Gegenprobe
  [R001] `r` points into the `dma` space at `Ring`, and that table declares `ops`
```

**Die Gegenprobe steht daneben, weil eine stille Regel wie eine erfüllte aussieht** (W10):
`R001` **kann** fallen, es sieht nur keinen `walk` — in *keinem* Raum, nicht bloß im
`normal`-Raum. *Der Satz in `FRAGMENTE.md`, `R001` schreibe „nur im `normal`-Raum" vorbei,
ist zu freundlich: die Platzierungsregel kennt `walk` als Träger überhaupt nicht.*

## 3. Der Grenzfall: sagt der Prüfer etwas über A/D? — **Nein**

**Die A/D-Bits stehen im Korpus, als ganz gewöhnliche Formatfelder:**
`beispiele/07-eintritt-und-boot.gab`:48-49 (`benutzt : bool @5`, `schmutzig : bool @6`),
ebenso `beispiele/03-format.gab`:66-67 und `messung/fragmente/F09.gab`:63 (`A @5, D @6`).

**Und das Axiom steht auch da** — als Zeichenkette:

```
$ ./target/debug/gabbro annahmen beispiele/06-annahmen.gab
A7  mmu_schreibt_nur_a_und_d  assume  nicht-falsifizierbar
    "Die MMU setzt in einem Seitentabelleneintrag ausschliesslich die Bits A und D; …"
-- 13 Annahmen
```

```
$ grep -rn 'annahmen(baum)' --include=*.rs crates/gabbro-check/src/
kontexte.rs:308 · geteilt.rs:440 · namen.rs:485 · namen.rs:2127 · schleifen.rs:40
$ grep -rn '"ein_kern"' --include=*.rs crates/gabbro-check/src/
kontexte.rs:309 · geteilt.rs:440
```

> **`ein_kern` ist der EINZIGE Annahmenname, den der Prüfer mechanisch liest.**
> `mmu_schreibt_nur_a_und_d` wird gezählt, gedruckt und ins Zeugnis geschrieben — und von
> keinem Pass gelesen. Es ist **nicht** mit `Pte.benutzt`, mit `walk` oder mit irgendeiner
> Rahmenaussage verknüpft. *`beispiele/06-annahmen.gab` enthält nicht einmal eine
> Seitenmaschinerie: kein `walk`, kein `format Pte`, keine `table`, kein `device`.*

**Die Antwort auf die gestellte Frage lautet also: das Axiom ist stumm.** A/D sind eine
Schreibstelle, die kein Gabbro-Code erzeugt, und keine Regel kennt sie. Was der Name kauft, ist
**Sichtbarkeit** — A7 steht in `gabbro annahmen` und im Zeugnis, mit dem Vermerk
*nicht-falsifizierbar* und dem Grund dafür. Das ist mehr als nichts und weniger als eine Regel.

## 4. Und die Analogie trägt nicht: `reserved` hat selbst keine Absage

Der Kandidat begründet sich mit *„so wie `reserved` an einem `format`-Feld"*. Also nachgesehen,
was `reserved` mechanisch tut:

```
$ grep -rn "reserviert" --include=*.rs crates/gabbro-check/src/
emit.rs:2228 · emit.rs:2383 · zeremonie.rs:585

$ ./pruefe-klauseln.py
-- NUR GETRAGEN: 16 --
   abgesenkt oder berichtet, von keinem Pass geprueft.
   reserviert   FeldDecl   emit.rs:2228,2383, zeremonie.rs:585
```

**Kein Prüfpass liest es — und das steht seit jeher in einem Register**, nur hat es
niemand gegen die `hardware`-Analogie gehalten. Ein Schreiben in ein `reserved`-Feld
geht durch:

```
$ ./target/debug/gabbro pruefe b39-a-reserved-schreiben.gab
  3 Items, 0 Fehler, 0 Hinweise
```

**Und die Kontrollprobe sagt, dass diese Null wenig wert ist** (W16 — ein Werkzeug, das eine
Mischung misst, sieht plausibel aus):

```
$ ./target/debug/gabbro pruefe b39-kontrolle-feld-gibts-nicht.gab   # p.gibts_nicht = 1;
  3 Items, 0 Fehler, 0 Hinweise
```

*Ein Feld, das es gar nicht gibt, fällt genauso wenig.* Die Messung kann **„`reserved` beißt
nicht"** nicht von **„ein Feldschreiben über einen Zeiger wird überhaupt nicht aufgelöst"**
trennen — dieselbe Klasse wie `TODO.md`s „Ein unbekannter TYPNAME fällt nirgends".

**Was dabei nebenher herausfiel, ist der schärfere Befund:**

```
$ gabbro emit b39-a-reserved-schreiben.gab > b39a.c
$ cc -std=c11 -Wall -Wextra -c b39a.c
b39a.c:37:5: error: Implizite Deklaration der Funktion »Pte_setz_pte_frei«
```

Der Erzeuger **ruft** einen Setzer für ein `reserved`-Feld und **definiert** ihn nicht
(`emit.rs`:2228 überspringt reservierte Felder). **`reserved` beißt heute im C-Übersetzer,
nicht im Prüfer** — mit der falschen Meldung, im falschen Werkzeug, hinter dem Rücken der elf
geprüften Klassen. *Wer `hardware A, D;` mit der `reserved`-Analogie begründet, erbt diese
Lage.*

## 5. Was ein Bau kosten würde

| Ort | was daran hinge |
|---|---|
| `gabbro-syntax/src/kw.rs` | ein **neues reserviertes Wort** `hardware` — Spalte 1 der Wette |
| `gabbro-syntax/src/parse.rs`, `ast.rs` | `walkdecl` bekommt eine Zeile; `Verschachtelt`-Lehre: **jeder neue Zweig braucht einen Leser** |
| `dokumente/SYNTAX.md` | EBNF 146 → 147 Regeln, Wortschatz 216 → 217 Terminale (`pruefe-syntax.sh` hält beide) |
| `kbedingung.rs` | die K-Bedingung müsste die hardwareschreibbaren Felder **ausnehmen**, statt sie zu fordern |
| `wirkungen.rs` | die Rahmenaussage *„nur was dasteht, ändert sich"* wird an dieser Stelle falsch — der Ausnahmegrund gehört benannt |
| `m3.rs` (`R001`) | die Platzierungsregel müsste `walk` als Träger überhaupt erst kennen |
| `emit.rs`, `zeugnis.rs` | Absenkung und Buchung (K100.4 verlangt: was absenkt, wird eingeordnet) |
| `blindstellen.rs` | eine neue Zelle Form × Stellung |
| Korpus | Giftprobe, Mutation, eine Zeremonieregel (`T…`), und ein Programm, das die Form **braucht** |

## 6. Das Urteil: **nicht bauen**

1. **Die Kollision tritt nicht ein** und kann es nicht: `group ops` und `by ops` am `walk`
   existieren beide nicht in der Grammatik. Der Bedarf ist **null Fundstellen**, nicht
   „wenige".
2. **Regel A ist damit verletzt**, wenn gebaut würde: kein Programm hat die Form gebraucht.
   *Dieselbe Bewegung, die `locks ordered` getötet hat.*
3. **Es wäre Spalte 1 der Konvergenzwette.** F7–F10 stehen bei **null neuen Konstrukten**
   (`MESSUNGEN.md`:3557-3560); `hardware A, D;` machte aus der Null bei F9 eine Eins — und
   die Wette wird genau an dieser Spalte zitiert.
4. **Die Analogie trägt nicht** (Punkt 4 oben): `reserved` hat keine Prüferregel, sondern
   einen Übersetzerfehler.

> **Was stattdessen bleibt, hat schon einen Ort.** A7 steht in der Axiomschicht, als
> *nicht-falsifizierbar* mit Grund — das ist die Buchung aus K100.2, und sie ist keine
> Entlastung, sondern eine benannte Last. *Der Bau wird fällig, wenn die Seitenmaschinerie
> einen erzeugten Träger bekommt; bis dahin ist er eine Zusage ohne Einlöser.*

---

## Was diese Messung NICHT sagt

* **Sie spricht `masks IRQ` nicht frei.** `H101` prüft die **Kopplung**, nicht die
  Maskierung selbst: dass maskierte Interrupts auf einem Kern wirklich tragen, ist A5
  (`masks_irq_schuetzt_wie_eine_sperre`) und bleibt eine Annahme mit Sonde.
* **Sie deckt keine Bibliothek.** Drei der vier Träger stehen in Einheiten ohne `entry`;
  dort schweigt `H101`, und das verschwindet mit der ABI, nicht mit dieser Regel.
* **Sie sagt nichts über die erste Hälfte von «B38».** *„Ein Wert über eine Sperrgrenze
  verliert seine Fakten"* — dass die V-Regeln an der Grenze sterben, ist hier nicht
  nachgemessen worden.
* **Die B39-Nullen sind Grammatiknullen, keine Bedarfsnullen.** Sie sagen: die Form ist
  heute nicht schreibbar. Sie sagen nicht, dass niemand sie schreiben wollte.
