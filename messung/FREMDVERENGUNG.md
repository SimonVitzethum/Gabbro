# Die Zusage eines fremden Rumpfs ist eine Tatsache im Prüfer — und sie entscheidet

> **Gemessen am 2026-08-21.** Gegenstand ist nicht, ob eine `ensures`-Zeile an einem
> rumpflosen `extern fn` *dasteht*, sondern ob sie im Rufer **etwas bewegt**. Das sind zwei
> verschiedene Zahlen, und bis heute stand nur die erste irgendwo.

## Der Befehl

```
./instrumente/zaehle-fremdverengung.py                 -- die Zahl für den ganzen Korpus
./instrumente/zaehle-fremdverengung.py --stellen       -- jede Stelle mit Datei, Zeile und Klausel
./instrumente/zaehle-fremdverengung.py --sprechprobe   -- nur die Sprechprobe, in beide Richtungen
gabbro zeugnis <datei.gab>                 -- dieselbe Zahl je Datei, Abschnitt F
```

Alles davon gehört auf `ki-pc-fisch-101` (`cargo run`, `CLAUDE.md`).

## Die Zahl

```
== 1 wirksame Fremdverengungen aus 10 ausgesprochenen Verträgen, 57 von 61 Dateien mit Zeugnis ==
   109 fremde Rümpfe insgesamt; 4 Dateien tragen Fehler und haben kein Zeugnis.
```

| | |
|---|---|
| **109** | fremde Rümpfe im Korpus (`beispiele/*.gab` + `messung/*/*.gab`) |
| **11** | davon **sprechen ihre Pflicht aus** — `ensures` oder `maintains` an einer Deklaration ohne Rumpf |
| **1** | davon **verengt wirklich** etwas beim Rufer |

Die eine Stelle:

```
F  FOREIGN CONTRACTS THAT NARROWED -- a foreign `ensures` became a FACT here
     127:   abarbeiten -> naechste_menge           range     result >= 1
            u32 in 0 .. 4096  ->  u32 in 1 .. 4096
```

## Warum die anderen neun nichts bewegen — und das ist der Ertrag der Messung

**Sechs von zehn nennen gar nicht `result`.** `beispiele/22-bootstrecke.gab` sagt
`ensures mmu_an_zahl == 1`, also eine Aussage über den **Weltzustand**. Der Prüfer liest aus
einem fremden `ensures` nur `result <op> <Zahl>` und `result <op> <Ort>`; alles andere bleibt
liegen (W10, und es steht als solches im Modulkopf).

**Zwei weitere nennen `result` und bewegen trotzdem nichts** — weil die Grenze schon dort
steht. Die dritte Zeile steht zum Vergleich daneben:

| Datei | Klausel | Ergebnistyp | bewegt |
|---|---|---|---|
| `beispiele/41-handschlag.gab`:101 | `result >= 1` | `Laenge = u32 in 1 .. 4096` | nichts |
| `beispiele/06-annahmen.gab`:115 | `result >= 1` | `Stapelgroesse = u64 in 1 .. 1048576` | nichts |
| `beispiele/39-auftragsdienst.gab`:115 | `result >= 1` | `Rest = u32 in 0 .. 4096` | **`0 ..` → `1 ..`** |

> Drei Zeilen, wortgleich, an derselben Bauform — und **eine davon ist Vertrauensfläche mit
> Wirkung, zwei sind Zierde.** Genau deshalb zählt das Zeugnis die *wirksame* Verengung und
> nicht die vorhandene Klausel.

**Und die vierte `result`-Klausel ist tot, ohne dass ihr etwas fehlt:**
`beispiele/22-bootstrecke.gab`:72
erklärt `melde_roh(...) -> u32 ensures result <= 4096` — die Form, die verengen *würde*. Die
Funktion wird in der Einheit nirgends gerufen. *Eine Verengung ohne Rufstelle ist keine.*

## Hälfte (a): die Fläche wird schon geführt — nachgeprüft, nicht angenommen

Handprobe an einer echten Korpusdatei, `beispiele/22-bootstrecke.gab` — der Datei mit den
meisten ausgesprochenen Fremdpflichten des Korpus:

```
$ gabbro zeugnis beispiele/22-bootstrecke.gab
E  FOREIGN -- the generator writes the prototype, somebody else the body

     The bodies this unit does NOT write, and the contract
     the checker uses to reason about them:
       melde_roh                  effects { reads text }, mit `costs`, ensures (1)
       mmu_an                     effects { consumes p, writes mmu_an_zahl }, mit `costs`, ensures (1)
       …
     0 assumptions, 0 templates (0 of them UNPROVED), 4 direct forms,
     7 foreign bodies (7 state their duty), 0 narrowings from foreign contracts

$ gabbro pflichten beispiele/22-bootstrecke.gab
F  Foreign duty (7)
     melde_roh :: ensures #1
     …
== 7 obligations: 0 preservation, 0 postcondition, 7 foreign, 0 precondition ==
```

**Die Fläche steht also wirklich schon da**, an zwei Stellen und mit Namen: `zeugnis`
Abschnitt E (was der Prüfer glaubt) und `pflichten` Klasse `F` (was ein Mensch schuldet).
*(a) war eine Buchung und keine Lücke.* Neu ist ausschließlich die letzte Zahl der
Befundzeile — und sie steht dort, weil eine Fläche und eine Wirkung zwei verschiedene Dinge
sind.

## Was diese Zahl NICHT sagt

* **Sie ist eine UNTERE Schranke der Fläche.** Gezählt wird nur über Einheiten, aus denen ein
  Zeugnis entsteht, und das entsteht nur ohne Fehler. Vier Fragmentdateien (`F01`, `F03`,
  `F05`, `F09`) tragen heute Fehler und sind nicht gemessen; die 222 Giftdateien sind
  bauartbedingt abgewiesen und werden gar nicht erst angesehen.
* **Sie ist in der anderen Richtung eine OBERE Schranke der GEBRAUCHTEN Tatsachen.** Gebucht
  wird, dass eine Tatsache *entstanden* ist — nicht, dass irgendeine Absage später auf ihr
  ruht. Für die relationale Hälfte (`ensures result <= s.len`, `Fakt::Beziehung`) gilt das
  besonders: eine Beziehung, die niemand liest, zählt hier trotzdem.
* **Sie sagt nichts darüber, ob die Zusage stimmt.** Sie sagt, dass Gabbro sie glaubt. Ein
  fremder Rumpf, der `result >= 1` verspricht und `0` liefert, macht die Verengung falsch —
  und diese Übersetzung sagt darüber nichts. *Wer nicht prüfen kann, exportiert.*
* **Sie sagt nichts über `impl fn`.** Dieselbe Verengung an einem Rumpf, den Gabbro sieht,
  ist eine Ableitung, die Gabbro einmal selbst nachrechnen wird. Sie steht bewusst nicht in
  dieser Zahl — sonst wäre die Vertrauensfläche zu groß statt zu klein.

## `M115` — die Gegenrichtung, und warum sie NICHT dieselbe Klasse ist

`m1::requires_pruefen` liest das `requires` des **fremden** Gerufenen und sagt am Rufort ab
(`M115`), wo der Bereich des Arguments die Vorbedingung ausschließt. Auch dort entscheidet
ein fremder Vertrag über die Annahme eines Programms. Trotzdem steht sie nicht in Abschnitt F:

| | `ensures` → Verengung | `requires` → `M115` |
|---|---|---|
| Richtung | der Prüfer glaubt **mehr** | der Prüfer glaubt **weniger** |
| Fehlerfolge | ein falsches Programm geht durch | ein richtiges Programm wird abgewiesen |
| Wirkung im Erzeugnis | ja — ein engerer Bereich besteht Prüfungen, die ein weiterer nicht besteht | nein — es entsteht kein Code, es entsteht eine Absage |

> **Eine falsche Vorbedingung an einer fremden Deklaration kann ein richtiges Programm
> abweisen; sie kann kein falsches durchlassen.** Deshalb ist sie Zeremonie und kein
> Vertrauensposten. Der Satz steht auch im Zeugnis, unter Abschnitt F — damit die
> Entscheidung dort nachlesbar ist, wo jemand nach ihr sucht.

Die *Menge* der offenen Vorbedingungen am Rufort wird schon gezählt, an der richtigen Stelle:
`gabbro pflichten` führt sie als `V` (`pflichten::Art::Vorbedingung`), mit ihren beiden
Schranken daneben.

## Warum es EIN Leser ist und nicht zwei

`crates/gabbro-check/src/fremdverengung.rs` beantwortet die Frage *„verengt diese
`ensures`-Klausel, und wie?"* genau einmal: `bereich_aus_ensures` liefert den verengten Typ
**und** die Schritte, die dahin geführt haben. M1 nimmt den Typ und rechnet damit weiter, das
Zeugnis nimmt die Schritte und druckt sie ab.

> Ein Zeugnis, das den Baum selbst noch einmal nach `ensures`-Klauseln absucht, wäre der
> zweite Leser gewesen — und **genau diese Bauart hat am 2026-08-20 eine Tatsache verloren,
> die zwei Leser hatte und von der nur einer las** (`verbundwert`, ein `let`-Typ, der zu
> `c->len` wurde). Deshalb bekommt `zeugnis::zeige` seit heute den Quelltext und die Liste
> des **Passes** statt einer zweiten eigenen Lesung.

## Die Sprechproben, die rot werden können

| Wo | Was fällt |
|---|---|
| `tests/beispiele.rs::eine_fremdverengung_steht_mit_namen_im_zeugnis` | die Stelle verschwindet aus dem Zeugnis |
| `tests/beispiele.rs::eine_klausel_ohne_wirkung_steht_nicht_unter_f` | eine Klausel ohne Wirkung wird mitgezählt |
| `tests/beispiele.rs::ein_eigener_rumpf_zaehlt_nicht_als_fremdverengung` | ein `impl fn` landet in der Vertrauensfläche |
| `tests/beispiele.rs::auch_die_relationale_nachbedingung_wird_gebucht` | die relationale Hälfte fällt aus der Buchung |
| `./instrumente/zaehle-fremdverengung.py --sprechprobe` | beide Richtungen an zwei Einheiten, die sich in **einem Zeichen** unterscheiden |

**Und der Zähler selbst kann rot werden — gemessen, nicht behauptet.** Mit der Mutation
`fremdverengung-zaehlt-jede-klausel` im Prüfer:

```
== Sprechprobe, in beide Richtungen ==
  verengende Klausel  (u32 in 0 .. 4096):  1  ok
  bindende Klausel ohne Wirkung (1 .. 4096): 1  GESCHEITERT -- erwartet 0
RC mit Mutation = 1        RC ohne Mutation = 0
```

Und vier Mutationen in `mutiere-pruefer.py`, alle vier **gefangen** (einzeln gefahren auf
`ki-pc-fisch-101`, 2026-08-21):

```
gefangen   fremdverengung-zaehlt-jede-klausel
gefangen   fremdverengung-ueberspringt-die-ruempfe-ohne-rumpf
gefangen   fremdverengung-vergisst-die-beziehung
gefangen   zeugnis-druckt-abschnitt-f-nicht
```

## Abweichungen von der Buchführung, nachgerechnet

Der TODO-Posten nennt **89 fremde Rümpfe, 10 mit `ensures`, „und aus jedem verengt M1"**.
Nachgemessen am 2026-08-21:

| gebucht | gemessen | Befehl |
|---|---|---|
| 89 fremde Rümpfe | **80** in `beispiele/`, **109** über den ganzen `.gab`-Korpus | `./instrumente/zaehle-fremdverengung.py` |
| 10 mit `ensures` | **10** — bestätigt | `./instrumente/zaehle-fremdverengung.py` |
| „aus jedem verengt M1" | **1 von 10** | `./instrumente/zaehle-fremdverengung.py --stellen` |

*Die dritte Abweichung ist die, auf die es ankommt.* Sie war nicht nachzählbar, solange keine
Zahl über die *Wirkung* geführt wurde — und genau das ist der Grund, dass der Posten einen
eigenen Zähler bekommen hat statt einer Zeile in der Annahmenfläche.
