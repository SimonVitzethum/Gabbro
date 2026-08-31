# Neun Quantorendomänen, und welche ihrer Namen jemand prüft

*Gemessen am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 14 GB verfügbar, 20 Kerne).
Werkzeug: der **unveränderte** Prüfer `target/debug/gabbro`, gebaut aus `4673a07`. Träger der
Verfälschungen: `messung/proben/probe-neun-domaenen.gab` — alle neun Domänen in EINER
Einheit, damit je Messung genau eine Angabe wechselt und die Kontrolle dieselbe Datei ist.*

`messung/QUANTORENDOMAENEN.md` hat an `chain(a, b) in <ort>` gefunden, dass **die beiden
Feldnamen kein Pass liest**. Dieses Dokument fragt dieselbe Frage an allen neun Domänen:
*welche Namen nennt eine Domäne, und welchen davon prüft jemand?*

> **`chain` war der Anlass und ist nicht der Gegenstand.** Der Befund unten ist größer als
> die eine Domäne — und er ist nicht der Befund, mit dem gerechnet wurde.

---

## 0. Die Apparatur, und sie steht vor der Messung

`gabbro pruefe` schreibt auf **STDOUT**, `gabbro emit` auf **STDERR**. Die Vorgängerbahn hat
für beide `stderr` gelesen und **acht Verfälschungen als „0 Fehler" gebucht**. Das Skript
dieser Bahn liest **beide Leitungen** und zählt die Kennungen aus der Vereinigung.

Und die Gegenproben stehen **vor** der ersten Messzeile, nicht daneben:

| Gegenprobe an `beispiele/55-kindkette.gab` | erwartet | gemessen |
|---|---|---|
| `tree { parent gibtsnichtxyz, … }` | `D006` | **`D006`** |
| `ensures … chain(…) in c.slots[zzz]` | `M109` | **`M109`** |

*Ohne die erste hätte diese Bahn dieselbe Nullmessung bekommen wie die vorige und sie für
einen Befund gehalten.*

Die Nullmessung: `messung/proben/probe-neun-domaenen.gab` unverändert — **18 Items,
0 Fehler, 0 Hinweise, 0 `C001`.**

---

## 1. Die Tafel — was eine Domäne nennt, und wer es liest

Jede Domäne nennt einen **Ort** (Grundname plus Feldsuffixe), zwei nennen mehr, eine nennt
nichts. Gemessen wird je Zelle die kleinste Verfälschung durch den unveränderten Prüfer.

| # | Domäne | die Namen, die sie nennt | Grundname des Orts | **Typ** des Orts | die zusätzliche Angabe |
|---|---|---|---|---|---|
| 1 | `slots of <ort>` | Ort | `M109` **nur in `ensures`** | **niemand** | — |
| 2 | `chain(a, b) in <ort>` | Ort **+ zwei Feldnamen** | `M109` nur in `ensures` | **niemand** | **niemand** — der Fund, und §6 baut ihn: seit `D014`–`D016` in ALLEN Stellungen |
| 3 | `descendants of <ort>` | Ort (+ die `tree`-Kante an der Tabelle) | `M109` nur in `ensures` | **niemand** | `D006`–`D008` an der `table`; *ob die Tabelle überhaupt eine hat*: niemand |
| 4 | `ancestors of <ort>` | Ort (+ `tree { parent }`) | `M109` nur in `ensures` | **niemand** | wie 3 |
| 5 | `queue <ort>` | Ort (+ das einzige Feldarray) | `M109` nur in `ensures` | **niemand** | nur der KOSTENPASS, und nur an einem `traverse` |
| 6 | `fields of <pfad>` | ein **Pfad** | **niemand** | **niemand** | — |
| 7 | `elems of <ort>` | Ort **einschließlich Feldname** | `M109` nur in `ensures`, **und nur der Grundname** | **niemand** | **niemand** — Fund |
| 8 | `threads` | **nichts** | — | — | — |
| 9 | `mappings of <ort>` | Ort (+ die `walk`-Deklaration) | `M109` nur in `ensures` | **niemand** | nur der Kostenpass (`walkschranken`), am `traverse` |

**Drei Spalten, drei Antworten:** der Grundname ist geprüft, aber nur in einer von fünf
Stellungen; der Typ ist nirgends geprüft; die zusätzliche Angabe ist bei zweien von neun
nirgends geprüft.

*Die Tafel steht im Zustand VOR dem Bau — sie ist die Nullmessung. Was §6 daran ändert,
ändert genau eine Zelle, und sie ist dort einzeln nachgemessen.*

---

## 2. Die Messreihe — zweiunddreißig Verfälschungen, eine Zeile je Zelle

Alle an `messung/proben/probe-neun-domaenen.gab`, alle gegen den unveränderten Prüfer, alle
mit `C001 = 0`.

### 2a Der Grundname des Orts — der einzige geprüfte Name

| Verfälschung | Befund |
|---|---|
| `slots of gibtsnichtxyz` (in `ensures`) | **`M109`** |
| `chain(…) in k.slots[zzz]` | **`M109`** |
| `descendants of k.slots[zzz]` | **`M109`** |
| `ancestors of k.slots[zzz]` | **`M109`** |
| `queue zzznix` | **`M109`** |
| `elems of zzznix.plaetze` | **`M109`** |
| `mappings of zzznix` | **`M109`**, `M111` |
| `fields of Gibtsnichtxyz` | **nichts fällt** |
| `fields of NKNOTEN` (eine Konstante) | **nichts fällt** |

> **`fields of` ist die einzige Domäne, deren Grundname überhaupt nicht geprüft wird** — sie
> trägt einen `Pfad` und keinen `Ort`, und der Namenssammler von `M109`
> (`m1.rs::sammle_namen_pred_geb`) hat für `FelderVon` denselben leeren Zweig wie für
> `Threads`. *Sie hat im ganzen Korpus null Stellen; die Zelle stand als `ungemessen` in
> `ABSAGEFORMEN.md`:403 und ist es jetzt nicht mehr.*

### 2b Der TYP des Orts — und hier fällt nirgends etwas

Nicht der Name wurde getauscht, sondern **der Parameter**: derselbe Name, ein Typ, über dem
die Domäne nichts bedeutet.

| Verfälschung | was das heißen sollte | Befund |
|---|---|---|
| `slots of k`, `k : ptr<…> Ring` | ein Verbund hat keine Slots | **nichts fällt** |
| `chain(…) in k.plaetze[p]`, `k : ptr<…> Ring` | ein Zahlenarray hat keine Kette | **nichts fällt** |
| `descendants of k.slots[s]`, `table` **ohne `tree`** | die Kante ist nicht erklärt | **nichts fällt** |
| dieselbe Tabelle mit `tree { parent elter }` | `descendants of` braucht alle drei Kanten | **nichts fällt** |
| `queue r`, `r : ptr<…> Knoten` | eine Tabelle ist keine Warteschlange | **nichts fällt** |
| `queue s`, `s : RingNr` | ein Skalar ist keine Warteschlange | **nichts fällt** |
| `elems of k`, `k : ptr<…> Knoten` | ein Tabellenzeiger ist kein Feldarray | **nichts fällt** |
| `mappings of w`, `w : ptr<…> Knoten` | die Tabelle hat keinen `walk` | **nichts fällt** |
| `fields of Knoten` (eine `table`) | eine Tabelle ist keine Feldliste | **nichts fällt** |
| ein **zweites** Feldarray im `Ring` | `arraylaenge_im_verbund` gäbe `None` | **nichts fällt** |

**Neun Domänen, zehn Typverfälschungen, null Absagen.** Die Kontrolle daneben: benennt man
den `walk` um, sodass der Parametertyp `Baum` verschwindet, fällt **`N040`** — *der Typname
wird also sehr wohl aufgelöst, nur fragt niemand, ob die Domäne zu ihm passt.*

> Das ist keine Nachlässigkeit eines Passes, sondern eine Adresse, die es nicht gibt.
> `domaene.rs::domaenenschranke` **rechnet** genau diese Zuordnung aus — Tabelle, Verbund,
> Feldlänge, `walk`-Ebenen — und liefert `None`, wenn sie nicht aufgeht. **Gerufen wird sie
> nur vom Kostenpass und vom Traversierungszähler**, also nur an einem `traverse`. In einer
> Annotation läuft kein Kostenpass. *Die Rechnung steht da und wird an der Stelle, an der
> die Sprache sie bräuchte, nicht angestellt.*

### 2c Die zusätzliche Angabe — `chain` und `elems of`

`chain(a, b)` nennt seine Kante **am Durchlauf** und ist damit die einzige Domäne, die eine
Kante an der Fundstelle trägt statt an der Deklaration. Alle Verfälschungen im `ensures`
von `d2_chain`:

| statt `chain(erstes_kind, naechstes_geschwister)` | was es bedeutet | Befund |
|---|---|---|
| `chain(gibtsnicht, auchnicht)` | Felder, die es nicht gibt | **nichts fällt** |
| `chain(belegt, belegt)` | ein `bool` — gar keine Kante | **nichts fällt** |
| `chain(marke, marke)` | ein `u32` — keine Kante, nicht einmal ein Ende | **nichts fällt** |
| `chain(naechstes_geschwister, erstes_kind)` | die Kante verkehrt herum | **nichts fällt** |
| `chain(elter, elter)` | die Kante des BAUMS statt der Kette | **nichts fällt** |
| `chain(zzza, zzzb)` in einer `invariant` | dasselbe, andere Stellung | **nichts fällt** |
| `chain(zzza, zzzb)` im Rumpf einer `spec fn` | dasselbe, dritte Stellung | **nichts fällt** |

Und `elems of <ort>` ist derselbe Fall mit einem anderen Gesicht: der Ort trägt **den
Feldnamen im Suffix**, und `M109` steigt in Suffixe nur ab, wenn sie ein `[index]` sind
(`m1.rs`:3966 — *„`.feld` und `->feld` sind Namen im TYP, nicht in der Umgebung"*).

| Verfälschung | Befund |
|---|---|
| `elems of r.gibtsnichtfeld` | **nichts fällt** |
| `elems of r.kopf` (ein Skalarfeld, kein Array) | **nichts fällt** |

Dasselbe an der gebundenen Variablen: `mappings of w` bindet `m` an einen `Pte`, und
`m.gibtsnichtfeld` im Rumpf **fällt nicht**.

### 2d `threads` — nichts zu nennen, also nichts zu prüfen

`threads` nennt keinen Namen. Nachgemessen und mit `QUANTORENDOMAENEN.md` §4 gleichlautend:
`t` gebunden und unbenutzt fällt nicht, und `forall t in threads` gegen
`forall t in slots of k` getauscht ändert nichts. **Hier ist die Lücke keine Lücke der
Prüfung, sondern eine der Deklaration** — und das ist die Sprachentscheidung `Q3`, die
gebucht steht und die diese Bahn nicht anrührt.

---

## 3. Der zweite Befund, und er ist der größere: die STELLUNG

`M109` läuft über `f.ensures` und über sonst nichts (`m1.rs`:3100, `for p in &f.ensures`).
Derselbe unbekannte Grundname, an fünf Stellungen gemessen:

| Stellung | `slots of gibtsnichtxyz` | `chain(zzza, zzzb)` |
|---|---|---|
| `ensures` | **`M109`** | nichts |
| `requires` | **nichts** | nichts |
| `invariant` an der `table` | **nichts** | nichts |
| Rumpf einer `spec fn` (`= forall …`) | **nichts** | nichts |
| `maintains` | nennt nur eine Marke, keinen Quantor | — |

Und so verteilen sich die Quantorenstellen des Korpus (`beispiele/` + `messung/`,
Kommentarzeilen abgezogen, gezählt von `zaehle.py` dieser Messung):

| Domäne | `ensures` | `requires` | `invariant` | `spec fn =` | Summe |
|---|---|---|---|---|---|
| `slots of` | 1 | 3 | 34 | 4 | 42 |
| `mappings of` | 2 | 0 | 6 | 0 | 8 |
| `queue` | 2 | 2 | 0 | 0 | 4 |
| `chain(…) in` | 1 | 1 | 1 | 0 | 3 |
| `ancestors of` | 0 | 1 | 0 | 0 | 1 |
| `elems of` | 0 | 0 | 0 | 1 | 1 |
| `threads` | 1 | 0 | 0 | 0 | 1 |
| `descendants of` | 0 | 0 | 0 | 0 | **0** |
| `fields of` | 0 | 0 | 0 | 0 | **0** |
| **Summe** | **7** | **7** | **41** | **5** | **60** |

> **Sieben von sechzig.** Die eine Stellung, die `M109` liest, trägt 7 der 60
> Quantorenstellen des Korpus; die `invariant` trägt 41 und ist ungelesen. *Die Regel greift
> dort, wo der Korpus sie am wenigsten braucht* — und das ist wortgleich der Befund, mit dem
> `M109` selbst am 2026-08-19 gebaut wurde (`m1.rs`:3953: *„`M109` prüft damit genau die
> Namen, die niemand falsch schreibt"*), einen Ring weiter außen.

**Und das ist keine Aussage über Quantoren.** Gemessen an derselben Datei, ohne jeden
Quantor: `requires c.slots[zzz].belegt`, `requires zzznix.slots[p].belegt`,
`requires c.slots[k].gibtsnichtfeld` — **alle drei fallen nicht.** Die Namensauflösung fehlt
der ganzen `requires`-Klausel und der ganzen `invariant`, nicht ihrer Quantorenhälfte.

---

## 4. Welcher Pass müsste es sagen — je Zelle, und warum er es nicht tut

| Lücke | der Pass, der es sagen müsste | warum er schweigt |
|---|---|---|
| Grundname in `requires`/`invariant`/`spec fn` | `M109` (`m1.rs`) | seine Schleife läuft über `f.ensures`; die anderen Klauseln stehen nicht darin |
| Grundname von `fields of` | `M109` | `sammle_namen_pred_geb` hat für `FelderVon` einen leeren Zweig — ein `Pfad` ist kein `Ort` |
| Typ des Orts, alle neun | ein Domänenpass, den es nicht gibt | `domaene.rs::domaenenschranke` rechnet die Zuordnung, wird aber nur vom Kostenpass und vom Zähler gerufen — beide nur am `traverse` |
| `tree`-Kante fehlt ganz | `D006`–`D008` (`kbedingung.rs`) prüfen die DEKLARIERTE Kante | dass eine Tabelle eine braucht, weil eine Domäne an ihr läuft, sagt heute nur der Erzeuger mit `C001`, und der läuft an einer Annotation nicht |
| Feldnamen von `chain(a, b)` | **niemand, an keiner Stelle** — bis §6 | die drei Leser (`wirkungen.rs`:1164, `m1.rs`:4048, `gruppe.rs`:527) mustern `KetteIn { ort: o, .. }` und werfen `a` und `b` weg. *Ein vierter Leser war die Antwort, kein vierter Blick derselben drei* |
| Feldname im Suffix von `elems of` | `M109` | er steigt nur in `[index]`-Suffixe ab, nicht in `.feld` |
| `threads` | keiner | die Domäne nennt nichts (Sprachentscheidung `Q3`) |

---

## 5. Was daraus gebaut wird — und was ausdrücklich nicht

**Gebaut wird die Zelle mit dem gemessenen Mangel und dem vorhandenen Vorbild:** die beiden
Feldnamen von `chain(a, b)`. `D006`–`D008` sagen an der `table` genau denselben Satz über
dieselbe Sorte Name (*das Feld steht im Slot · es ist `option index into Self` · es zeigt in
die eigene Tabelle*), und `SYNTAX.md`:1060 nennt `chain(a, b) in` beim Umzug der Baumkante
als das Vorbild, das es längst konnte. **Auf `chain` selbst ist das Argument nie
zurückgefallen** — und die Messung oben sagt, dass sieben Verfälschungen der Kante durch
alle drei Stellungen laufen.

**Nicht gebaut wird hier:**

| | Posten | Grund |
|---|---|---|
| **S1** | `M109` auf `requires`, `invariant` und `spec fn`-Rümpfe ausdehnen | **Der größte gemessene Mangel dieser Tafel** (53 von 60 Stellen), und deshalb gehört er nicht als Beifang in einen Bau über `chain`. Er berührt jede Klausel des Korpus, nicht eine Domäne; die Gegenprobe dafür ist ein voller Korpuslauf und kein Giftbeispiel |
| **S2** | ein Typpass über allen neun Domänen (`slots of` auf einer Tabelle, `queue` auf einem Verbund, …) | benannt und gemessen, aber `domaene.rs` liefert für neun Varianten fünf Schrankenquellen (`K001-DOMAENENSCHRANKE.md`:233) — eine Absage aus `None` wäre bei `KetteIn`, `FelderVon` und `Threads` ein Fehlalarm. *Der Pass braucht eine eigene Zuordnungstabelle, und die ist eine Entscheidung über neun Wörter* |
| **S3** | `fields of` überhaupt: Pfad prüfen, Bindung erklären | null Korpusstellen, null Absagen, und der Erzeuger sagt sie namentlich ab. **Regel A** — es gibt keinen Gegenstand, der den Bedarf misst |
| **S4** | `queue` mit sichtbarem Kopf, `threads over <tabelle>` | Sprachentscheidungen des Ordners, gebucht als `Q2`/`Q3` |

*Diese Tafel stand, bevor eine Zeile Prüfercode fiel* (Commit `25db09e`). Sie ist die
Nullmessung, gegen die §6 sich messen lässt.

---

## 6. Was gebaut wurde — `D014`/`D015`/`D016`, und was sie NICHT fangen

**Eigene Kennungen, nicht eine erweiterte.** Die Entscheidung ist gemessen und nicht
gewählt: `D006`–`D008` sitzen an der **Deklaration** (`kbedingung.rs::baumkanten`, ein
Durchlauf über `t.baum`), `chain(a, b)` sitzt an der **Fundstelle** und kommt je Tabelle
beliebig oft mit verschiedenen Feldern vor. Ein gemeinsamer Code müsste die Spanne einer
`table` tragen, an der die Kette gar nicht steht — *und die Meldung „`tree parent X`
names no field“ schickt den Leser dann an eine Zeile, in der nichts steht.*

Die drei Regeln sind `D006`–`D008` Wort für Wort, und der Pass steht in `domaene.rs`,
gerufen aus `m1::lauf` — dort, wo die `Umgebung` schon steht:

| Kennung | die Frage | das Vorbild |
|---|---|---|
| **`D014`** | das Feld steht im Slot der Tabelle, in der die Kette läuft | `D006` |
| **`D015`** | es ist `option index into <Tabelle>` — eine Kette muss ENDEN können | `D007` |
| **`D016`** | es zeigt in dieselbe Tabelle, nicht in eine fremde | `D008` |

### 6a Die Giftproben — je Klasse eine, je genau eine Kennung

| Datei | gemessen |
|---|---|
| `beispiele/gift/422-kettenkante-gibt-es-nicht.gab` | `D014`, sonst nichts, 0 `C001` |
| `beispiele/gift/423-kettenkante-ohne-ende.gab` | `D015`, sonst nichts, 0 `C001` |
| `beispiele/gift/424-kettenkante-in-fremde-tabelle.gab` | `D016`, sonst nichts, 0 `C001` |

Und ein voller Korpuslauf über **434 Dateien**: `D014`/`D015`/`D016` fallen in **null**
sauberen Dateien. *Eine neue Regel, die den eigenen Korpus zerlegt, ist keine Regel.*

### 6b Die Gegenrichtung — und sie ist der Grund, dass zwei Verfälschungen stehen bleiben

| bleibt grün | warum |
|---|---|
| `chain(erstes_kind, naechstes_geschwister)` | die erklärte Kette |
| `chain(naechstes_geschwister, erstes_kind)` | **vertauscht — und strukturell trotzdem eine Kette** |
| `chain(elter, elter)` | die Vorfahrenkette |
| `chain(erstes_kind, erstes_kind)` | die linke Kante des Baums |

> **Drei der fünf gemessenen Verfälschungen fallen jetzt, zwei nicht — und das ist Regel
> A und keine Bequemlichkeit.** `chain(a, b)` heißt: *nimm `<ort>.a`, dann folge `.b`*.
> Beide Namen sind wohlgeformte Kanten, in jeder Reihenfolge und auch zweimal derselbe;
> `chain(x, x)` läuft eine Spindel und **steht so im Korpus**
> (`messung/proben/probe-vier-zellen.gab`:59, `chain(naechst, naechst)`).
> *Sie abzuweisen bräuchte eine Aussage darüber, was der Schreiber MEINTE — und keine
> Messung dieser Bahn trägt eine.* Die naheliegende Regel („die beiden sind die
> `tree`-Kanten in vertauschten Rollen“) hätte `chain(kind, kind)` mitgerissen, und das
> ist die Spindel.

### 6c Alle vier Stellungen, nicht die eine, die `M109` liest

`chain(zzza, zzzb)` an vier Stellen, je **`D014`**: `ensures` · `requires` · `invariant`
an der `table` (über `Self`) · `traverse`. Der Pass bindet `Self` selbst, weil die
Umgebung den Namen nicht kennt (`m1.rs` sagt das an `M120`).

### 6d Die Mutationsprobe — gebaut, nicht nur verankert

Drei Mutationen von Hand gesetzt, **gebaut** und mit `cargo test --no-fail-fast`
gemessen; die Quelle danach byteweise zurückgestellt und gegen `sha256` geprüft:

| Mutation | Schaden | gefallene Proben |
|---|---|---|
| `kettenkante-nimmt-irgendein-feld` | ein Name, den es nicht gibt, nimmt das erste Slotfeld | **2** |
| `kettenkante-braucht-kein-ende` | die Kante muss kein `option index into` mehr sein | **2** |
| `kettenkante-darf-hinaus` | die Kante darf in eine fremde Tabelle zeigen | **2** |

Es sind je dieselben zwei — die Giftprobe (`jedes_gift_faellt_mit_seinem_code`) und der
Einzeltest (`die_kettenkante_wird_gegen_ihre_tabelle_gehalten`) —, und **keine dritte**:
der Schaden bleibt bei der einen Regel.

> **Und die erste Messung sagte „1 Probe“, dreimal.** `cargo test` ohne
> `--no-fail-fast` hält beim ersten roten Ziel an, also war die zweite Probe nie
> gelaufen. *Ein Messgerät, das nach dem ersten Treffer aufhört, meldet immer genau
> einen* — dieselbe Klasse wie die stderr-Leitung in §0, und beide Male hat erst die
> Gegenprobe es gezeigt.

### 6e Was weiter ungeprüft bleibt, und mit welchem Grund

| Stelle | Zustand | Grund |
|---|---|---|
| der **Typ** des Orts, bei allen neun Domänen | **weiter ungeprüft** | S2. Löst der Ort sich nicht zu einer Tabelle auf, **schweigt** der neue Pass — er rät den Träger nicht. `domaenenschranke` fällt für ihre Zwecke von der ganzen Kette auf die Basis zurück; für eine SCHRANKE ist eine zu große Zahl ein zu schwaches Urteil, für eine ABSAGE wäre ein falsch geratener Träger ein Fehlalarm über einen fremden Feldnamen |
| die Rolle der beiden `chain`-Kanten | **weiter ungeprüft** | §6b — es gibt keine Messung, die eine Reihenfolge falsch nennt |
| Grundnamen in `requires`/`invariant`/`spec fn` | **weiter ungeprüft** | S1, 53 von 60 Stellen. Der neue Pass liest zwar alle Stellungen, aber nur die `chain`-Kante; die Namensauflösung selbst bleibt bei `M109` und damit bei `ensures` |
| der Pfad von `fields of` | **weiter ungeprüft** | S3, Regel A: null Korpusstellen |
| der Feldname im Suffix von `elems of` | **weiter ungeprüft** | derselbe Bau wie S1: `M109` steigt nicht in `.feld` ab |
| `threads` | **nichts zu prüfen** | die Domäne nennt keinen Namen — `Q3`, Sprachentscheidung |
| eine Tabelle, an der `descendants of` läuft und die keine `tree` hat | **im Prüfer weiter ungeprüft** | der Erzeuger sagt `C001`, und an einer Annotation läuft er nicht |

---

## 7. Was dieses Dokument NICHT sagt

1. **Nichts darüber, ob die geprüften Namen die richtigen Dinge benennen.** Eine Kante, die
   existiert und `option index into Self` ist, ist deshalb nicht die Kette, die das Programm
   meint. Gabbro hat keinen Beweiser; `gabbro pflichten` zählt, es löst nicht ein.
2. **Nichts über die Traversierungsstellung.** Alle Messungen oben stehen in Annotationen.
   Am `traverse` sagt der Erzeuger fünf der neun Domänen namentlich ab (`ABSAGEFORMEN.md`),
   und `descendants of` über einer Tabelle ohne `tree` fällt dort an `C001` — gemessen an
   `beispiele/gift/195-descendants-ohne-tree.gab` (`pruefe`: nichts, `emit`: 1 × `C001`).
   *Der Prüfer schweigt auch dort.*
3. **Nichts über `state`.** Das ist die eine `UNGEDECKT`-Zelle der Grammatiktafel, ihre
   Absage ist als richtig nachgemessen, und sie ist nicht der Gegenstand dieser Bahn.
