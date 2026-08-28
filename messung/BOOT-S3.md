# S3 des Bootsatzes: ein Ereignis, keine Nachbarschaft

*Entschieden am 2026-08-28, abends. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **Der Auftrag stellte eine Entwurfsfrage, und sie ist die ganze Sache:** wie wird
> *„verbraucht die Marke UND blendet aus"* zu **einem** Ereignis, das ein Pass sieht — statt
> zu zwei Klauseln, die zufällig nebeneinander stehen? *Zwei Zusagen, die man einzeln
> erfüllen kann, sind keine eine.*

`SPRACHE.md` §12 führte S3 mit der Spalte **gebaut: NEIN** und nannte den Grund selbst:
`beispiele/07-eintritt-und-boot.gab` schrieb `boot_ende` als gewöhnliche `fn` mit
`effects { consumes t, writes code_abbildung }` — **ein Wirkungsname, kein Mechanismus.**

---

## 1. W24 zuerst — und die Messung hat die Frage umgedreht

**W24 sagt: schreib die naheliegende Form hin und lass sie durch den UNVERÄNDERTEN Prüfer
laufen.** Getan, gegen `master` (`100c34d`) ohne eine Zeile Änderung, `gabbro pruefe`, vier
Probedateien.

### (a) Der Wortlaut aus `SPRACHE.md` §12

```gabbro
fn boot_ende(t : BootPhase, kern_wurzel : Seitentabelle)
    ensures !exists m in mappings of kern_wurzel : m.abschnitt == boot
    effects { consumes t, writes code_abbildung };
```

```text
Fehler: [P012] a.gab:26:52: Praedikat erwartet, Bezeichner `m` gefunden
   26 |     ensures !exists m in mappings of kern_wurzel : m.abschnitt == boot
      |                                                    ^
```

**Sie fällt — an EINEM Wort.** Spalte 52 ist das `m` des Quantorenrumpfs; der Parser bricht
dort ab, weil `boot` hinter dem `==` ein **Wortschatzwort** ist (`space`, `Raum::Boot`) und
in keinem Ausdruck stehen kann. *Der Quantor selbst, `!exists m in mappings of X :`, ist
vorher durchgelaufen.*

### (b), (c) Dasselbe ohne das Wort `boot`

```gabbro
    ensures !exists m in mappings of kern_wurzel : m.abschnitt == 1     -- (b)
    ensures forall m in mappings of kern_wurzel : m.abschnitt != 1      -- (c)
```

```text
Fehler: [M111] `boot_ende` cannot establish this postcondition
      = it names neither `result` nor a place the function writes according to `effects`
```

**Beide parsen und typen.** Sie fallen an `M111` — und die Meldung sagt *wörtlich* das, was
die Tabellenzeile über den Bestand sagte: `writes code_abbildung` ist ein Name, der mit
`kern_wurzel` nichts zu tun hat.

### (d) Mit `writes kern_wurzel`

```text
d.gab: 6 Items, 0 Fehler, 0 Hinweise
```

### (e) Der Bestand von `beispiele/07`, unverändert

```text
e.gab: 4 Items, 0 Fehler, 0 Hinweise
```

### Was die vier Läufe zusammen sagen

| | |
|---|---|
| **Die Nachbedingung ist HEUTE schreibbar** | (d), 0 Fehler. `mappings of` in `ensures` ist gebaut, `!exists` auch |
| **Der Parser fehlte nicht** | nur `boot` als Wert, und das ist ein Wort und keine Form |
| **Gefehlt hat die BINDUNG** | (e), 0 Fehler: **nichts sagte, dass diese Funktion das Bootende IST** |

> **Dritte Instanz derselben Bauart nach `transition`, «B35» und der `ops`-Rufform** — und
> zum vierten Mal lautet die Antwort: *gefehlt hat nicht die Form.* Hier war es nicht der
> Gerufene, sondern der **Zusammenhalt**: zwei Klauseln, die beide schreibbar waren, und
> keine Regel, die sie aneinanderband.

**Und ein zweiter Befund fiel dabei ab, den kein Entwurf vorgesehen hatte:** `m.section ==
boot` ist **zweifach** unschreibbar. `boot` ist ein Wortschatzwort — und ein
Seitentabelleneintrag hat **gar kein Abschnittsfeld**. `.boot` ist eine Bindezeitstrecke,
kein Bit in der Tabelle. *Der Satz in `SPRACHE.md` war geschrieben worden, bevor er parsen
musste.* Die gebaute Form nennt deshalb **Rahmenschranken** statt eines erfundenen Feldes.

---

## 2. Die vier Formen, beide Seiten je Form

### (A) Eine Klausel an der `fn`: `retires <marke> from <raum> falsifier <sonde>` — **gewählt**

| | |
|---|---|
| **dafür** | **Drei Teile, eine Klausel, keiner allein schreibbar.** Die Grammatik verlangt Marke, Raum und Klasse in einem Zug; `O011` hält die Marke gegen `effects { consumes … }`. Damit ist „verbraucht" und „blendet aus" nicht mehr trennbar — genau die Forderung. **Ein einziges neues Wort** (`retires`); `from`, `space` und der Schwanz `falsifier`/`unfalsifiable` stehen schon. Der Schwanz ist **derselbe wie an `assume` und `axiom`**, und damit ist die Klausel von sich aus ein Eintrag der Axiomschicht — `P029` sagt ohne eine neue Zeile ab, wenn beides fehlt |
| **dagegen** | **Ein neues Wort ist ein neues Wort**, und der Wortschatz ist geschlossen. Und die Klausel steht an einer **Deklaration ohne Rumpf**: was sie zusagt, prüft niemand nach — sie verschiebt die Pflicht, sie erfüllt sie nicht. *Das ist der Preis, und er steht in `saetze.rs` als Vorbehalt, nicht in einer Fußnote* |

### (B) Eine sechste Funktionsklasse: `boot_end fn boot_ende(…)`

| | |
|---|---|
| **dafür** | `FnKlasse` gibt es, die Parsestelle gibt es, kein neues Wort in einer neuen Stellung. Und die Klasse liest sich wie `raw` — dieselbe Familie |
| **dagegen** | **Eine Klasse ist AUSSCHLIESSEND, und das Bootende ist es nicht.** In `beispiele/07` ruft der `boot`-Block `rust_eintritt`, eine `extern fn`; ein wirkliches `boot_ende` wird ebenso `extern` oder `impl` sein. Eine Funktion kann nicht `extern` **und** `boot_end` sein, und damit wäre die Form an der einzigen Stelle unschreibbar, für die sie gebaut wird. Dazu der Preis: **44 `FnKlasse`-Fundstellen** (`grep -rn FnKlasse crates/ --include=*.rs \| grep -v tests \| wc -l`), an denen jede Absenkungs- und Rumpffrage neu zu beantworten wäre — für eine Aussage, die mit dem Rumpf nichts zu tun hat |

### (C) Ein Wirkungswort: `effects { retires t from boot, … }`

| | |
|---|---|
| **dafür** | Es stünde **genau dort, wo `consumes t` steht** — dieselbe Liste, also ein Eintrag statt zweier, und die Unteilbarkeit käme aus der Stelle statt aus einer Regel. Das ist der eleganteste Zuschnitt der vier |
| **dagegen** | **96 `WirkungArt::`-Fundstellen in elf Dateien** (`grep -rn 'WirkungArt::' crates/ --include=*.rs \| wc -l`; `wirkungen.rs` 16, `geteilt.rs` 14, `emit.rs` 11, `alias.rs` 9, `bindung.rs` 8 …). Jede davon müsste die Frage „ist das ein Lesen, ein Schreiben, ein Verbrauch?" für eine Wirkung neu beantworten, die **keine** davon ist. Und die Sonde hat in einer Wirkungsliste keinen Platz: `falsifier` gehört zur Vertrauensklasse, nicht zum Effekt — sie müsste doch wieder daneben stehen, und dann sind es wieder zwei |

### (D) Gar kein neues Wort: das Bootende ist, **wer die Marke verbraucht**

| | |
|---|---|
| **dafür** | Null Grammatik. Die Daten liegen alle schon da: `O008` sammelt die linearen Geistmarken und die `raw fn`s, die sie verlangen. Man verlangte einfach von jedem Verbraucher die `mappings of`-Nachbedingung |
| **dagegen** | **Gemessen an der einzigen Korpusstelle, die es gibt, trifft die Regel ZWEI Funktionen.** `beispiele/07` verbraucht `BootPhase` an zwei Stellen (`grep -n 'consumes t' beispiele/07-eintritt-und-boot.gab`): `boot_ende` — und `extern fn rust_eintritt(t : BootPhase) -> never`, der Bootverteiler, der die Marke über die Sprachgrenze trägt und nie zurückkehrt. **Von diesen beiden ist genau eine das Bootende, und der Unterschied steht nirgends im Typ.** Eine Regel, die beide trifft, verlangt vom Verteiler eine Seitentabellen-Nachbedingung; eine, die beide durchlässt, misst nichts. *Und der Raum und die Sonde bleiben ohnehin unschreibbar — sie kommen aus keinem Verbrauch* |

### Die Wahl, mit Grund

**(A).** (D) fällt an einer Messung und nicht an einem Geschmack: zwei Verbraucher, einer
davon das Bootende. (B) fällt an der Ausschließlichkeit der Klasse — die Form wäre an ihrer
eigenen Zielstelle unschreibbar. (C) ist der schönere Zuschnitt und kostet **96 Fundstellen**
für eine Wirkung, die keine ist, und müsste die Sonde trotzdem danebenstellen.

*Von (A) aus bleibt (C) erreichbar:* wer den Wirkungszuschnitt später will, hat mit
`Stilllegung` einen Ort, an dem Marke und Raum schon zusammenstehen.

---

## 3. Was Beweispflicht wurde und was Annahme mit Falsifikator

**Die Linie läuft mitten durch die Klausel**, und das ist die eigentliche Auskunft dieses
Dokuments:

| Aussage | Klasse | wer trägt sie |
|---|---|---|
| Die Marke wird verbraucht, und zwar von genau dieser Funktion | **Prüferregel** | `O011` gegen `effects { consumes t }` |
| Nach dem Ereignis steht **keine Abbildung** des Raumes mehr in der Tabelle | **Beweispflicht** | `O012` verlangt sie als `walk`-Tatsache über `mappings of`; sie steht als `ensures` an einer Deklaration ohne Rumpf und ist damit eine **Zusage über fremden Code** (`F`) |
| Eine Adresse **ohne Abbildung** ist nicht mehr erreichbar | **Annahme mit Falsifikator** | `manifest.rs::stilllegungsannahmen` bucht sie aus der Klausel, `gabbro annahmen` führt sie, `sonden/sonde_boot_unerreichbar.c` fährt sie |
| Nach dem Ereignis typt kein `raw`-Ruf mehr | **schon gebaut** | S1, `O008` — steht seit heute früh |

> **Warum die Ausblendung selbst nicht in die Prüferregel gehört:** sie ist eine Aussage über
> die MMU und den TLB, und keine über ein Programm. *Kein Pass sieht sie, heute nicht und mit
> keinem Beweisprojekt.* Aber sie **einfach** in die Axiomschicht zu buchen wäre zu billig
> gewesen — dann verschluckt die Buchung die ganze Schicht. Deshalb die Zweiteilung: `O012`
> hält die formulierbare Hälfte fest, und nur der Rest geht in die Annahme.

### Die Sonde ist ein Programm, kein Name

`messung/AXIOMSCHICHT.md` §3 hat den Bestand gemessen: *„27 Annahmen nennen eine Sonde, 26
verschiedene Namen — und NULL davon existieren als Programm."* `sonden/` hatte **eine**.

`sonden/sonde_boot_unerreichbar.c` ist die **zweite**, und sie fährt genau die Zeile, die
`SPRACHE.md` §12 als Falsifikator nennt. Vier Arme, gemessen auf `ki-pc-fisch-101`:

```text
sonde boot_unerreichbar :: nach der Stilllegung ist keine Adresse des Raumes erreichbar
      Runden 2000 (gewuenscht 2000000, Deckel 2000)
      arm 1  abgebildet, muss GEHEN      -- durchgelassen 2000
      arm 2  ausgeblendet, eigener Kern  -- gefaultet     2000
      arm 3  ausgeblendet, FREMDER Kern  -- gefaultet     2000
      arm 4  SPRUNG in den Raum          -- gefaultet     2000  (vorher gelaufen 2000)
```

* **Arm 1 ist die Empfindlichkeitsprobe** und läuft zuerst: derselbe Zugriff, dieselbe
  Fehlerbehandlung, auf einer **abgebildeten** Seite. Fällt er, ist der Detektor blind, jede
  grüne Zeile darunter wertlos, und die Sonde endet mit `1` **über sich selbst**.
* **Arm 3 ist der Grund, warum das mehr als eine `munmap`-Vorführung ist:** ein zweiter Faden
  berührt die Seite **vor** der Ausblendung, hält sie also in seinem Übersetzungspuffer, und
  greift danach erneut zu. *Die gefährliche Form ist nicht die veraltete Tabelle, sondern der
  stehengebliebene TLB auf einem Kern, der nicht mehr gefragt hat.*
* **Arm 4 ist der Sprung** — der Fall, um den es im Bootsatz wirklich geht, und nicht bloß
  ein Datenzugriff. x86_64, mit einem W^X-Übergang, den ein gehärteter Kern verweigern darf;
  wo er nicht läuft, sagt die Sonde **NICHT GEFAHREN** und nie grün.
* **Was sie nicht sieht: Fehlspekulation.** Ein transienter Zugriff hinter einer falsch
  vorhergesagten Verzweigung hinterlässt nichts, was eine Fehlerbehandlung sähe.
  `SPRACHE.md` §12 nimmt genau diesen Fall an der Schicht selbst aus, und die Sonde schreibt
  es in die eigene Ausgabe, statt eine grüne Zeile für sich sprechen zu lassen.

```bash
ssh ki-pc-fisch-101 'cd gabbro-s && ./instrumente/pruefe-sonden.sh'
# == 2 von 2 Sonden gelaufen, 27 Sondennamen im Manifest benannt ==
```

*Die zweite Zahl ist die Anklage und bleibt es: 27 benannt, 2 gefahren.*

---

## 4. Die Regeln und ihre Giftproben

Jede Regel hat **nein sagen** gesehen, einzeln, mit einem Fehler je Datei:

| Kennung | Probe | gemessene Ausgabe |
|---|---|---|
| `O010` | `beispiele/gift/341-bootmarke-ohne-stilllegung.gab` | `` `raw fn phys_schreiben` demands `BootPhase`, and no function retires it `` |
| `O011` | `/342-stilllegung-andere-marke.gab` | `` `boot_ende` retires `t`, and its `effects` do not consume `t` `` |
| `O011` | `/344-stilllegung-ohne-marke.gab` | `` `retires n` names no parameter of a `linear ghost type` `` |
| `O012` | `/343-stilllegung-ohne-tatsache.gab` | `` `boot_ende` retires an address space and no postcondition says what is gone `` |

**`341` ist wörtlich der Bestand von `beispiele/07` bis heute** — dieselben zwei Zeilen, die
mit **0 Fehlern** durchgingen. *Eine Giftprobe, die den eigenen Korpus von gestern ist, ist
die schärfste Sorte.*

### Und die Regel fand sofort eine zweite Fundstelle

`dokumente/SYNTAX.md` §14 trug denselben Fehler in der **Grammatikdokumentation**:

```gabbro
fn boot_end(t: BootPhase) effects { consumes t, writes code_map };
```

und darunter, in Prosa: *„`boot_end` consumes the linear token **and** unmaps `code<boot>` —
an event."* **Der Satz behauptete das Ereignis, der Block schrieb es nicht**, und
`korpus.rs::die_beispiele_der_grammatik_gehen_selbst_durch` hat es in derselben Minute
gemeldet, in der `O010` gebaut war. *Ein Grammatikdokument, dessen Beispiele die eigene
Prosa nicht einlösen, ist die teuerste Sorte Prosa: es sieht aus wie ein Beleg.*

---

## 5. Was NICHT gebaut ist, und warum

**Das gehört hierher und nicht in eine Lücke.**

1. **„Genau EIN Verbraucher der Marke" ist keine Regel.** `O010` verlangt, dass *irgendjemand*
   die Marke stilllegt. `beispiele/07` verbraucht `BootPhase` weiterhin **zweimal** —
   `boot_ende` und `rust_eintritt`. Das ist eine Aussage über Kontrollflusspfade, und M2s
   Linearität ist eine Regel über **Rümpfe**; diese Datei hat keine. *Die Regel wäre baubar
   und ist es nicht: sie braucht eine eigene Messung darüber, was ein `extern fn … -> never`
   mit einer linearen Marke eigentlich tut, und die habe ich nicht gemacht.*
2. **`O012` liest die DOMÄNE und die Verneinung, nicht die Bedeutung.** Dass
   `m.rahmen >= BOOT_RAHMEN_UNTEN && m.rahmen < BOOT_RAHMEN_OBEN` wirklich die Bootrahmen
   meint, sieht der Pass nicht. Dieselbe Grobheit wie bei `maintains`. Die schärfere Fassung
   müsste den stillgelegten **Raum** mit dem Prädikat verbinden — und dafür fehlt der Sprache
   die Brücke zwischen `space` und einer Rahmenstrecke.
3. **`O010` ist programmweit über das, was der Prüfer SIEHT**, und `gabbro pruefe` prüft je
   Datei. Eine `raw fn` in einem Modul, dessen Bootende woanders steht, bekommt allein
   geprüft einen Fehlalarm — dieselbe Klasse wie `O009`, das auch nur Namen sieht, die es im
   selben Programm auflösen kann. *Messbar am eigenen Korpus:*
   `beispiele/gift/300-zeiger-auf-raw-fn.gab` fällt jetzt mit **zwei** Kennungen (`O009` und
   `O010`), weil es ein Fragment ist. `--with` deckt den Fall für Bibliotheken, für Fragmente
   nicht.
4. **Die `section ".boot"`-Platzierung wird weiterhin nicht erzwungen** (die offene Hälfte
   von S2, unverändert). `retires` sagt, dass ein Raum stillgelegt wird; dass der `raw`-Code
   überhaupt in ihm liegt, sagt nach wie vor niemand.
5. **Kein Isabelle-Satz.** S3 ist ausdrücklich *„Axiomschicht + Falsifikator"* und keine
   Beweispflicht; ein Satz über eine MMU wäre ein Satz über ein Modell, das dieser Ordner
   nicht hat.

---

## 6. Abnahme

Alles auf `ki-pc-fisch-101:gabbro-s` (Bau, Tests, Emission, Sonden), die Textwächter lokal.

| Werkzeug | Ergebnis |
|---|---|
| `cargo test` | grün, 0 Fehlschläge |
| `pruefe-emission.sh` | `ALL PASS — 24 durchgestochen, 51 von 51 uebersetzen` |
| `pruefe-englisch.py` | `ALL PASS`, Ratsche gehalten (neue Kommentare englisch) |
| `pruefe-syntax.sh` | `153 Regeln definiert, 0 offen`; Wortschatz `219 = 219` |
| `pruefe-kennungen.py` | `ALL PASS — 234 Kennungen`, `O:` von 8 auf 11 |
| `pruefe-saetze.py` | `234 Kennungen, 67 Saetze, **45 ohne Satz**` — Marke gehalten |
| `pruefe-gruende.py` | Sprechprobe in beide Richtungen ok |
| `pruefe-schablonen.py` | `6 Praemissen, 0 ohne Adresse` — Marke gehalten |
| `pruefe-sonden.sh` | `2 von 2 Sonden gelaufen, 27 Sondennamen benannt` |
| `mutiere-pruefer.py --anker` | **322 von 325** — unverändert; die drei fehlenden liegen alle in `emit.rs` und sind nicht von hier |

**Vorgefunden rot und nicht angefasst:** `pruefe-klauseln.py`, `pruefe-vergabe.py`,
`pruefe-todo.py`, `pruefe-zahlen.py`, `pruefe-zitate.py`.
