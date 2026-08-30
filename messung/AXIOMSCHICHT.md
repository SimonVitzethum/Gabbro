# Die Axiomschicht, gemessen — und was die Zahl **nicht** sagt

*Stand 2026-08-21. Jede Zahl unten nennt den Befehl, der sie nachrechnet (Hausordnung 6).
Gebaut und gemessen auf `ki-pc-fisch-101:gabbro-d`; lokal reicht der Speicher nicht.*

```bash
rsync -rlpgoD --delete --exclude 'target/' --exclude '__pycache__/' --exclude '.claude/' \
      ./ ki-pc-fisch-101:gabbro-d/
ssh ki-pc-fisch-101 'cd gabbro-d && export PATH=$HOME/.cargo/bin:$PATH && cargo build --release'
```

---

## 1. Der Bestand: 33 Annahmen, jede mit Sonde **oder** Grund

```bash
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro annahmen beispiele/*.gab' | tail -1
# -- 33 Annahmen
```

Der Posten im Ordner sagt **32**, und das war bis heute richtig. Die 33. ist neu und in
diesem Lauf entstanden — `sperrabdruck_haelt_fremde_kerne_fern`, siehe Abschnitt 4.

**Dass jede eine Sonde oder einen Grund trägt, ist keine Leistung des Korpus, sondern der
Grammatik**: `SYNTAX.md`:1190 lässt zu `assume`/`axiom` nur `falsifier ident` **oder**
`unfalsifiable string` zu, und das Fehlen von beidem ist ein Übersetzungsfehler. *Die Zahl
misst hier die Grammatik, nicht die Sorgfalt.*

---

## 2. Erste Frage: wie viele sind **nicht** falsifizierbar?

**6 von 33.** Eine nicht falsifizierbare Annahme ist eine andere Währung als eine mit
lauffähiger Sonde — gegen sie kann keine Probe je etwas ausrichten.

```bash
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro annahmen beispiele/*.gab' \
  | grep -c "nicht-falsifizierbar"
# 6
```

| Annahme | Grund | Klasse des Grundes |
|---|---|---|
| `release_stellt_sichtbarkeit_her` | *„das Speichermodell ist nicht durch Ausführung widerlegbar — eine erfolgreiche Probe zeigt nur, dass die Umordnung diesmal ausblieb"* | **Speichermodell** |
| `sperrabdruck_haelt_fremde_kerne_fern` | *„… eine Sonde, die den Abdruck hält und nachsieht, zeigt nur, dass diesmal niemand hingesehen hat"* | **Speichermodell** |
| `mmu_schreibt_nur_a_und_d` | *„eine Sonde müsste die MMU anhalten und dabei genau das Fenster öffnen, in dem sie schreibt"* | **Beobachtung stört den Gegenstand** |
| `wbinvd` | *„die Wirkung ist auf dieser Maschine nicht beobachtbar"* | **kein Messpunkt** |
| `x2apic_zweischritt` | *„qemu64 hat kein x2APIC — die Sonde hat hier kein Gerät"* | **kein Gerät auf DIESER Maschine** |
| `ipi_kommt_an` | *„Lebendigkeit fällt unter keinen Mechanismus dieser Sprache"* | **Lebendigkeit** |

**Die Verteilung ist die eigentliche Aussage, und sie zerfällt in drei sehr ungleiche
Lager:**

* **Zwei sind prinzipiell unwiderlegbar** (Speichermodell). Keine Maschine und keine
  Laufzeit ändert daran etwas — eine grüne Probe ist hier ein Nicht-Ereignis.
* **Zwei sind es aus einem Grund, der am Messapparat hängt** (`mmu_schreibt_nur_a_und_d`,
  `wbinvd`). *Ein anderer Apparat könnte sie widerlegbar machen*, und dann wäre die Zeile
  zu ändern.
* **Eine ist es nur HIER** (`x2apic_zweischritt`: „qemu64 hat kein x2APIC"). Auf echter
  Hardware mit x2APIC wäre sie falsifizierbar. **Das ist die schwächste der sechs**, weil
  ihr Grund kein Grund über die Sache ist, sondern über die Testmaschine.
* **Eine ist es aus einem Grund über die SPRACHE** (`ipi_kommt_an`), und der deckt sich mit
  D8: *„`progress` nennt Annahmen, beweist keine Lebendigkeit."*

> **Was diese Tabelle nicht sagt:** dass die sechs Gründe stimmen. Sie sind Prosa, und
> `gabbro` liest sie nicht. Geprüft ist, **dass** einer dasteht, nicht **was** er sagt.

---

## 3. Zweite Frage, und sie ist die unangenehme: **gibt es die Sonden?**

**27 Annahmen nennen eine Sonde, 26 verschiedene Namen — und NULL davon existieren als
Programm.**

> **Nachgemessen 2026-08-30: es sind 29, und EINE existiert.** Der Befund unten stimmt in
> seiner Klasse und war in seiner Zahl zu klein. **Und er ist jetzt eingelöst, nicht nur
> gebucht:** ein Name ohne Programm steht nicht mehr im Manifest — siehe die Tabelle in
> Abschnitt 4 und die Zeile, die sagt, wie viele gestrichen wurden.

```bash
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro annahmen beispiele/*.gab' \
  > /tmp/annahmen.tsv
# je Sonde: kommt der Name IRGENDWO ausserhalb seiner eigenen `falsifier`-Zeile vor?
grep -rIn "sonde_" . --exclude-dir=.git --exclude-dir=target | grep -v "falsifier sonde_"
```

Der Lauf über den ganzen Baum findet **vier** Sondennamen ausserhalb ihrer
`falsifier`-Zeile. Von Hand nachgesehen ist keiner davon eine Sonde:

| Sonde | Fundort | Was es wirklich ist |
|---|---|---|
| `sonde_mxcsr_rne` | `TODO.md`, `crates/gabbro-check/src/manifest.rs` | der **Erzeuger** der Zeile und ein Posten, der genau das schon buchte |
| `sonde_keine_ueberbreite` | dieselben zwei | dito |
| `sonde_invlpg` | `crates/gabbro-check/tests/manifest.rs` | eine **Zeichenkette in einem Testprogramm** |
| `sonde_cr3` | `crates/gabbro-check/tests/manifest.rs` | dito |

**Damit ist der Befund: 0 von 27.** Die Sonde ist in jedem einzelnen Fall ein Name, dem
kein Programm entspricht.

**Das ist kein Vorwurf an den Korpus, sondern eine Entscheidung, die dasteht:** `namen.rs`
:1548 hält seit dem 2026-08-19 fest, *„`expects` names an EXTERNAL probe, like
`assume … falsifier`: it does not stand in Gabbro because it RUNS"*. Eine Sonde **gehört**
nicht in den Baum. Die Frage ist damit nicht, ob sie hier fehlt, sondern ob sie
**irgendwo** ist — und die Antwort ist: es gibt im ganzen Ordner keinen Ort, an dem eine
Sonde stünde, kein Verzeichnis, kein Läufer, keine Buchung über ihren Lauf.

> **Und genau das ist die Gestalt, gegen die dieser Ordner steht.** Ein
> `falsifier sonde_xyz`, dessen Sonde nirgends existiert, ist eine Zusicherung über das
> **Ausbleiben einer Widerlegung** — dieselbe Klasse wie **R15** („erfüllt, sobald der
> Prüfer schweigt") und **W10** („nicht abgewiesen ist nicht bestätigt").
>
> *Der Ordner buchte das bisher für **zwei** Sonden* (TODO.md: *„Die zwei Gleitkommasonden
> gibt es als NAMEN, nicht als Programm"*). **Gemessen gilt es für alle 27.** Die Buchung
> war nicht falsch, sie war zu klein — und zwar in der schmeichelhaften Richtung.

### Was „falsifizierbar" damit heute wirklich heisst

Drei Stufen, und die Sprache unterscheidet nur die ersten beiden:

| | Bedeutung | Zahl am 2026-08-21 | **Zahl heute** |
|---|---|---|---|
| **unfalsifizierbar** | mit ausgeschriebenem Grund | **6** | 6 |
| ~~falsifizierbar, Sonde benannt~~ **ungedeckt** | ~~ein Name, der eine Sonde bezeichnen würde~~ — der Name ist **gestrichen** | **27** | **29** |
| **falsifizierbar, Sonde LÄUFT** | ein Programm, das fallen kann | **0** | **1** |

**Die dritte Zeile existiert grammatisch nicht** — und `SYNTAX.md`:1211 nennt genau diese
Unterscheidung: *„Three classes, and the third does not exist syntactically: falsified
(probe ran and held), not falsifiable (with a reason), not run."* Die Sprache verbietet,
dass „nicht gelaufen" wie „falsifiziert" **aussieht**; sie hat aber keine Form, in der
„gelaufen" sich von „benannt" unterscheidet. ~~*Heute sind alle 27 im Zustand „nicht
gelaufen", und nichts im Erzeugnis sagt es.*~~

> **GEHEILT am 2026-08-30, im ERZEUGNIS statt in der Grammatik.** Der Satz *„nichts im
> Erzeugnis sagt es"* stimmt nicht mehr. Manifest und Zeugnis tragen einen Sondennamen nur
> noch, wenn die Sonde als **Programm** steht (`manifest::SONDEN_MIT_PROGRAMM`, gepflegt
> gegen `sonden/sonde_*.c`); sonst ist der Name **gestrichen** und die Klasse heißt
> `ungedeckt`.
>
> ```
> A2  write_cr0    ungedeckt   --
> -- 36 Annahmen
> -- 29 Sondenname(n) GESTRICHEN: die Sonde steht nicht als Programm.
> ```
>
> **„Nicht gefahren" war ein Übersetzungsfehler, kein Zwischenzustand.** Der Name las sich
> als Deckung und war eine Zusicherung über das Ausbleiben einer Widerlegung. *Wer einen
> Namen behalten will, schreibt die Sonde* — eine Zeile in `SONDEN_MIT_PROGRAMM`, und er
> steht wieder da. **Genau so ist `sonde_boot_unerreichbar` von 0 auf 1 gekommen:** sie
> existiert als `sonden/sonde_boot_unerreichbar.c` und läuft.
>
> **Und die Zahl bleibt stehen.** Die Schlusszeile sagt, wie viele Namen gestrichen wurden —
> *sonst wäre eine Liste, die schrumpft, von einer, die nie größer war, nicht zu
> unterscheiden.* Dieselbe Logik wie Abschnitt E im Zeugnis: was nicht gedeckt ist, wird
> **benannt getragen** statt weggelassen. Das Zeugnis führt sie als dritte Währung mit
> (`N assumptions (M of them NOT FALSIFIABLE, K UNCOVERED …)`), bewacht von
> `die_befundzeile_trennt_die_nicht_falsifizierbaren_annahmen`.

### Nebenbefund: **eine Sonde trägt zwei Verpflichtungen — über die Dateigrenze**

```bash
grep -rn "sonde_vtd_srtp" beispiele/
# beispiele/02-geraet.gab:53:    falsifier sonde_vtd_srtp;
# beispiele/09-ohne-zeiger.gab:135:    falsifier sonde_vtd_srtp;
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro pruefe \
  beispiele/02-geraet.gab beispiele/09-ohne-zeiger.gab' | head -2
# beispiele/02-geraet.gab: 7 Items, 0 Fehler, 0 Hinweise
# beispiele/09-ohne-zeiger.gab: 20 Items, 0 Fehler, 0 Hinweise
```

`geraet_quittiert` (02) und `vtd_srtp_quittiert` (09) sind **zwei Annahmen mit
verschiedenen Namen und identischem Satz**, und beide nennen dieselbe Sonde.

**`N024` verbietet genau das** — *„a probe belongs to exactly ONE obligation — two on one
probe means a green run discharges both, and one of them nobody ever checked"* — **aber
`N024` läuft je Übersetzungseinheit.** Über die Dateigrenze greift es nicht.

Und `manifest::vereinige`, das die Annahmenmengen mehrerer Dateien zusammenlegt, fängt es
auch nicht: es prüft **gleicher Name → gleicher Inhalt**. Hier stehen *verschiedene* Namen
auf *derselben* Sonde — die Richtung, die keiner der beiden Wächter abdeckt.

*Nicht gebaut in diesem Lauf* (es ist Passarbeit an `namen.rs`, und die Datei gehört mir
nicht). **Vorschlag steht in der Übergabe.**

---

## 4. Der Satz über den **Sperrabdruck** — die Prämisse hat jetzt einen Namen

`beweise/Gruppe_Erhaltung.thy`, Locale `zug`, nimmt `voll i` als *„der Abdruck ist
gehalten"* und schliesst daraus, dass niemand hinsieht. **Dass ein gehaltener Abdruck einen
fremden Kern wirklich fernhält, ist eine Aussage über das Speichermodell** und fällt nicht
in diesen Satz.

Vorher stand sie in `gabbro schablonen` als hängende Prämisse mit der Adresse
*„bräuchte: die AXIOMSCHICHT"*. **Jetzt ist die Adresse bezogen:**

```bash
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro schablonen' | grep "tooth 3"
# --   of those PREMISES WITHOUT A PASS (tooth 3): 8 -- a proof nothing establishes.
./instrumente/pruefe-schablonen.py   # Marke 8, ALL PASS
```

**Zahn 3: 9 → 8.** Gebaut als **erzeugte** Annahme (`manifest.rs::sperrabdruckannahme`),
nicht als verlangte — aus demselben Grund wie die zwei Gleitkommaannahmen: *es ist eine
Maschinenfrage, keine Programmfrage.* Jedes Programm mit einer Verbindungs-Invariante
hätte dieselbe Zeile geschrieben, und eine Zeile, die jeder abschreibt, ist eine, die
niemand liest.

Sie erscheint, sobald eine `group` im Baum steht:

```bash
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro zeugnis \
  beispiele/17-gruppe-ueber-zwei-sperren.gab' | grep sperrabdruck
#      A6  sperrabdruck_haelt_fremde_kerne_fern NICHT FALSIFIZIERBAR -- das Speichermodell …
```

> **Was sich damit NICHT geändert hat:** der Beweis ist derselbe. `abdruck_innen` ist
> weiterhin eine Annahme des Locales, und kein Pass stellt sie her — *kein Pass kann es,
> ein Speichermodell ist keine Aussage über Zustände.* **Was sich geändert hat, ist, dass
> ein Leser des Beweises sie sieht, statt sie zu unterstellen.**
>
> *Zahn 3 zählt Adressen, er prüft sie nicht* — das sagt `pruefe-schablonen.py` selbst, und
> es gilt auch für diese.

---

## 5. Die **Gnadenfrist** wird jetzt verlangt (`H015`)

**Der Posten im Ordner behauptete: ein `rcu … reclaims` ohne benannte Gnadenfristannahme
geht heute durch. Die Handprobe vor dem Bau bestätigt ihn** — und zwar an einer echten
Korpusdatei, nicht an einer konstruierten:

```bash
grep -n "reclaims\|gnadenfrist" beispiele/43-gegenprobe.gab
# 39:rcu BACCT protects { Konten } reclaims frei;      <- und keine Gnadenfrist
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro pruefe beispiele/43-gegenprobe.gab'
# beispiele/43-gegenprobe.gab: 16 Items, 0 Fehler, 0 Hinweise
```

**Die Regel ist dieselbe wie `S003` an `progress`, an einem anderen Konstrukt:** was kein
Pass herstellen kann, wird **verlangt** statt unterstellt.

`H015` steht an der **Rückgewinnungsstelle**, neben `H011`/`H012` — dort, wo die Gefahr
ist, und nicht an der Deklaration. *Deshalb bleibt `43-gegenprobe.gab` grün: die Datei
deklariert `reclaims frei`, gibt aber nirgends zurück.* **Eine Regel an der Deklaration
hätte drei Korpusdateien rot gemeldet, von denen zwei nichts falsch machen.**

Sprechprobe in beide Richtungen:

```bash
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro pruefe \
  beispiele/gift/230-gnadenfrist-fehlt.gab'
# Fehler: [H015] …:47:9: `frei` reclaims, and no assumption names the grace period of `BACCT`
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro pruefe beispiele/31-rcu.gab'
# beispiele/31-rcu.gab: 9 Items, 0 Fehler, 0 Hinweise
```

Die Giftprobe hat **eine Annahme, die von etwas anderem handelt** — nicht gar keine. *Eine
Zählung, die bloss fragt „gibt es hier Annahmen?", wäre zufrieden;* diese Probe misst die
Regel und nicht ihre Umgebung.

Zwei Mutationen, beide gefangen (`cargo test` auf `gabbro-d`, je einzeln gesetzt und
zurückgenommen):

| Mutation | beschädigt | Zustand |
|---|---|---|
| `gnadenfrist-wird-nicht-mehr-verlangt` | `H015` fällt ganz aus | **gefangen** |
| `gnadenfrist-nimmt-jede-annahme` | jede Annahme deckt jede Domäne | **gefangen** |

> **Was `H015` NICHT prüft**, und es steht hier statt in einer Fussnote:
>
> * **nicht, dass die Annahme wahr ist.** Das kann keine Sprache.
> * **nicht, dass ihr Satz von der Gnadenfrist handelt.** Geprüft ist, dass eine benannte
>   Annahme die RCU-Domäne **beim Namen nennt**. Ein Satz, der `BACCT` erwähnt und von
>   etwas anderem redet, kommt durch.
> * **nicht, dass die Sonde läuft** — siehe Abschnitt 3, sie läuft bei keiner der 27.
>
> Was sie herstellt, ist schmal und trotzdem der ganze Punkt: **ein Satz, den jemand
> aufgeschrieben hat und der im Zeugnis steht**, statt einer Unterstellung.
>
> Die Anbindung über den **Namen im Satz** ist die schwächste Stelle der Regel. Der
> saubere Weg wäre ein Grammatikplatz (`rcu D … reclaims P progress G;` — **null neue
> Wörter**, `progress` steht im Wortschatz). Er ist hier nicht gegangen worden, weil er
> `parse.rs`, `ast.rs`, `SYNTAX.md` und drei Korpusdateien berührt, die diesem Lauf nicht
> gehören. *Vorschlag steht in der Übergabe.*

---

## 6. Die Klasse steht jetzt auch in der **Buchung**, nicht nur in der Liste

`gabbro zeugnis` führte jede Annahme mit ihrer Klasse — `Sonde <x>` oder
`NICHT FALSIFIZIERBAR -- <grund>`. **Die Befundzeile darunter warf beide in einen Topf:**

```text
- 13 assumptions, 0 templates (0 of them UNPROVED), 8 direct forms, …
+ 13 assumptions (4 of them NOT FALSIFIABLE), 0 templates (0 of them UNPROVED), …
```

*Dieselbe Klasse wie die Fremdverengungen, die gestern geschlossen wurde: eine Zahl, in
der zwei Währungen stecken, liest sich wie eine.* Die Nachbarn derselben Zeile führen ihre
Untermenge längst mit (`(N of them UNPROVED)`, `(N state their duty)`) — hier fehlte sie.

**Die Frage aus dem Posten — ob eine nicht falsifizierbare Annahme im Zeugnis in der
allgemeinen Fläche verschwindet — hatte damit zwei Hälften, und nur die zweite war offen:**
in der **Liste** stand sie seit jeher als eigene Zeile (wie `A10`); in der **Buchung**
verschwand sie. Jetzt nicht mehr.

```bash
ssh ki-pc-fisch-101 'cd gabbro-d && ./target/release/gabbro zeugnis beispiele/06-annahmen.gab' \
  | grep "assumptions ("
#      13 assumptions (5 of them NOT FALSIFIABLE), 0 templates (0 of them UNPROVED), …
```

Der Test dazu zählt die **Liste** und hält die **Zeile** dagegen — *ein Literal wäre ein
Muster, das seine eigene Antwort enthält* (W16).

---

## 7. Was diese Messung insgesamt **nicht** sagt

* **Sie sagt nichts über x86 gegen aarch64.** Die aarch64-Hälfte des Postens ist versiegelt
  („blockiert — Abstammung", 2026-08-15) und wurde nicht angefasst. *Der einzige
  aarch64-Baum ist nachweislich ein älterer Schnappschuss derselben Abstammung; eine Zahl
  von dort wäre nicht ungenau, sondern falsch — und in der schmeichelhaften Richtung.*
* **Sie sagt nicht, dass die 33 Annahmen ausreichen.** Gemessen ist, was **deklariert**
  ist. Eine Annahme, die niemand aufgeschrieben hat, taucht in keiner dieser Zahlen auf —
  und `sperrabdruck_haelt_fremde_kerne_fern` war bis heute genau so eine. **Die Zahl ist
  in dieser Richtung eine untere Schranke.**
* **Sie sagt nichts über den Korpus ausserhalb `beispiele/`.** Alle Läufe oben stehen auf
  `beispiele/*.gab`. `messung/*/*.gab` ist nicht mitgezählt.
* **Sie misst die Grammatik, wo sie die Sorgfalt zu messen scheint.** Dass jede Annahme
  Sonde oder Grund trägt, erzwingt der Parser.
