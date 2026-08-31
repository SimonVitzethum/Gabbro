# Die 25 Wörter, die an je EINER Datei hängen — und EINE Einsamkeit ist richtig

*Gemessen am 2026-08-31 über dem Stand `f364dc2`, lokal (`free -g`: 31 GB gesamt, 17 GB
verfügbar, 20 Kerne). Werkzeug: `instrumente/pruefe-grammatiktafel.py`, ohne eine Änderung
daran — die Karte, die `traeger()` schon rechnet, einmal ausgeschrieben.*

`messung/GRAMMATIKTAFEL.md` §7 nennt die Zahl und die neun Adressen. Dieses Dokument nennt
je Wort den **Grund**, und der Grund ist der Ertrag: *eine Deckung, die an einer Datei hängt,
misst die Datei und nicht die Sprache* — aber **warum** sie an einer hängt, entscheidet, ob
das zu heilen ist oder zu benennen.

---

## 0. Der Stand, aus dem gerechnet wird

```
219 Terminale · 83 Dateien emittieren vollstaendig · 83 davon uebersetzen
gesenkt 214 · abgesagt 0 · vom Pruefer 1 · UNGEDECKT 4
```

**125 der 219 Terminale sind NUR durch Absenkung gedeckt** — kein Prüferfehlertext nennt sie.
Nur für diese 125 ist die Trägerfrage überhaupt eine Frage; ein Wort mit Prüferdeckung
überlebt den Ausfall jeder Datei. Ihre Verteilung:

| getragen von | Wörter |
|---|---|
| **1 Datei** | **25** |
| 2 Dateien | 15 |
| 3 Dateien | 19 |
| 4–12 Dateien | 38 |
| 13–81 Dateien | 28 |

*Der Median liegt bei vier; das Maximum ist `module` mit 81.* Die 25 sind kein Rand, sondern das erste
Fünftel — und **die 15 daneben sind der nächste Boden**, denn zwei Dateien überleben nur
einen Ausfall.

> **Und keines der 25 steht irgendwo sonst im Baum.** Nachgemessen über alle 426 `.gab` —
> nicht nur über die 83 übersetzenden: für jedes der 25 Wörter ist die Trägerdatei die
> **einzige** Fundstelle überhaupt. Es ist also nicht so, dass ein zweites Programm das Wort
> schreibt und nur an einem `C001` scheitert. *Es ist einmal geschrieben, im ganzen Baum.*

---

## 1. Die Tafel der 25

`⟨G⟩` = Bündel aus der GRAMMATIK · `⟨A⟩` = Bündel aus der AUTORSCHAFT ·
`⟨Z⟩` = Zufall · `⟨E⟩` = eng

| Wort | Trägerdatei | Grammatikstelle | Klasse | warum nur diese |
|---|---|---|---|---|
| `walk` | `beispiele/07-eintritt-und-boot.gab` | `walkdecl` :1158 | **⟨G⟩** | eine Produktion, fünf Pflichtwörter |
| `levels` | `beispiele/07` | `walkdecl` :1158 | **⟨G⟩** | dito |
| `node` | `beispiele/07` | `walkdecl` :1159 | **⟨G⟩** | dito |
| `down` | `beispiele/07` | `walkdecl` :1160 | **⟨G⟩** | dito |
| `leaf` | `beispiele/07` | `walkdecl` :1161 | **⟨G⟩** | dito |
| `mappings` | `beispiele/07` | `domain` :695 | **⟨G⟩** | „erzeugt aus einer `walk`-Deklaration" — ohne `walk` kein Gegenstand |
| `insert` | `beispiele/47-ops-wortmenge.gab` | `opname` :1104 | **⟨G⟩** | braucht `table` + `slot` + `occupied` |
| `remove` | `beispiele/47` | `opname` :1104 | **⟨G⟩** | dito |
| `relabel` | `beispiele/47` | `opname` :1104 | **⟨G⟩** | dito **und** `tree { parent … }` |
| `i8` | `messung/grammatik/zahlbreiten.gab` | `intty` :356 | **⟨A⟩** | eine Datei gegen eine Liste geschrieben |
| `i16` | `zahlbreiten.gab` | `intty` :356 | **⟨A⟩** | dito |
| `i32` | `zahlbreiten.gab` | `intty` :356 | **⟨A⟩** | dito |
| `i64` | `zahlbreiten.gab` | `intty` :356 | **⟨A⟩** | dito |
| `and` | `zahlbreiten.gab` | `accdecl merge` :283 | **⟨A⟩** | dito — mit `i8…i64` hat es NICHTS zu tun |
| `port` | `messung/grammatik/geraeteworte.gab` | `space` :463 | **⟨A⟩** | dito |
| `rc` | `geraeteworte.gab` | `regklasse` :1288 | **⟨A⟩** | dito |
| `seq` | `geraeteworte.gab` | `atomicdecl` :1375 | **⟨A⟩** | dito |
| `exists` | `beispiele/07` | `quant` :682 | ⟨Z⟩ | der seltenere Zwilling von `forall` (11 Dateien) |
| `prim` | `beispiele/07` | `fndecl` :739 | ⟨Z⟩ | ein Kopfwort neben `raw`, `divergent`, `extern` |
| `sizeof` | `beispiele/03-format.gab` | `builtin` :642 | ⟨Z⟩ | der seltenere Zwilling von `lenof` (5 Dateien) |
| `allocs` | `beispiele/09-ohne-zeiger.gab` | `eff` :858 | ⟨Z⟩ | eine Wirkung neben zehn anderen |
| `min` | `beispiele/23-akkumulatoren.gab` | `accdecl merge` :283 | ⟨Z⟩ | `max` (3) und `add` (2) sind geschrieben |
| `finite` | `beispiele/26-gleitkomma.gab` | `narrowstmt` :949 | ⟨Z⟩ | braucht nur einen Gleitkommawert |
| `use` | `beispiele/29-undurchsichtig.gab` | `usedecl` :297 | ⟨Z⟩ | braucht nur zwei Module |
| `boot` | `beispiele/07` | `bootdecl` :245 **und** `space` :463 | ⟨Z⟩ / **⟨E⟩** | **zwei Stellen, zwei Antworten — siehe §4** |

**8 ⟨A⟩ · 9 ⟨G⟩ · 8 ⟨Z⟩ · 1 gespalten.**

---

## 2. ⟨G⟩ — das Bündel lässt sich nicht teilen, aber verdoppeln

`walkdecl` ist **eine** Produktion:

```ebnf
walkdecl = "walk" ident "levels" constexpr "{"
             "node" ":" array ","
             "down" ":" ident "when" pred ","
             "leaf" ":" pred ","
             { invariant }
           "}" ;
```

Keines der fünf Wörter ist ohne die anderen vier schreibbar — **das ist keine Eigenschaft des
Korpus, sondern der Grammatik.** Die Frage „lässt sich das Bündel teilen?" hat darum eine
Antwort, und sie ist nein.

> **Die richtige Frage ist eine andere: lässt es sich VERDOPPELN?** Ein zweiter `walk` über
> einer anderen Struktur trägt alle fünf noch einmal, und dann kostet ein `F06` in
> `beispiele/07` nicht mehr fünf Zellen, sondern keine. *Ein Bündel, das an zwei Stellen
> steht, ist kein Bündel mehr, sondern eine Form mit zwei Belegen.*

Dasselbe für `insert`/`remove`/`relabel`: `opdecl = "ops" opname { "," opname } ";"` verlangt
eine `table` mit `count`, `slot` und `occupied`; `relabel` zusätzlich eine `tree`-Kante.
Verdoppelbar, nicht teilbar.

`mappings` hängt anders am Bündel — es steht in `domain` und nicht in `walkdecl`, aber die
Grammatik sagt an Ort und Stelle *„erzeugt aus einer `walk`-Deklaration"*. Ohne `walk` gibt es
den Gegenstand nicht. **Es fällt mit dem Bündel und steigt mit ihm.**

---

## 3. ⟨A⟩ — und das ist ein Befund über die eigene Methode

Acht der 25 hängen an den **zwei Dateien, die in der Nacht zuvor genau gegen diese Lücke
geschrieben wurden.** `zahlbreiten.gab` trägt `i8`, `i16`, `i32`, `i64` und `and`;
`geraeteworte.gab` trägt `port`, `rc` und `seq`. Die acht Wörter haben grammatisch **nichts
miteinander zu tun** — `intty`, `accdecl`, `space`, `regklasse` und `atomicdecl` sind fünf
Stellen in fünf Abschnitten. Sie stehen zusammen, **weil eine Datei gegen eine Liste
geschrieben wurde.**

> **Eine Lücke mit EINER Datei zu schließen verschiebt sie, sie schließt sie nicht.** Vorher
> waren die acht `UNGEDECKT`; jetzt sind sie `gesenkt` und hängen an einem einzigen `cc`-Lauf.
> Das ist besser — eine Absenkung, die läuft, ist mehr als eine, die es nie tat —, **aber es
> ist dieselbe Bauart wie die Lücke, gegen die es geschrieben wurde.**
>
> *Das ist die Selbstauskunft dieses Dokuments und der Grund, warum die Antwort in §5 nicht
> „noch eine Datei" heißt.* Wer die 25 in EINE zweite Datei schreibt, hat 25 Wörter an zwei
> Dateien und eine neue Adresse, an der es weh tut.

⟨A⟩ ist damit die **billigste** Klasse: jedes der acht Wörter ist einzeln schreibbar, an einer
Stelle, die zu ihm gehört. Es braucht keinen Kunstgriff, nur einen anderen Ort.

---

## 4. `boot` — ein Wort, zwei Stellen, zwei verschiedene Antworten

`boot` steht in `beispiele/07` an **beiden** Stellen, an denen die Grammatik es kennt:

```ebnf
bootdecl = "boot" ident "arch" ident "{" { bootstep } "dispatch" path ";" "}" ;   (* :245 *)
space    = "normal" | "mmio" | "dma" | "code" | "boot" | "port" | ident ;         (* :463 *)
```

Als **Adressraum** (`ptr<boot, r> T`, `retires t from boot`) ist es ⟨Z⟩ und so billig wie
`port`. Als **`bootdecl`** ist es ⟨E⟩ — und das ist die eine benannte Absage dieses
Dokuments:

> **Ein `bootdecl` ist die Modusleiter EINER Maschine, und es gibt genau eine davon je
> Architektur.** `write_cr3` · `write_cr4(PAE)` · `wrmsr_efer(LME)` · `write_cr0(PG)` ist der
> x86_64-Weg in den Langmodus, nicht *ein* Weg. Ein zweites `bootdecl` wäre entweder eine
> **Abschrift** — Falle 80 im Kleinen, ein Programm nur damit ein Zähler steigt — oder
> `aarch64`, und das ist versiegelt (`CLAUDE.md`: „blockiert — Abstammung", kein dritter
> Anlauf).
>
> **Die Einsamkeit des `bootdecl` ist richtig und wird benannt, nicht geheilt.**

Was daraus folgt, ist eine Unterscheidung, die diese Tafel selbst schon macht (§6.2 der
GRAMMATIKTAFEL): **ein Terminal ist nicht dasselbe wie eine Form.** Wird `boot` in einer
zweiten Datei als `space` geschrieben, ist das **Wort** an zwei Dateien gedeckt und die
**Form** `bootdecl` weiterhin an einer. Beides ist wahr, und beides gehört gesagt — *wer nur
den Zähler nennt, hat den `bootdecl` stillschweigend für gedeckt erklärt.*

Für die Reichweite der Form über den Korpus steht `gabbro blindstellen` (FORM × POSITION), und
das ist die andere Grundgesamtheit. **Diese Tafel misst Wörter; sie soll nicht so tun, als
misse sie Formen.**

---

## 5. Was daraus folgt

| Klasse | Wörter | Weg |
|---|---|---|
| ⟨A⟩ | `i8` `i16` `i32` `i64` `and` `port` `rc` `seq` | an einen Ort schreiben, **der zum Wort gehört** — nicht wieder in eine Liste |
| ⟨Z⟩ | `exists` `prim` `sizeof` `allocs` `min` `finite` `use` `boot`(space) | dito; jedes einzeln billig |
| ⟨G⟩ | `walk` `levels` `node` `down` `leaf` `mappings` | **ein zweiter `walk`** über einer anderen Struktur — sechs auf einmal |
| ⟨G⟩ | `insert` `remove` `relabel` | **eine zweite `table` mit `ops`** und einer `tree`-Kante |
| ⟨E⟩ | `bootdecl` (die FORM) | **benannt, nicht geheilt** |

**Und die Marke, die daraus wird, misst nicht die 25.** Sie misst *wie viele Wörter an je
einer Datei hängen* — eine Zahl, die auch steigt, wenn ein neues Wort in die Grammatik kommt
und genau ein Programm es schreibt. *Eine Ratsche über einer Zahl, die aus zwei Richtungen
wächst, braucht ihren Grund an der Marke* (§ Ratschen, `dokumente/`).

---

## 5b. Und so ist es ausgegangen — **25 → 0**, am selben Abend

Vier Programme aus der Grammatik, jedes mit einem Gegenstand statt einer Liste. Jedes prüft
mit **0 Fehlern, 0 Hinweisen, 0 `C001`** und übersetzt unter `cc -std=c11 -Wall -Wextra
-Werror` bei `-O0` und `-O2`:

| Datei | verteilt | Gegenstand |
|---|---|---|
| `messung/grammatik/blocklauf.gab` | `walk` `levels` `node` `down` `leaf` `mappings` | der Indirektionsbaum eines Inodes |
| `messung/grammatik/tabellenworte.gab` | `insert` `remove` `relabel` `exists` | ein Gerätebaum: Gerät am Bus am Bus |
| `messung/grammatik/messreihe.gab` | `i8` `i16` `i32` `i64` `and` `min` `finite` `sizeof` | eine Messreihe |
| `messung/grammatik/raumworte.gab` | `port` `rc` `seq` `boot` `prim` `allocs` `use` | ein Zeitgeber am Altlastenbus |

```
vorher   25 an je EINER Datei · 15 an zwei · Median 4
nachher   0 an je EINER Datei · 38 an zwei · Median 4
```

**`gesenkt` bleibt bei 214, `UNGEDECKT` bei 4.** Die Programme decken nichts Neues ab; sie
machen die vorhandene Deckung unempfindlich. *Dass es sich in keiner Deckungszahl zeigt, ist
der Punkt.*

Was dabei herausgefallen ist, steht in `messung/GRAMMATIKTAFEL.md` §9: ein Formatfeld namens
`gueltig` kollidiert mit der erzeugten Prüfkörperfunktion (`beispiele/gift/413`), und die
Sprechprobe des Wächters selbst hing daran, dass ein Wort einsam ist — sie brach ab, sobald
keines mehr einsam war.

**Und §4 steht unverändert:** `bootdecl` bleibt allein in `beispiele/07`. Benannt, nicht
geheilt.

---

## 5c. Und am selben Abend **0 → 3**, aus der ANDEREN Richtung

§5 nennt sie und hier ist sie: *„eine Zahl, die auch steigt, wenn ein neues Wort in die
Grammatik kommt und genau ein Programm es schreibt."* Drei Programme für die
Quantorendomänen `chain`, `queue` und `threads` (`beispiele/55`–`57`,
[`QUANTORENDOMAENEN.md`](QUANTORENDOMAENEN.md)) haben drei Zellen von `UNGEDECKT` auf
`gesenkt` gedreht:

```
vorher    chain · queue · threads  an je NULL Dateien, weil UNGEDECKT
nachher   chain · queue · threads  an je EINER Datei
          0 an je einer Datei -> 3 · 38 an zwei -> 36 · Median 4
```

**Ein Wort, das von null auf eins geht, hebt eine Zahl, die Einsen zählt.** Der Gegenstand
ist gewachsen, nicht die Schwäche — und `MARKE_ALLEIN` steht darum auf 3, mit diesem Grund an
der Marke (`instrumente/pruefe-grammatiktafel.py`). *Die Zweierzahl ist im selben Zug von 38
auf 36 gefallen, weil zwei Wörter nach OBEN gewandert sind; auch das ist die gute Richtung
und darum keine Ratsche.*

### Was damit offen ist, und es wird nicht weggeredet

Die drei hängen an je einer Datei, und das ist genau der Zustand, den §3 als *„dieselbe
Bauart wie die Lücke, gegen die es geschrieben wurde"* benennt. **Der Ausweg ist derselbe wie
dort und nicht der billige:** ein zweiter Träger müsste ein zweiter **Gegenstand** sein.

| Wort | zweiter Gegenstand, der sich anbietet | Zustand |
|---|---|---|
| `chain` | eine Freiliste (`beispiele/27`) — *„alles, was an der Kette hängt, ist unbelegt"* trägt die Domäne | **offen** |
| `queue` | eine zweite Warteschlange sagt nichts Neues — die Domäne selbst ist der Befund (`QUANTORENDOMAENEN.md` §3) | **offen, und der Nutzen ist fraglich** |
| `threads` | dasselbe: solange `t` an keiner Deklaration hängt, ist der zweite Beleg derselbe Satz | **offen, und der Nutzen ist fraglich** |

> **Für zwei der drei wäre ein zweites Programm heute eine Abschrift.** `queue` und `threads`
> tragen ihre Zusicherung nicht bzw. nur halb; ein zweiter Beleg dafür misst dieselbe Lücke
> ein zweites Mal. *Das ist die `bootdecl`-Lage aus §4 in einer anderen Farbe: benannt, nicht
> geheilt — und der Grund ist hier nicht die Maschine, sondern die Domäne.*

---

## 6. Was dieses Dokument NICHT sagt

1. **Nichts darüber, ob die Absenkung richtig ist.** Ein Wort an fünf Dateien kann fünfmal
   dasselbe falsche C erzeugen. Die Trägerzahl misst die **Empfindlichkeit der Messung**, nicht
   die Güte der Sprache.
2. **Nichts über die 94 Wörter mit Prüferdeckung.** Für sie ist die Trägerfrage keine —
   ein Prüferfehlertext nennt sie, und der fällt mit keiner `.gab`-Datei aus.
3. **Nichts über Formen.** Siehe §4. Ein zweiter Beleg für ein Wort ist kein zweiter Beleg für
   die Produktion, in der es steht.
