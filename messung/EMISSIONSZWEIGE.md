# Die Auffangzweige der Emission — was hinter `_ =>` entschieden wurde

*Gemessen und aufgeloest am 2026-08-21.*

`mutiere-pruefer.py` sagt den Satz, aus dem dieser Posten folgt:

```
   Eine Flaeche mit 0 Mutationen ist nicht gedeckt, sondern unbeschaedigbar.
   `240 von 240` misst den PRUEFER; ueber Annotation und Code sagt es nichts.
```

**Eine Ebene tiefer gilt derselbe Satz.** Ein `_`-Zweig ueber einem Summentyp *hat* eine
Antwort — er gibt sie nur nicht zu Protokoll. Damit kann an ihr auch nichts fallen: er ist
so unbeschaedigbar wie eine Flaeche ohne Mutation, und aus demselben Grund.

---

## 1. Die Messung — der Befehl, der sie nachrechnet

Ein Auffangzweig ist hier `_ =>` (mit oder ohne Wache) in einem `match`. Ob er ueber einem
**AST-Summentyp** steht, wird nicht aus dem Kopf geraten, sondern aus den **Geschwister-
zweigen** abgelesen: ein Zweig `ExprArt::Zahl(..) =>` nennt den Typ woertlich.

```bash
python3 /tmp/.../zaehle_auffang.py crates/gabbro-check/src/emit.rs      # Werkzeug s. u.
```

Das Werkzeug ist ein Wegwerfzaehler und liegt nicht im Baum; sein Ergebnis steht hier, und
die Zahlen sind mit `grep -c '_ =>'` grob nachpruefbar — **grob**, weil `grep -c` ZEILEN
zaehlt und die Zweige mit Wache (`_ if … =>`) nicht kennt:

```bash
grep -c '_ =>' crates/gabbro-check/src/emit.rs        # 51  (vorher 73)
grep -c '_ =>' crates/gabbro-syntax/src/parse.rs      # 34  (unveraendert)
```

### Der Stand, Datei fuer Datei

| Datei | Auffangzweige | davon ueber einem AST-Summentyp |
|---|---:|---:|
| `emit.rs` **vorher** | 79 | **58** |
| `emit.rs` **nachher** | 56 | **37** |
| `parse.rs` | 34 | 33 (davon 32 ueber `Art`/`Kw`, **1** ueber `ExprArt`) |
| `m1.rs` | 37 | 31 |
| `namen.rs` | 28 | 25 |
| `wirkungen.rs` | 11 | 11 |
| `kosten.rs` | 11 | 9 |

> **Der Auftrag nannte 28 fuer `emit.rs`; gemessen wurden 58.** Die Differenz ist keine
> Meinungsverschiedenheit ueber die Definition, sondern ueber die Zaehlweise: 28 trifft die
> Zweige mit *stiller Vorgabe* (`_ => {}`, `_ => <Wert>`), 58 auch die *Vorbehalte*
> (`_ => None`, `_ => false`), deren Rufer beim Namen absagt. **Beide Zahlen stehen hier**,
> weil nur die zweite die Frage beantwortet, die der Auftrag stellt: *wie viele
> Entscheidungen stehen nicht im Quelltext?*

---

## 2. Was aufgeloest wurde — je Zweig, was vorher still fiel

**21 der 58** sind ausgeschrieben. Sieben davon haben beim Ausschreiben einen Fehler
freigelegt; die uebrigen vierzehn haben eine Entscheidung sichtbar gemacht, die richtig war
und nirgends stand.

### 2.1 Die sieben, die einen Fehler freigelegt haben

| # | Stelle | Was der Sammelzweig zugesagt hat | Was wirklich dahinter lag |
|---|---|---|---|
| 1 | `sammle_retry` (`StmtArt`) | „hier steht kein `retry`" | Er erreichte **`locks`, `match`, `narrow` und den Rumpf eines `retry` — sonst nichts.** Ein `retry` in einem `if`, `breaking`, `observes`, im `else` eines `let … else`, im `update`-Rumpf eines `exchange` oder in einem `forever`/`traverse` bekam **keinen Eintrag in der Schrankenkarte** — und die Absenkung antwortete darauf mit `C001`: *„`bounded … ops` — the per-pass cost is not fixed"*. **Die Kosten standen fest.** Eine Absage mit dem falschen Grund ist einen Schritt von einer stillen entfernt. |
| 2 | `verbundlokale` (`StmtArt`) | „diese Anweisung traegt keinen Unterblock" | Neun handgeschriebene Abstiegsarme neben `crate::unterbloecke`, und die Kopie war abgedriftet: **`observes { … }` und der `update`-Rumpf eines `exchange`** wurden nie besucht. Ein `let c : Completion` darin wurde mit `c->len` statt `c.len` abgesenkt — genau der Fehler vom 2026-08-20, eine Ebene tiefer. |
| 3 | `ausdruck_geraet` (`ExprArt`) | „unbekannte Form → leere Zeichenkette, und `bank` faengt das ab" | **Das Fehlerzeichen ueberlebte die Zusammensetzung nicht.** In einem Blatt war `""` richtig; steckte das Blatt in einem `Binaer` oder einer `Klammer`, kam `" * 16"` bzw. `"()"` heraus — **nicht leer**, also durch die Wache. Im Erzeugnis stand dann `(d->basis + ( * 16) + …)`. *Der Fehler fiel bei `cc`* — und genau darum geht es hier nicht: **eine Weigerung, auf die man baut, ist eine Zusage.** Die Funktion traegt jetzt `Option` und weigert sich an der Stelle, die den Grund kennt. |
| 4 | `ausdruck_format` (`ExprArt`) | „alles andere kann der gewoehnliche Ausdrucksleser" | Zwei Formen kann er nicht. **`!feld`** ging an `ausdruck` und wurde `!(feld)` statt `!(F_feld(v))` — ein Bezeichner, den die erzeugte Datei nirgends erklaert. Und ein **Ort MIT Suffix** (`a.b`, `a[i]`) wurde klaglos `a->b`, in einer Pruefkoerperfunktion, deren einziges Objekt `v` heisst. |
| 5 | `benutzte_namen` / `sammle_expr_namen` (`ExprArt`) | zweimal dieselbe Frage | **Zwei Register ueber derselben Sache** (W7), und sie waren auseinandergelaufen: der Praedikatsleser stieg **nicht** in Indexausdruecke ab, der Anweisungsleser schon. `retry … until t.slots[i] == 0` liess `i` als tot gelten. Zusammengezogen zu `ort_namen`. |
| 6 | `rechnet_mit_gleitkomma` (`ItemArt`) | „dieses Item fuehrt keinen Typ" | Es fragte fuenf Itemarten und liess neunzehn fallen — darunter **`table` und `format`**. Eine Einheit mit `f64` im Slot rechnete mit Gleitkomma **ohne die Ansage**, und die Ansage ist keine Verzierung: sie sagt `-ffast-math ist verboten` und benennt die SSE2-Annahme. **Eine Aussage, die fehlt, ist keine schwaechere Aussage, sondern gar keine.** |
| 7 | `schrittbits` (`Option<OrtSuffix>`) | „`transition` on an indexed place" | Der Zweig stand fuer **zwei** Suffixformen und nannte **eine**. Ein `->`-Zugriff bekam die Absage fuer einen Index zu lesen. *Eine Weigerung mit dem falschen Grund ist eine falsche Zusage.* |

### 2.2 Die vierzehn, die eine ungeschriebene Entscheidung sichtbar gemacht haben

| Stelle | Die Entscheidung, die jetzt dasteht |
|---|---|
| `anweisung` (`StmtArt`) | Hinter *„no lowering: statement kind"* stand **genau eine** Anweisungsart: `breaking`. Sechzehn von siebzehn senken ab — die Absage nannte keine davon. Jetzt: `StmtArt::Bricht(_) => weigere(…)` mit dem Grund (Beweisregion, Wiederherstellungspflicht im Manifest, Regel A). |
| `ausdruck` (`ExprArt`) | Hinter *„expression form"* standen **genau drei** Formen. Jede hat jetzt ihren eigenen Satz: `sizeof`/`lenof`/`aligned` (kein Objekt, das man messen koennte), `old(place)` (nichts im C haelt den alten Wert), `result` (ein Vertrag wird zur Uebersetzungszeit geprueft, W6). |
| `pred_c` (`PredArt`) | Fuenf Formen sind **keine Laufzeitbedingung**: Quantor und `reaches` brauchten eine Schleife (die `costs` nie gezaehlt hat), `x in D` dieselbe Gestalt, `Held(L)` ist ein **Zeuge** — eine Pruefung dafuer waere genau der Laufzeittest, den W6 verbietet —, und `a => b` schreibt der Erzeuger nicht in `!a || b` um. |
| `wirkungsattribut` (`WirkungArt`) | `pure`/`const` sind **Anweisungen an den C-Uebersetzer**, keine Buchung. Eine neue `WirkungArt`, die still hier hereinfaellt, waere nicht ein fehlender Tabelleneintrag, sondern **die Erlaubnis, den Ruf zu loeschen.** |
| `Ordnung` (Sammelgang der Atomics) | `_ => relaxed` deckte `Some(Relaxed)` **und** die fehlende Klausel — beide heute richtig — und haette eine fuenfte Ordnung ebenso gedeckt, mit der schwaechsten von allen. *Eine falsche Speicherordnung faellt in keinem Testlauf auf; sie faellt auf einer anderen Maschine auf.* |
| `benutzte_namen` (`StmtArt`) | **Der Gegenfall, und er ist der wichtigste:** `breaking` NICHT zu betreten ist richtig, weil `anweisung` es beim Namen ablehnt. Die Menge speist zwei Verbraucher mit **entgegengesetzter** sicherer Richtung — zu wenige Namen und eine Tabelle verliert ihren `T_speicher`, zu viele und ein toter Parameter verliert sein `(void)k;`, was `cc -Wextra -Werror` als Fehler meldet. **Eine Ueberschaetzung ist hier nicht die vorsichtige Antwort, sondern die andere.** |
| `pred_namen` (`PredArt`) | Dieselbe Rechnung: die vier Beweisformen lesen nichts, **weil** `pred_c` sie ablehnt. |
| `sammle_expr_namen` (`ExprArt`) | Dieselbe Rechnung fuer `sizeof`/`old`/`result`. |
| `sprungziele` (`StmtArt`) | Der Abstieg kommt von `unterbloecke` — und das erzwingt fuer eine neue `StmtArt` nur die Frage *„traegst du einen Block?"*, **nicht** *„springst du?"*. Ein neues Sprungwort waere hier stumm durchgefallen, waehrend `-Wunused-label` danach eine Marke meldet, die sehr wohl angesprungen wird. |
| `emittiere`, Namensindex (`ItemArt`) | Der Index ist die Karte, auf der jede spaetere Absenkung nachschlaegt. Beim Ausschreiben hat **`rustc` sofort zweimal widersprochen**: `Tabelle` sei unerreichbar (steht laengst da) und `Statisch` fehle. *Ein `_`-Arm laesst nicht nur Neues durchfallen; er laesst auch vergessen, was schon da ist.* |
| `benutzt`-Sammler (`ItemArt`) | Nur ein `Block` kann eine Tabelle beim Namen nennen. Zwei Traeger sind knapp daran vorbei und jetzt begruendet ausgeschlossen: ein `device` senkt ueber `d->basis` ab, ein `boot` senkt `set x = <expr>` als `static const uint64_t` ab — **ein Tabellenzugriff waere dort schon kein gueltiges C.** |
| `#define`-Sammler (`ItemArt`) | Der Gang schreibt nur `#define`s; alles andere hat seinen eigenen Gang. *Der Sammelzweig las sich wie „das uebrige kommt spaeter"; er sagte aber nur „hier nicht".* |
| `eigene_sicht` (`TypExpr`) | Skalare tragen keinen `.`- und keinen `->`-Zugriff. Zwei sind es nur beinahe: `[T; N]` und ein anonymer Verbund in der Signatur — **Formen ohne Absenkung**, die `ctyp` beim Namen ablehnt. |
| `geist_wert` (`ExprArt`) | Ein Geist ist **linear**: keine Felder, keine Elemente, keine Arithmetik. Damit kann keine der uebrigen elf Formen einen liefern — **ausser der Klammer**, und dass `let p = (mmu_an(p));` nicht geloescht wird, steht jetzt als der eine offene Punkt daneben. |

### 2.3 Ein Zweig, der ausgeschrieben und trotzdem unerreichbar ist

`schrittbits`, Arm `Some(OrtSuffix::Ueber(_))`. `parse::transition` setzt
`pfeil_ist_suffix = false`, solange es den Ort links vom `:` liest (G3) — in `ST: ACK -> ACK`
waere `->` sonst zugleich Zeigerzugriff und Uebergangspfeil. **Ein `R->A:` faellt schon im
Parser an `P001`.**

Der Arm bleibt, weil der `match` erschoepfend sein muss, und er sagt, **worauf er sich
verlaesst**. Er traegt eine Absage und kein `unreachable!()`: eine Zusicherung ueber die
Kistengrenze haelt der Uebersetzer nicht, und faellt die Parserregel, soll hier eine benannte
Weigerung fallen und kein Absturz.

**Und er hat keine Mutation und darf keine haben** — eine Mutation, die nichts beschaedigen
kann, ist schlimmer als ein toter Anker.

---

## 3. Was NICHT aufgeloest wurde, und warum

**37 Auffangzweige ueber AST-Summentypen bleiben in `emit.rs`.** Sie sind fast alle von einer
Bauart:

```rust
fn feldlaenge(e: &Expr, u: &Namen) -> Option<String> {
    match &e.art {
        ExprArt::Zahl(n) => Some(n.to_string()),
        ExprArt::Ort(o) if … => Some(…),
        _ => None,          // <- der Rufer sagt `C001` mit einem Grund
    }
}
```

Das ist ein **Vorbehalt** und keine stille Zusage: der Wert `None` reist zum Rufer, und dort
steht ein `weigere(…)` mit einem Satz. Sie auszuschreiben haette pro Stelle zehn Zeilen
gekostet und **keine Entscheidung sichtbar gemacht, die nicht schon im Rufer steht.**

Der eine, der bleibt und ein Sammelzweig mit Absage ist:

* `rumpf_als_wert` — `_ => weigere(…, "statement in an `update` body … only `return <expr>`
  and `if <expr> { … }` say that")`. **Die Erlaubnisliste steht in der Meldung selbst**, und
  sie ist zwei Eintraege lang; sie auszuschreiben hiesse, fuenfzehn Arme mit demselben Satz
  zu fuellen.

---

## 4. `parse.rs` — der Kalibrierungspunkt, und die Zahl faellt niedrig

**34 Auffangzweige, und der Ertrag ist NULL.** Das ist kein Ausrutscher der Messung, sondern
ein Datum ueber die Grenze des Musters.

| Klasse | Zahl | Warum der Sammelzweig richtig ist |
|---|---:|---|
| benannte Absage (`P…`) | 20 | *„hier stand ein Wort, das hier nicht stehen darf"* — die Absage IST der Zweig |
| Schleifenausgang | 4 | Vorrangkletterei: `_ => break` heisst *„kein Operator dieser Stufe mehr"* |
| Ja/Nein ueber dem NAECHSTEN Wort | 6 | `_ => false` / `_ => None` auf die Frage *„faengt hier ein Typ an?"* |
| Wiederherstellungsschleife | 2 | `_ => {}` heisst *„weiterspringen"* — die Schleife sucht eine Grenze |
| Vorgabeproduktion der Grammatik | 1 | `_ => self.zuweisung_oder_ruf()?` — die EBNF hat diese Vorgabe selbst |
| **ueber einem AST-Summentyp** | **1** | `let … else` ueber etwas, das kein `call` und kein `place` ist — **und der Zweig ist bereits eine benannte Absage `P016` mit Grammatiknotiz.** |

### Der strukturelle Grund, und er ist nennbar

> **Ein Parser matcht ueber ein OFFENES Alphabet.** Das naechste Zeichen kann alles sein, und
> „alles andere" ist darum ein wirklicher, wohldefinierter Fall mit einer wirklichen
> Antwort: **ablehnen.**
>
> **Ein Erzeuger matcht ueber einen GESCHLOSSENEN Baum**, den ein Pass davor schon
> angenommen hat. „Alles andere" ist dort kein Fall, sondern eine Menge, die der Leser des
> Quelltextes nicht aufzaehlen kann — und die Antwort darauf ist eine Vermutung.

Das Muster wandert also **nicht** vom Erzeuger zum Parser. Wo es das naechste Mal gesucht
wird, sollte es dort gesucht werden, wo ein Pass ueber einem *fertigen* Baum laeuft:
`m1.rs` (31), `namen.rs` (25), `wirkungen.rs` (11 von 11).

---

## 5. Mutationen je Emissionsflaeche — vorher und nachher

```bash
python3 mutiere-pruefer.py --anker      # Ankerstand und Flaechenpruefung, ohne Bau
python3 mutiere-pruefer.py              # der volle Lauf
```

| Flaeche | vorher | nachher |
|---|---:|---:|
| `pruefer` | 157 | **158** |
| `annotation` | 0 | 0 |
| `code` | 79 | **84** |
| `schablone` | 3 | 3 |
| **Summe der Flaechen** | **239** | **245** |
| **Mutationen gesamt** | **240** | **245** |

### Die eine Zeile, die vorher nicht aufging

**239 ≠ 240.** Eine Mutation (`ops-nimmt-jedes-wort`, `parse.rs`) trug
`flaeche="pass"` — **ein Name, den `FLAECHEN` nicht kennt.** Die Aufstellung zaehlt
`m.flaeche == name` ueber die bekannten Flaechen; ein Tippfehler darin nimmt die Mutation aus
**jeder** Zeile heraus, ohne irgendwo aufzufallen. Die Gesamtzahl stimmte weiter.

*Dieselbe Klasse wie die Kiste im Pfad einen Tag vorher:* **eine Flaeche, die kein Werkzeug
erreicht, fehlt nicht laut — sie fehlt still.** Behoben, und `mutiere-pruefer.py` prueft es
jetzt selbst (`flaechen_stand()`), mit Sprechprobe.

### Die fuenf neuen Mutationen

Alle auf `emit.rs`, Flaeche `code`, jede beschaedigt **genau eine** aufgeloeste Entscheidung:

| Mutation | Beschaedigte Entscheidung |
|---|---|
| `sammler-erreicht-den-zweig-nicht-mehr` | `sammle_retry` sieht ein `if` nicht mehr |
| `breaking-heisst-wieder-anweisungsart` | die Absage nennt `breaking` nicht mehr beim Namen |
| `ausdrucksform-heisst-wieder-ausdrucksform` | die drei Ausdrucksformen fallen unter einen Satz |
| `gleitkomma-im-slot-wird-nicht-angesagt` | ein `f64` im Slot bleibt unangesagt |
| `indexuebergang-ohne-grund` | die Absage am Index nennt die Form ohne den Grund |

Zwei **bestehende** Anker sind mitgezogen worden, weil ihr Text verschwunden ist:

* `ausdruck-faellt-offen-auf-null` stand auf `_ => { weigere(…, "expression form") }` und
  zeigt jetzt auf den `old(place)`-Arm — **dorthin, wo die Probe steht**;
* `budget-ist-schleifenzaehler` hat eine Einrueckungsebene verloren, weil `sammle_retry`
  flacher geworden ist.

```bash
python3 mutiere-pruefer.py --anker     # 245 von 245 Ankern greifen -- ALL PASS
```

### Der volle Lauf

```bash
ssh ki-pc-fisch-101 'cd gabbro-i && export PATH=$HOME/.cargo/bin:$PATH && python3 mutiere-pruefer.py'
# == 245 von 245 gueltigen Mutationen gefangen (100 %) ==
#      pruefer      158 Mutationen
#   !! annotation     0 Mutationen
#      code          84 Mutationen
#      schablone      3 Mutationen
```

**Alle fuenf neuen Mutationen wurden gefangen.** Und die Aufstellung geht jetzt auf:
158 + 0 + 84 + 3 = **245** = Gesamtzahl.

---

## 6. Der Waechter, der dabei rot werden konnte und es nicht war

`pruefe-abstieg.py` entschuldigte einen Pass, sobald **irgendwo in der Datei** ein
`_ => weigere(` stand:

```python
weigert = "_ => weigere(" in ganz          # <- je DATEI
```

`emit.rs` stand damit als *„weigert sich benannt"* da — **waehrend drei Sammler darin ihre
Unterbloecke nicht erreichten** (`sammle_retry` kein `if`, `verbundlokale` kein `observes`,
`benutzte_namen` kein `breaking`). Ein Vorbehalt an einer Stelle deckte Luecken an drei
anderen.

*Genau die Vergroeberung, die dieser Waechter zwei Tage vorher an den Paessen gemessen und
bei sich selbst stehen gelassen hatte* — dieselbe Klasse, eine Ebene hoeher.

Die Entschuldigung gilt jetzt **je Funktion**, mit einer eigenen Sprechprobe (R14): eine
Giftquelle mit zwei Funktionen — eine weigert sich benannt, die andere hat eine Luecke —
muss die Luecke melden **und** die Weigerung entschuldigen.

```bash
python3 pruefe-abstieg.py
# ...
#   emit::rumpf_als_wert       weigert sich benannt (8 Arten)
#   (Sprechprobe: die Weigerung entschuldigt NUR ihre eigene Funktion -- ok)
# == ABSTIEG: ALL PASS -- jeder Pass erreicht jeden Unterblock ==
```

---

## 7. Was die Emission dazu sagt

```bash
ssh ki-pc-fisch-101 'cd gabbro-i && export PATH=$HOME/.cargo/bin:$PATH && ./pruefe-emission.sh'
# == EMISSION: ALL PASS -- 19 durchgestochen, 47 von 47 uebersetzen ==
```

**Beide Zahlen unveraendert.** Das ist die erwartete Antwort und trotzdem eine Aussage: die
21 aufgeloesten Zweige haben an keiner Stelle die Absenkung eines Programms veraendert, das
vorher durchkam. *Wo ein Verhalten sich geaendert hat — `retry` im `if`, `f64` im Slot,
`observes` im Verbundsammler —, hatte der Korpus keine Stelle;* die Proben dafuer stehen im
Test, nicht im Korpus.

---

## 8. Was das NICHT heisst

* **Ausgeschrieben ist nicht geprueft.** Von 21 aufgeloesten Zweigen tragen **fuenf** eine
  Mutation mit einer Probe. Die uebrigen sechzehn sind Entscheidungen, die jetzt im
  Quelltext stehen und deren Ausfall der **Uebersetzer** meldet (ein neuer Summentypfall ist
  ein `E0004`) — *aber ihr falscher INHALT faellt an nichts.* W10: nicht abgewiesen ist nicht
  bestaetigt.
* **Die 37 verbliebenen Zweige sind begruendet, nicht gepruefte.** Die Begruendung ist
  jeweils *„der Rufer sagt `C001`"*; dass er das in jedem Fall tut, ist gelesen und nicht
  gemessen.
* **`parse.rs` mit 0 Funden ist eine Aussage ueber `parse.rs`,** nicht ueber Parser im
  Allgemeinen und nicht ueber die uebrigen Paesse. `m1.rs` mit 31 steht unangetastet da.
