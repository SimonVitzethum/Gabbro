# Die zwölf Wildcards, selbst nachgezählt — und zwei Zahlen der Buchung sind falsch

*Gemessen am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 13 GB verfügbar, 20 Kerne,
`ulimit -v unlimited`). Korpus: **499 `.gab`-Dateien** — alles unter `beispiele/`,
`beispiele/gift/`, `messung/` und `halde.gab`.*

**Gezählt mit `eprintln!`, nicht mit `panic!`.** Der erste Treffer bricht den Prozess ab und
verdeckt jeden späteren im selben Lauf — die Falle steht seit heute in `CLAUDE.md`
(*„Eine Messung, die beim ersten Treffer abbricht, misst die falsche Frage"*).

---

## Die Messapparatur, und warum sie den Befehl mitschreibt

Ein Wildcard in einem **Pass** wird von jedem Befehl erreicht, der diesen Pass fährt. Wer
`pruefe`, `emit`, `zeugnis` und `zeremonie` über denselben Korpus fährt und die Treffer in
**einen** Topf wirft, zählt so eine Stelle **viermal**.

> **Genau das ist mit `domaene.rs` passiert.** Gebucht standen `8x Wahrheit`; gemessen sind es
> **2 je Lauf** — 2 × 4 Befehle = 8. *Die Vier steckte im Messgerät, nicht im Gegenstand.*

Die Zahlen unten sind deshalb **je Befehl** erhoben (`2>&1 >/dev/null | sed s/^WC /WC[befehl] /`)
und werden dem Befehl zugeordnet, der die Stelle wirklich erreicht.

## Die Zählung

| # | Stelle | Treffer | gesehene Konstruktoren | Kategorie |
|---|---|---:|---|---|
| 1 | `emit.rs` `schreibwort` `_ => "gabbro_setz_le64"` | **148** | nur `(8, false)` | tragender Standardzweig |
| 2 | `emit.rs` `breite_von` `_ => 8` | **146** | nur `U64` | tragender Standardzweig — **die Wurzel** |
| 3 | `emit.rs` `lesewort` `_ => "gabbro_le64"` | **107** | nur `(8, false)` | tragender Standardzweig |
| 4 | `emit.rs` `T_remove`-Rücksetzung `_ => "0"` | **29** | `Bool`, `Int(u32)`, `Int(u32 in a..b)`, `Pfad`, `Index{optional:false}` | **echter Befund** |
| 5 | `emit.rs` Nutzlast `_ => "nothing"` | **21** | nur `None` | tragender Standardzweig |
| 6 | `zeugnis.rs` `_ => "traverse"` | **20** | `SlotsVon` 12, `ElementeVon` 3, `Threads` 2, `Schlange` 2, `KetteIn` 1 | **echter Befund** |
| 7 | `emit.rs` `intty` `_ => "int64_t"` | **4** | nur `I64` | tragender Standardzweig |
| 8 | `domaene.rs` Kantentyp `_ => ""` | **2** | nur `Wahrheit` | tragender Standardzweig |
| 9 | `fremdverengung.rs` `zeichen` `_ => "?"` | **0** | — | tote Verteidigung |
| 10 | `aufrufgraph.rs` `held_aus_expr` `_ => "…"` | **0** | — | tote Verteidigung |
| 11 | `zeremonie.rs` `regel_fuer_herkunft` `_ => "A3"` | **0** | — | tote Verteidigung |
| 12 | `m1.rs` `zeichen` `_ => "?"` | **0** | — | tote Verteidigung |

**Acht feuern, vier schweigen.** Die drei Kategorien der vorigen Messung bestätigen sich, und
die mittlere ist die größte: **sechs der acht feuernden fangen genau einen Konstruktor**, und
zwar den beabsichtigten Normalfall. Sie sind kein Fehler *heute* — sie sind die Stelle, an der
der **nächste** Sprachfall still verschwindet.

## Die zwei Korrekturen an der Buchung

### `breite_von` feuert 146×, gebucht war 0

`e8a6752` buchte für `breite_von` **0 Treffer** und schloss daraus, der Zweig decke
`{U64, I64}` und sei damit „richtig beantwortet". **Die Zahl ist falsch, der Schluss war
richtig** — der Zweig deckt genau `{U64, I64}`, und `U64` ist im Korpus der häufigste
Ganzzahltyp überhaupt.

Der Unterschied zu `intty` (4 Treffer, nur `I64`) erklärt die Zahl vollständig:
`intty` **zählt `U64` auf**, `breite_von` nicht. *Zwei Verteiler über demselben Enum, und der
eine hat einen Fall mehr benannt als der andere.*

> **Warum es zählt:** dieselbe Stelle wurde als *schweigend* gebucht wie zuvor `emit.rs:3488`
> unter `panic!`. Ein Zweig, den man für tot hält, wird nicht gestrichen — und dieser ist der,
> unter dem alle vier Hardwarepunkte liegen.

### `domaene.rs` feuert 2×, gebucht war 8

Siehe oben: vier Befehle, ein Pass. Kein Befund, ein Messgerätefehler.

## Was die Messung NICHT sagt

* **Sie misst den Korpus, nicht die Sprache.** Ein Zweig mit 0 Treffern ist nicht unerreichbar —
  er ist von *diesen* 499 Dateien nicht erreicht. `fremdverengung.rs` und `m1.rs` fangen
  Operatoren, die die Grammatik kennt; ob eine schreibbare Quelle sie erreicht, ist eine
  zweite Frage und hier nicht gestellt.
* **Sie misst das Feuern, nicht die Richtigkeit.** `schreibwort (8,false)` feuert 148× und ist
  jedes Mal richtig. Die Gefahr steht nicht im Treffer, sondern im **nächsten** Konstruktor.

---

# Was gestrichen wurde

## Die Wurzel: eine Tafel statt zweier Verteiler

`intty` und `breite_von` waren **zwei Aufzählungen über demselben Enum mit verschiedener
Länge** — sieben Worte gegen sechs, und beide mit einem `_`, der den Rest verschluckte.
Jetzt lesen beide **eine** Tafel:

```rust
fn ganzzahlwort(k: Kw) -> Option<(&'static str, u32)>   // Name in C, Breite in Byte
```

`intty` und `breite_von` geben `Option`; `breite_oder_absage`/`intty_oder_absage` machen
daraus **`C001` an der Spanne des Typs**. Kein Rufer setzt einen Vorgabewert ein.

**Warum die Null hinter der Absage ungefährlich ist:** `command_emit` schreibt **kein C**,
wenn nach der Emission ein Fehler steht. Dieselbe Form benutzt `zahltext` seit jeher für eine
Tabellenlänge, die es nicht lesen kann.

## `lesewort` / `schreibwort`: die vierte Breite steht jetzt da

`(8, false)` war der `_`-Zweig; beide zählen ihn jetzt auf und geben `Option`.
`wortpaar_oder_absage` sagt bei Namen ab statt das nächstbeste Wort zu nehmen.

## Zwei Stellen derselben Klasse, die in der Liste der zwölf FEHLTEN

| Stelle | was sie tat | jetzt |
|---|---|---|
| `umgebung.rs::breite_von` `_ => (64, false)` | jedes unbekannte Wort **vorzeichenlos, 64 Bit** | `Option`; `max`/`min` fällt aus, `intbereich` nimmt den **weitesten** Bereich |
| `emit.rs::ctyp` `if f32 { float } else { double }` | ein drittes Gleitkommawort still `double` | beide Worte einzeln, sonst `None` → Absage des Rufers |

Die erste ist die **schärfere** der beiden Fehlantworten: ein vorzeichenbehaftetes Wort
bekäme einen Bereich ohne seine negative Hälfte, und M1 rechnete über Werten, die es nie
annimmt. *Ein `else` ist derselbe Wildcard mit anderer Schreibweise.*

## Die Absage ist heute unerreichbar, und eine Probe sagt warum

`emit.rs::breitentafel` — vier Proben, alle über `kw::ALLE` und `ist_intty`, also über
**denselben** Listen, die Lexer und Pässe lesen:

| Probe | Aussage |
|---|---|
| `jedes_ganzzahlwort_hat_eine_breite` | `ist_intty` und die Tafel decken einander **in beide Richtungen** |
| `die_acht_worte_stehen_einzeln` | Name **und** Breite je Wort — ein Prädikat sagt nichts über Breiten |
| `erzeuger_und_pruefer_sagen_dieselbe_breite` | `emit`-Tafel gegen `umgebung`-Tafel (`W7`: zwei Register über einer Sache) |
| `jede_breite_hat_ein_lese_und_ein_schreibwort` | die `C001` in `wortpaar_oder_absage` ist aus keinem legalen Programm erreichbar |

> **Das ist der eigentliche Ertrag.** Ein neunter Ganzzahltyp ist ab jetzt eine **rote Probe**
> und kein stilles `volatile uint64_t *` auf einem Geräteregister.

## Die Gegenrichtung, byteweise

499 Korpusdateien × drei Befehle, `md5` über den ganzen Mitschnitt:

| | vorher | nachher |
|---|---|---|
| `pruefe` | `fbc70c78b2b8cdbb6b816f259a027d5d` | **gleich** |
| `emit` | `34eb26ede4aa86fdc80ca0ceb195f92b` | **gleich** |
| `zeugnis` | `686a1ef576ec08a79642e0fe35fbc493` | **gleich** |

*Kippt eine Datei, war die Zuordnung geraten.* Keine kippte.

---

# Die übrigen sechs, und zwei Befunde dabei

| Stelle | vorher | jetzt |
|---|---|---|
| `emit.rs` Nutzlast | `_ => "nothing"` | `Some(Nichts(_))` und `None` **einzeln** — dasselbe Wort, zwei Gründe |
| `domaene.rs` Kantentyp | `_ => ""` + `strip_prefix` | die **sechzehn** anderen `Typ`-Varianten aufgezählt |
| `fremdverengung.rs` `zeichen` | `_ => "?"` (13 von 18) | alle achtzehn |
| `m1.rs` `op_zeichen` | `_ => "?"` (2 von 18) | alle achtzehn |
| `aufrufgraph.rs` `Held(…)` | `_ => "…"` als **Sperrname** | kein Name statt eines erfundenen |
| `zeremonie.rs` `regel_fuer_herkunft` | `_ => "A3"` | Funktion **gestrichen**, die Regel kommt aus `typ_der_rechten` |

## Zwei davon sind mehr als Kosmetik

### `zeremonie.rs` — zwei Register über einer Sache, und sie liefen schon auseinander

`regel_fuer_herkunft` traf **dieselbe Fallunterscheidung ein zweites Mal** wie
`typ_der_rechten` — und die beiden waren nicht deckungsgleich:

```gabbro
let x : T = (f());
```

`typ_der_rechten` löst die Klammer auf und findet die Signatur von `f` → **`A1`**.
`regel_fuer_herkunft` sieht die Klammer, fällt in `_` → **`A3`**, *„gleich dem deklarierten
Typ eines Namens im Geltungsbereich"*. **Ein Nachweis, der auf eine Deklaration zeigt, die
er nicht gelesen hat.**

Der Zweig feuerte über 499 Dateien nie; die Klammerform ist trotzdem heute schreibbar.
`typ_der_rechten` gibt jetzt `(Typ, Nachweis, Regel)` zurück — **eine** Stelle entscheidet
beides, und die Klammer erbt die Regel ihres Inhalts. `W7` aufgelöst statt bewacht.

### `aufrufgraph.rs` — ein erfundener Sperrname

`Held(<kein Ort>)` bekam den Namen `…`. In beiden Lesern (`geteilt.rs`) ist so ein Name
inert, weil er keiner deklarierten Sperre gleicht — **aber inert ist nicht abwesend**: er
stand im Satz der gehaltenen Sperren, und der nächste Leser, der nach Anzahl statt nach Namen
vergleicht, hätte ihn mitgelesen. Jetzt entsteht kein Name. *Weniger gehaltene Sperren heißt
mehr Absagen, nie weniger — die konservative Richtung.*

## Drei Operatortafeln, eine Probe

`opsruf::zeichen` war vollständig, `fremdverengung::zeichen` fing **13 von 18**,
`m1::op_zeichen` **2 von 18** — beide mit `_ => "?"`. `M136` hatte genau daran schon einmal
`x | y ? z` für `x | y == z` gedruckt: *eine Absage, die die Zeile nicht zitieren kann, um
die es geht.*

Alle drei zählen jetzt achtzehn auf, und zwei Proben halten sie zusammen
(`opsruf::operatortafeln`, `m1::operatortafel`). **Drei Register über einer Sache
zusammenzulegen ist ein größerer Zug als diese Bahn trägt; sie auf dieselbe Antwort zu
verpflichten nicht.**

## Was NICHT gestrichen wurde, und warum

`typ_der_rechten` behält `_ => None`, `held_aus_pred` behält `_ => {}`. **Der Unterschied ist
die Richtung des Fehlers:**

* Ein `_`, der einen **plausiblen Wert** liefert (`8`, `"int64_t"`, `"A3"`, `"…"`), macht aus
  einem unbekannten Fall einen beantworteten. *Das ist das stille Byte.*
* Ein `_ => None` liefert **nichts** und schiebt die Entscheidung an den Rufer, der absagt
  oder nach `T8` fällt. *Das ist der ehrliche Ausgang, den dieser Ordner an vielen Stellen
  ausdrücklich so schreibt.*

Über `ExprArt` (30+ Varianten) erschöpfend aufzuzählen, was ohnehin `None` heißt, kostet
Zeilen und kauft nichts — **die Absicherung ist dort der Rufer, nicht die Aufzählung.**
*Das ist ein Urteil und keine Messung, und es steht deshalb als Urteil da.*

---

# Die Ausnahme: `zeugnis.rs`, und die Antwort folgte aus der Messung

Die zwölf sind gestrichen. Elf davon änderten **nichts** am Korpus — dieser eine sollte etwas
ändern, und das ist der Punkt.

## Der Befund, reproduziert

`messung/proben/probe-zeugnis-injektiv-{a,b}.gab`, Unterschied **eine Zeile**
(`threads` gegen `queue r`), beide `0 errors, 0 hints`. Die Zeugnisse:

```
--- a          == Translation certificate: …-a.gab ==
+++ b          == Translation certificate: …-b.gab ==
```

**Der Dateiname war der einzige Unterschied.** Ohne die Kopfzeile: md5 beider Rümpfe
`d0ff59cac7aa208dae5c964754339cfa`.

> Ein Etikett ist kein Beleg. *Ein Zeugnis, das zwei verschiedene Programme belegt, belegt
> keines von beiden* — und diese Eigenschaft hängt **nicht** daran, ob der Erzeuger richtig
> arbeitet. Genau darum wäre sie die Absicherung gegen Erzeugerfehler.

## Und die Antwort war nicht „neun Etiketten"

Aus der Messung folgte mehr als die Aufzählung: **die neun Domänen ruhen auf verschiedenen
Schranken, und drei ruhen auf gar keiner.**

| Domäne | worauf die Schranke ruht |
|---|---|
| `slots of` | `count N` der Tabelle |
| `elems of` | die **Länge im Typ** (`[u32; 8]`) — sonst die Tabellenkapazität |
| `queue` | die Länge des **einzigen** Feldarrays; zwei Arrays → keine Schranke, `K003` |
| `mappings of` | `Knotenlänge ^ levels` aus der `walk`-Deklaration |
| `descendants of` | die Baumkanten, Postordnung — Terminierung ist eine **Hypothese** der Tabelle |
| `ancestors of` | die `parent`-Kette; kein Zyklus, und das ist dieselbe Hypothese |
| **`chain(…) in`** | **keine** — die Kette hat ein ENDE (`option index into T`), das ist keine LÄNGE |
| **`fields of`** | **keine** — endlich viele, aber keine Zahl in der Deklaration |
| **`threads`** | **keine** — wie viele es gibt, ist eine Aussage über die MASCHINE |

Die letzten drei standen in `domaene.rs::domaenenschranke` auf einem `_ => return None`.
Ehrlich, aber **unsichtbar**: nichts in der Datei sagte, um welche Domänen es geht, und das
Zeugnis deckte alle fünf Nichtbaumformen mit einem Wort. Beide sind jetzt aufgezählt.

## Die Probe MISST, sie behauptet nicht

`crates/gabbro-check/tests/zeugnis_injektiv.rs`, vier Proben:

| Probe | was sie misst |
|---|---|
| `das_gemessene_paar_hat_verschiedene_zeugnisse` | das Paar oben, **unter demselben Dateinamen gerendert** |
| `zwei_gleiche_programme_geben_gleiche_zeugnisse` | die Gegenrichtung — sonst wäre ein Zeitstempel „injektiv" |
| `alle_neun_domaenen_geben_verschiedene_zeugnisse` | die übrigen **fünfunddreißig** Paare |
| `jeder_domaenenausweis_steht_in_der_einordnung` | kein Ausweis fällt auf `UNZUGEORDNET` |

**Der Dateiname wird weggenommen.** Zwei Zeugnisse, die sich nur im Kopf unterscheiden, sind
nicht verschieden — sie tragen verschiedene Etiketten an derselben Aussage.

*Und die Probe wurde falsifiziert, bevor sie gebucht wurde* (R11): `KetteIn` versuchsweise
auf `traverse (slots of)` gezogen → `alle_neun_domaenen_geben_verschiedene_zeugnisse`
**FAILED**, die übrigen drei grün. Danach zurückgestellt und wieder grün.

## Die Gegenrichtung

| | vorher | nachher |
|---|---|---|
| `pruefe` | `fbc70c78b2b8cdbb6b816f259a027d5d` | **gleich** |
| `emit` | `062702775e2a6942c93927895224881e` | **gleich** |
| `zeugnis` | `686a1ef576ec08a79642e0fe35fbc493` | **`c051feaebb8c6d6677decf12452228ce` — geändert, und das ist der Zweck** |

> **Der `emit`-Wert oben ist nicht der aus Schritt 2** (`34eb26e…`). Grund: die zwei
> Probendateien haben einen längeren Kommentarkopf bekommen, und `emit` druckt Zeilennummern.
> *Nachgemessen statt behauptet:* der Baum von `59a8028` mit den NEUEN Probendateien liefert
> `062702775e…` — dieselbe Zahl. Der Unterschied ist der Kopf, nicht der Prüfer.

Der `zeugnis`-Unterschied ist **ausschließlich** in den Traversierungszeilen und den daraus
folgenden Schablonenzahlen: 9 × `traverse` und 8 × `traverse (Baum)` werden zu
`slots of` 6, `descendants of` 6, `ancestors of` 4, `elems of` 3, `threads` 2, `queue` 2,
`chain … in` 1 (plus die Mehrfachzählungen). *Wo eine Datei zwei verschiedene Domänen
durchläuft, zählt das Zeugnis jetzt zwei Schablonen statt einer — genau der Fall, den der
eine Ausweis verschwieg.*

---

# Der zweite echte Befund: `T_remove` setzt jetzt ab, statt zu raten

Der `_ => "0"` in `emit.rs` fing **29** Feldarten. Der Preis stand seit `e8a6752` als
Reproduzent im Baum und wurde in jenem Lauf ausdrücklich **nicht** geheilt.

## Was `0` in einem geräumten Slot anrichtet

```c
static void Verz_remove(Verz *t, uint32_t s) {
    t->slots[s].benutzt = 0;
    t->slots[s].stufe   = 0;   /* `u32 in 1 .. 9`   -- AUSSERHALB des eigenen Bereichs */
    t->slots[s].nachbar = 0;   /* `index into Verz` -- ein GÜLTIGER Index              */
}
```

Zwei verschiedene Fehler aus einer Zeile — und der zweite ist der unangenehmere: `0` liegt
**im** Typ und ist trotzdem falsch. Ein nicht-optionaler Index hat kein `None`; der geräumte
Slot behauptet danach eine Kante.

## Abgeleitet statt geraten

| Feldart | Rücksetzwert |
|---|---|
| `option index into T` | `T_NONE` (`beweise/Option_Sonderwert.thy`) |
| `bool` | `0` |
| Ganzzahl ohne Bereich, `wrapping` | `0` |
| Ganzzahl mit Bereich, der die Null enthält | `0` |
| Ganzzahl mit Bereich **ohne** die Null | **`C001`** |
| `index into T` (nicht optional) | **`C001`** |
| Neutyp | folgt dem Trägertyp, höchstens 16 Ebenen |
| Zeiger, Gleitkomma, Feld, Verbund, Fn-Zeiger, `never`, tagged | **`C001`** |

**Und die Absage bricht nicht beim ersten Feld ab.** Eine Tabelle mit zwei nicht ableitbaren
Feldern meldet zwei — *sonst hätte sie dieselbe Krankheit wie die Messung von heute früh.*

## Drei Proben, und der Unterschied ist EIN Zeichen

| Datei | was sie hält |
|---|---|
| `beispiele/gift/441-ruecksetzung-verlaesst-den-bereich.gab` | `u32 in 1 .. 9` → `C001` |
| `beispiele/gift/442-ruecksetzung-erfindet-eine-kante.gab` | `index into Verz` → `C001` |
| `messung/proben/probe-ruecksetzung-abgeleitet.gab` | sieben Feldarten, die **weiter** absenken |

Die Gegenprobe schreibt `u32 in 0 .. 9` statt `1 .. 9` und `option index into Verz` statt
`index into Verz`. *Damit misst das Paar die Regel und nicht die Datei.*

## Die Gegenrichtung: GENAU EINE Datei kippt

| | vorher | nachher |
|---|---|---|
| `pruefe` | `fbc70c78b2b8cdbb6b816f259a027d5d` | **gleich** |
| `emit` | `062702775e2a6942c93927895224881e` | `1173ca54fd41a407dbd7126ee799453e` |
| `zeugnis` | `c051feaebb8c6d6677decf12452228ce` | **gleich** |

*Je Datei nachgerechnet* (nicht nur die Summe): **von 499 Korpusdateien ändert sich genau
eine** — `messung/proben/probe-wildcard-ruecksetzung.gab`, der Reproduzent. Sie schrieb C
mit zwei falschen Werten und sagt jetzt `C001`.

## Und ein Nebenertrag: vier Blicke auf eine Karte wurden einer

Die Ableitung muss einen Neutyp auf seinen Träger auflösen — derselbe Blick, den
`vorzeichen` und `ctyp` schon zweimal taten. Statt eines vierten steht jetzt **`traegertyp`**
da, und `zaehle-karten.py` fällt von **40 auf 38** (unqualifiziert 36 → 34).

> *Ein Leser ist eine Stelle, die man heilen kann; vier sind vier, die man vergisst.*
