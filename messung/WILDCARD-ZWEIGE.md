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
