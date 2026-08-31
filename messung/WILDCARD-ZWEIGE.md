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
