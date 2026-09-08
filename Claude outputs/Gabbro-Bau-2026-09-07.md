# Bau vom 2026-09-07/08: der Lean-Kanal trägt die Klempnerei

**Der ganze Plan, ausführlich und auf Englisch (Baumregel): `programmlogik/PLAN.md`.** Dieser Bericht ist die Kurzfassung.

Ziel: ein Nutzer, der ein Gabbro-Programm formal verifizieren will, beweist **nur seine eigene Logik**. Alles andere — Rufkomposition, Schleifenregeln, Typisierung der Welt, Formen der Antworten, Vorbedingungen an Rufstellen, Rekursion, Kontrollfluss, Fallunterscheidungen an Lesestellen, Arithmetik — trägt das Modell (`programmlogik/Gabbro/Body.lean`), der Erzeuger (`crates/gabbro-check/src/lean.rs`) oder die Automatik (`gabbro_auto`).

## Stand (Korpus `beispiele/` + `messung/`, 189 Einheiten)

| | vorher (Bewertung) | jetzt |
|---|---|---|
| Pflichten im Register | 175 | 175 |
| davon als Lean-Ziel getragen | 14 | **90** |
| Annahmen (Hardware, Fremdcode, Walk) | – | 72, mit Namen in `Assumed ρ` |
| verweigerte Formen | 161 | **13** (`fields of`/`threads`/`mappings of` 9, Verbundwerte als Ergebnis 2, `sizeof`/`lenof` über Puffer 2) |
| erzeugte Sätze (`_meets`/`_keeps`/`unit_closed`) | – | 502, **0 Lean-Fehler** |
| davon von `gabbro_auto` geschlossen | – | **474** |
| als `sorry` an den Menschen | – | **28** (Lauf 23; 195 → 51 → 91* → 28) |

\* Der Anstieg auf 91 war gewollt: die Bereiche von Feldern, Nutzlasten, Lokalen und Antworten kamen erst als Pflicht in die Sätze und dann ins Modell (`Shape.intIn`).

`cargo test --no-fail-fast`: alle Sammlungen grün. `Body.lean` baut ohne `sorry`.

## Was heute dazukam

**Modell (`Body.lean`)**
- Rekursion: `Below e t' t`, `ContractBelow`, `contract_of_duty_rec` — Induktion über `decreases` einmal im Modell; der Nutzer sieht die Selbstzusage unterhalb des Maßes als Hypothese. **Wechselseitige Rekursion**: `Member`, `BelegM`, `ContractBelowM`, `contracts_of_duties_rec` — ein Zyklus beliebiger Länge, eine Induktion über das gemeinsame Maß; `gerade`/`ungerade` schließen und sind verdrahtet.
- `Shape.sum` trägt seine Fälle (`(.sum [("Kurz", true), ("Leer", false)])`): ein `tagged`-Wert der Form ist einer der erklärten Fälle mit der erklärten Nutzlast (`Shape.caseOk`); ein `match` darüber bleibt im Modell nie an einem Fall stecken, den der Typ ausschließt.
- `andBool`/`orBool` statt `binop` für `&&`/`||`: eine wahre Konjunktion zerfällt in zwei (`andBool_true_iff`), auch wenn eine Hälfte symbolisch bleibt.
- Schleifenindex im Bereich: `RunsLoopIn`, `looprule_of_body_in` — ein Durchgang über `slots of T` darf `0 ≤ k < count` annehmen.
- `-> never`: die Zusage ist `False`; was einem solchen Ruf folgt, ist unerreichbar.
- Rufe lesen ihre Antwort über die Projektionen `(ρ f t).1/.2`, nie über ein Paar-`match`.
- `Value.hasShape_*_true`: eine Form wird zum Zeugen.
- Automatik: `gabbro_pipeline` mit echtem Heartbeat-Budget je Schritt (`gabbro_try`; gemessen: `set_option maxHeartbeats … in` innerhalb eines Taktikblocks ändert die Grenze NICHT; ein verschachteltes `by` meldet sein Scheitern als Fehler des Satzes statt es zu werfen — `haveClosed`), `gabbro_cases` (Kontrollfluss-Split über `decide p`, `if`-Bedingungen, boolesche Variablen und Lesungen), `gabbro_calls` (innerste Rufe zuerst, je Instanz abgesichert, Marken je Ziel über Pässe hinweg, `Below` mit `omega`), `gabbro_open`/`gabbro_open_hyps` (Konjunktion/Existenz/Disjunktion/Formfakt/Fallfakt geöffnet, auf Kopien), `gabbro_assumption` (Konjunkt einer Hypothese), `gabbro_shape` (Zeuge einer Weltlesung, auch in Hypothesen), `gabbro_forall` (eine quantifizierte Prämisse, die der Kontext schon hergibt), `gabbro_instantiate` (Invariante am Index im Spiel, auch aus Konjunktionen), `gabbro_split` (verschiedene Felder ohne Fallunterscheidung; Hypothesen als Indexgleichungen), `simp_all`/`omega` in Schlussrunden.

**Erzeuger (`lean.rs`)**
- Verträge vor Pflichten (wechselseitige Rekursion referenziert vorwärts).
- Selbstrekursion verdrahtet (`contract_of_duty_rec`); wechselseitige Rekursion und Rekursion in Schleifen bleiben benannt unverdrahtet.
- Parameterbereiche (`n : u32 in 0 .. TIEFE`) stehen in der Vorbedingung (`shape_int_in`); eine Laufvariable verdeckt den Bereich ihres Namens.
- Statics, `atomic`, `accumulates` in `shapeOf`; Verbundfelder nach Typname (`.field "Text" "len"`), mit Zeugen; opake Neutypen tragen die Form ihres Untertyps (D1 gilt im Prüfer, nicht im Modell).
- Arrays als Pseudotabellen (`Ring.plaetze`, `buf`): Plätze, Zuweisungen, `elems of`, `queue`, `lenof`; ein geschriebener Verbund schreibt seine Arrays.
- Rufe in Ausdrücken werden gehoben (`match f(a)`, `if f(a)`, `let x = f(a)+1`, `g(f(a))`, `return f(a)+1`, Zuweisung) — nicht unter `&&`/`||`.
- Antwortform in jeder Zusage (`∃ x, r = some (.int x)` …, mit Fehlerkanal), `#ret` trägt seine Form durch die Schleife.
- Geräteregister: Lesen/Schreiben ist Gerätezusage (Annahme), keine Verweigerung. `aligned(e, n)` ist `e % n == 0`.
- Öffnungszeilen: die Hypothese selbst als Rewrites (`hall`), negative Literale, `_pre`/`_inv` im simp-Satz.
- Kopf: `maxHeartbeats 11300000` (Summe der Schrittbudgets).

**Am 2026-09-08 dazu** (Modell + Erzeuger): Rufketten (`gabbro_calls` schreibt die Antwort sofort ins Ziel, mit `bindLocal`-/`store`-Lemmata), `Shape.intIn lo hi` (Bereiche in der Welt: `WF_intIn`, `shape_intIn`, `gabbro_wf` mit `omega`), Nutzlastbereiche in `Shape.sum` (`Shape.payloadOk`), `∃ v, r = some v` für Antworten ohne Form (Token, Verbund) + `gabbro_values` (Fallsplit über den Wert), `chase_refl` und die `chase_store_*`-Rahmenlemmata (ein Store neben der Kette lässt sie stehen), `gabbro_divmod`/`gabbro_mul`/`gabbro_bits` (Grenzen von `/`, `%`, `*`, `&`, `^`, `|` für `omega`), `subst_vars`, späte `gabbro_cases`-Runde mit expliziten `decide`-Gleichungen und gespiegelten Ungleichungen, `queue T.slots[i].f`, Elementbereich als Schleifenbereich, Lokale mit Bereich in jeder Invariante.

**Prüfer und Emission**
- `gabbro prove|beweise [--template|--vorlage] [--model|--modell <dir>] <unit.gab>…` (`crates/gabbro-check/src/beweis.rs`): schreibt `programmlogik/Duty/<Unit>.lean`, baut das Modell mit `lake`, kompiliert die Pflichten, hält `programmlogik/Proofs/<Unit>.lean` dagegen. GREEN / OWED (welche Sätze) / RED / SETUP; Exit 0/1/3. `--template` schreibt die Datei, mit der ein Mensch anfängt: die erzeugten Öffnungen, `gabbro_pipeline`, und danach nur noch seine Logik.
- `gabbro emit --proved|--mit-beweis`: kein C für eine Einheit, die noch einen Beweis schuldet — die Absage stützt sich auf dieselbe Messung.
- `instrumente/pruefe-lean-pflichten.sh` ist die baumweite Hülle darum; `pruefe-lean-beweis.sh` zählt `error(` auch im neuen Lean-Format.
- Register: `fahnen.rs`/`erstnamen.rs` kennen die neuen Namen (englisch zuerst).

## Was ein Nutzer jetzt noch beweisen muss

Die `_statement`s, bei denen `gabbro_auto` ein `sorry` lässt — 28 von 502 im Korpus, alle in `PLAN.md` §5.1 als eigene Logik oder eigene Spezifikation eingeordnet. Stichproben (`gabbro_auto?`): Erhalt von `reaches`-Invarianten beim Umhängen (01-tabelle, F01, kapraum), die Verschiedenheit über Ringplätze (56 — die Vorbedingung sagt nicht, dass `i` frisch ist; der Satz ist so nicht beweisbar), Summen über Puffer (udp-echo), eine Zählerinvariante `n <= 8`, die `n+1 <= 8` nicht hergibt (46) — Programmlogik, und in zwei Fällen eine Spezifikation, die der Nutzer nachschärfen muss. Er schreibt sie in `Proofs/<Unit>.lean` hinter `gabbro_pipeline […] using shapeOf`.

## Was bleibt — mit Namen

- Verweigert (13): Quantoren über `fields of`, `threads`, `mappings of`; Verbundwerte als Funktionsergebnis; `sizeof`, `lenof` über Pufferzeiger.
- Nicht verdrahtet: Rekursion innerhalb einer Schleife; zwei Rufer verweigerter Routinen (Proben).
- Annahmen (72, benannt): Geräteversprechen, Walk-Klauseln, fremde `ensures`; `Initially` (Anfangszustand); Aliasfreiheit verschiedener Trägernamen; ein Verbundtyp = ein Objekt des Modells; Prüfer- und Erzeugerkorrektheit (nicht Gegenstand).

## Offen gelassen

- Commit `8a6899b` (2026-09-08) und Folgecommit; `git status` auf tux davor: `lean.rs`, `beweis.rs` (neu), `lib.rs`, `main.rs`, `fahnen.rs`, `erstnamen.rs`, `rechenwerk.rs`, `Body.lean`, `Spec.lean`, `zaehle-lean.py`, `pruefe-lean-beweis.sh`, `pruefe-lean-pflichten.sh` (neu). `programmlogik/_pruefung/` ist Messkram und kann weg; `programmlogik/Duty/`, `Proofs/` entstehen durch `gabbro prove`.
- Das Binärprogramm auf tux (`programmlogik/_pruefung/gabbro`) ist ein hier gebauter Release-Build; der eigene Bau läuft laut CLAUDE.md auf ki-pc-fisch-101.
- `.md`-Dokumente unangetastet.
