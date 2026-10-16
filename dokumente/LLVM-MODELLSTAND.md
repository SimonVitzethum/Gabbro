# LLVM backend: standing against the Lean model

*Measured 2026-10-15, backend `crates/gabbro-check/src/llvm.rs`. The unit is not the
example corpus but the Lean language model (`grammatik/Grammatik/Kern/Syntax/`):
every `Ty`, `Expr`, `Stmt`/`Block`/`Endblock` constructor and every `Deklaration`
field is booked as LOWERED, REFUSED (with code), ERASED (proof-only, correctly
absent from bytes) or OPEN. Corpus numbers are witnesses, not the measure.*

Method: `cargo test -p gabbro-check --test llvm` (14 tests), full workspace suite,
`opt -O3` over every checker-green corpus file on both targets (validity gate),
`instrumente/baue-llvm.sh` end to end (static, no INTERP/NEEDED, x86_64/aarch64
agreement). A constructor counts LOWERED only if its IR passes `opt` and, where
executed, runs.

## 1. Types (`Typen.lean`, `Ty`)

| Lean | Backend | Form |
|---|---|---|
| `int lo hi` | LOWERED | `i8`–`i64` by width; proven ranges narrow scalar cells (`u32` `<256` lives as `i8`); aggregates never narrow (one layout) |
| `bool` | LOWERED | `i1` (atomics: `i8` cell, converts at the edge) |
| `opt n` | LOWERED | `%gabopt` = `{i32 tag, [8 x i8]}` |
| `sum cs` | LOWERED | `{i32 tag, [P x i8]}`, `P` = largest case |
| `grund n` | LOWERED | `i32` (case values from the declaration) |
| `never` | LOWERED | `void` + `unreachable` |
| `fl lo hi` | LOWERED | `float`/`double` (finite by construction; the exporter builds no `Ty.fl` — direct surface lowering) |
| `fnptr sig` | LOWERED | `ptr` (producer `&f`, calls through the type's contract) |
| `ptr t rw` | LOWERED | `ptr` (device spaces: `volatile` accesses) |

## 2. Expressions (`Syntax.lean`, `Expr`)

LOWERED: `lit`, `wahr`, `falsch`, `var`, `glob`, `slot`, `durch`, `ptrOf`
(table address), `fnref`, `weiter` (widening), `add`, `sub`, `neg`, `mul`,
`div`, `rem`, `sdiv`, `srem`, `band`, `bor`, `bxor`, `shl`, `shr`, `lt`, `le`,
`eq`, `fllt`, `flle`, `und`, `oder` (short-circuit), `nicht`, `none`, `some`,
`fall` (incl. bare case as value and as static init), `grund`, and counting
`count k in slots/elems of X : p` (loop with a predicate).
`leseBytes`/`schreibBytes`: no own form — byte buffers lower through pointer
indexing plus arithmetic (e.g. `u16_gross`), which is the same bytes.

- `altGlob`/`altSlot`: assumptions only — correctly absent (never materialized).
- `istSome`: model-only, no surface spelling — nothing to lower.
- `forallSlots`/`existsSlots`/`reaches`: specification — erased.

## 3. Statements (`Syntax.lean`, `Stmt`/`Block`/`Endblock`)

LOWERED: `assignSlot`, `assignDurch`, `assignGlob`, `assignVar`, `ite`,
`onOption`, `onTag`, `onGrund`, `call`, `callInd`, `locks` (exclusive),
`breaking` (body runs), `traverse` (`slots of`, `elems of`, `queue`,
`ancestors of`, `descendants of`), `retry`, `forever`, `axiomCall`
(plain and errno gates), `ret`, `retGrund`, `leave`, `next` (by name — binder
or loop label), `bind`/`bindCall`/`bindCallInd`/`bindCallElse`/`bindAxiom`/
`bindAxiomElse`, `awaits`, `exchange` (both forms, bounded), `narrow` (int,
float range, `finite`, constant OR runtime bounds), `gleit`/`gleitLit`/
`gleitVon`, all `Endblock` forms.

- `uebergang` (state fields): plain store — the transition discipline is the
  checker's; the bytes are a store either way.
- `advances`/`retires`, `pruefung`: proof bookkeeping — correctly absent.
  (`pruefung` and byte views are also never built by the exporter.)
- `publish` with empty payload: release store. **With payload: REFUSED
  (`Y103`) — the goal theorem does not cover the hand-off (OFFEN O25).**
- `regSchreib`/`transition` (model `Reg`): REFUSED — the exporter builds no
  `Reg`; surface devices lower through `volatile` (`ptr<mmio>`/constructors).
  A full device state model is open work.
- Shared acquisition: REFUSED (`Y103`) — serializes nothing silently.

## 4. Declarations (`Syntax.lean`, `Deklaration`)

LOWERED: `Tab`/`count`/`Feld`/`typ`, `tabNr`, `Glob`/`gtyp` (+ atomics with
orderings, incl. arrays), `Lock`/`rang`, `Fn`/`sig`, `Inv` (erased),
`Ax`/`aparams`/`aerg`, `agruende` (errno decoding), `Annahme`/`a10`
(erased), `geist` (erased), guards/ranks/costs (erased, checked before).
Devices (`device … reg … fields …`) lower as `volatile` accesses at declared
offsets with bit extraction/insertion; `transition` lowers as read-modify-write
per step. `accumulates` lowers as one cell (the per-core split is a
proof obligation, not a byte). `format` lowers as a PACKED struct (`<{ … }>`).
Generated table operations (`ops insert, remove, relabel`) lower as inlined
mutations at the call site: `insert` hangs the parent (`Some p`) and sets the
occupied field, `remove` resets every field, `relabel` rewrites the parent —
the C emitter's semantics, byte for byte.

- `maskiert` (IRQ-masking locks): REFUSED (`Y102`) — needs the interrupt model.
- `Reg`/`rtyp`/`rklasse`/`spiegel`/`rzusage`/`rtraeger`: no lowering — see §3.
- `erlaubt` (state machine), `nutzlast` (non-empty), `braucht`, invariants:
  checker-side — correctly absent.

## Arenen: Reserve ist Adressraum, Belegung ist RAM (`ArenaDyn.lean`)

Das Modell (`ArenaDyn.lean`) unterscheidet Decke `M` (reserviert, nie implizit
berührt), Committed-Präfix `c` (`hi <= c <= M`, monoton) und Gebrauchtes; `grow`
über `M` ist Abweisung, darunter darf die Laufzeit scheitern (OOM ist real —
das `else` ist des Programms); `reset` lässt Commit stehen. Der Erzeuger folgt
demselben: drei Wörter (`basis`, `belegt`, `bereit`), Reserve einmalig per
`mmap(PROT_NONE)` (Adressraum ohne RAM), Commit in 1-MiB-Schritten per
`mprotect` bei Bedarf, jeder Fehlschlag in den `voll`-Zweig. Gemessen: 1 GiB
Decke → 24 Byte BSS, `rc=42` korrekt (seit TODO §1-B vier Wörter mit `frei`:
32 Byte, weiter decken-unabhängig). Die 1-MiB-Schritte überragen den Bedarf —
unbeobachtbar (keine Introspektion), also verfeinerungstreu. Seit TODO §1-B
rechnet der Schritt sauber in Bytes (Bedarf auf 1 MiB aufgerundet, an der
Decke gekappt): Decken unter 1 MiB committen ihren Rest in einem Schritt
(gemessen: `capacity 0 .. 4` läuft, `rc=100` mit Freilisten-Wiederverwendung).

## Slot-Freigabe (`free A[i];`, TODO §1-B)

Vier Wörter je Arena (`basis`, `belegt`, `bereit`, `frei` = -1 für leer):
`free` schreibt den alten Kopf als `i64`-Glied in den Slot und rückt den Kopf
vor (intrusiv, null Overhead — Elemente unter 8 Bytes tragen kein Glied,
`Y103`); der nächste `alloc` nimmt von der Liste (kein Commit, keine Abtastung)
oder vom Hochwasser; `reset` leert die Liste neben dem Zähler. Gemessen:
Beispiel `1161` läuft beidseitig (`rc=100`, Slot wiederverwendet), BSS weiter
konstant (32 Byte für 4 Wörter, decken-unabhängig; `frei` = -1 steht in DATA).
Lean: `FreiZustand` mit vier bewiesenen Erhaltungssätzen (`ArenaDyn.lean`);
der G-Exporteur verweigert noch (`LG005`, O14s dritte Form).

## Unbegrenzte Halde mit Abtastung (`pb P blw B`)

Die Klausel schaltet die unbegrenzte Form ein (SYNTAX.md §9.1, TODO §1): keine
`max`-Decke, die Decke ist der Zählerraum (`u32::MAX`); die Reserve bleibt
Adressraum ohne RAM, der Commit läuft je 1 MiB bei Bedarf. VOR jedem Commit
fragt der Erzeuger die nullstellige Frage `P` (Tor oder Funktion) nach freien
Bytes — unter der Nutzer-Schwelle `B` (z.B. `blw 1048576`, 1 MiB) läuft der
`voll`/`else`-Zweig. Ein Ruf je MiB, null im Schnellpfad; freistehend misst `P`
selbst. Prüfer `N584`/`N585` (Sätze in `saetze.rs`), drittes sanktioniertes
`inttoptr` (Laufzeit-Basis). Gemessen: Beispiel `1160` läuft beidseitig
(`rc=42`), OOM-Zweig bei 100 Bytes frei korrekt genommen, 0 Byte BSS.

## Rekursion ohne Stapel (Endrekursion als Schleife)

Rekursive Rufe liefen als echte Maschinenrufe — Tiefe 512 passt, Tiefe 200.000
nicht. Jetzt senkt der Erzeuger **endständige Rekursion** (solo und wechselseitig
über den Rufgraphen, Tarjan, iterativ) als Schleife: ein Aufruf `return f(…)` wird
Zustand + Sprung statt Rahmen. Gemessen: `ab(200000)` läuft mit **512 KB Stapel**
in 0,000 s (`rc=0`, korrekt). Bedingungen: alle Zyklus-Rufe endständig, einheitliche
Antwort, kein Fehlerkanal — sonst echte Rufe (Status quo, dokumentiert statt
verweigert). Nicht-endständige Rekursion nutzt weiter den Maschinenstapel
(begrenzt durch `decreases`, endlich aber endlich).

## 5. Open (model-measurable, with reason)

| Item | Reason | Sites |
|---|---|---|
| IRQ-masking locks | interrupt model (which bit, nesting) | `01`, gifts |
| Model `Reg`/`regLies` | the exporter builds no `Reg`; surface devices covered via `volatile`/`transition` |
| Publish with payload | OFFEN O25, uncovered by the goal | 11 |
| Shared locks | own primitive unproved | 3 (+1 correct probe) |
| Stack gates + `child` | `clone` trampoline | 4 (`kind-*`) |
| Entries (`unterbricht`) | hardware dispatch | 12 |
| `start` | real threads since 2026-10-16 (step 1): raw `clone` (`CLONE_THREAD`), own 8 MiB stack per root, futex join over global ready-words — measured 10x `rc=64` on x86_64, 5x under qemu-aarch64, deterministic under the ticket lock | the goal's concurrency legs are unchanged (the checker already ruled for every schedule); the per-access target→W/GX bridge stays validation work (§5) |
| Library calls (`@lib#f`) | needs the library/payload model | 2 (`106`, `107`) |
| `reset X at i count n` | the page give-back is a template + binding; the zero-fill alone is trivial, the whole statement is not | 2 (`175`) |
| `static ptr = array-name` decay | refused by the C emitter too (`C001`) — an open remainder, not a lowering gap | 1 (`38`) |

`start` is the sharpest edge: it lowers and runs, but sequentially. Every other
row is refused by name or genuinely lowered.

## 6. Invariant optimization (measured, not claimed)

**What the checker's facts turn into.** Measured over the 134 clean corpus units
(x86_64): **131 `llvm.assume`, 192 `!range`, 1182 `!tbaa` (of them 182
struct-path tags), 2 `noalias`, 2 `dereferenceable`.**

| Fact | Becomes | Evidence |
|---|---|---|
| a passed `narrow` | `llvm.assume` + the checked branch | — |
| `requires`/`ensures` (comparison) | `llvm.assume` at entry / before `ret` | 123 `requires`, 63 `ensures`; 5 quantified |
| loop `invariant` | `llvm.assume` at the loop head | 19 lines |
| declared integer range | a NARROWER CELL (`u32 in 0 .. 200` → `alloca i8`) | `%a3 = alloca i8` |
| declared integer range | `!range` on loads from it | 192 tags |
| **`forall s in slots of T : T.slots[s].f <= K`** | **`!range [0, K+1)` on every load of `T.slots[*].f`** | probe: `!{i32 0, i32 5}` from `<= 4` |
| scalar type | flat TBAA node under `omnipotent char` | 1182 tags |
| named record / table slot | **struct-path TBAA** `!{!struct, !member, i64 off}` | 182 tags |
| `own` pointer parameter | `noalias` | 2 |
| `requires N <= lenof(p)` | `dereferenceable(N)` | 2 |
| `requires aligned(p, N)` | `align N` | probe-verified |

**The quantified-invariant rule, in full.** A table invariant of the shape
`forall s in slots of T : T.slots[s].f <op> K` (K a literal or a folded
constant, `Self` or the table name) is read as a *range fact about the field*:
the load of `T.slots[*].f` carries `!range` from it, intersected with the
declared range. Both `P => Q` and `P && Q` bodies are searched, and the field
may stand on either side of the comparison (the direction flips). This is the
part of "invariant optimization" that the model asks for: the invariant is a
statement about **every slot**, so it is fuel for **every access**, not only for
the loop head. Corpus note: the 19 corpus invariants are almost all equality,
`reaches` or disjunction shaped, so the corpus exercises the rule little — the
rule is built and probe-verified.

**What is deliberately NOT there.** Each row is a decision with a reason:

- `!range` on stores — LLVM forbids it there (LangRef: loads, calls, invokes).
  The store-side carrier is the NARROWED CELL: a proven `< 256` value lives in
  an `i8`, so the store's type already states the range.
- Aggregates never narrow — one layout per named type, so no conversion at any
  call or return. This is a choice, not a limit: narrowing aggregate fields
  consistently would work, but a struct crossing an `extern`/gate boundary
  would then need conversion, and the boundary rule is not built. The gain
  stands in scalar cells.
- `i8`/`i1` and aggregates carry no TBAA node — bytes may overlay anything, and
  a byte view of a struct (`leseBytes`) is exactly that.
- Struct-path tags are emitted only where LLVM's verifier accepts the exact
  `(member, offset)` pair; where the access is an ELEMENT inside an aggregate
  field, the access falls back to the flat scalar node rather than emitting a
  tag the verifier would reject. (Measured: LLVM 23 rejects a struct tag whose
  offset is not a listed member.)
- `noalias` only where `own` is declared — never guessed.
- Quantified clauses of other shapes (`reaches`, disjunction, equality chains)
  do not become optimizer facts: they would need loop-level reasoning.
- No `llvm.loop` metadata. `opt -O3` already runs the loop vectorizer and
  unroller on its own analysis; a blind `vectorize.enable` hint can force an
  illegal or slower transform. Deliberately left to the pipeline.
- No `!prof` branch weights — there is no profile to state.

**The pipeline.** `opt -O3` (middle end) + `llc -O3` (codegen); `llc` alone does
not run the middle end (measured slower than `-O0`). `summe.gab`: **10 ms at
`-O0` → 2 ms at `-O3`** (an earlier run measured 20.3 → 3.3 ms; both runs,
rc=25, x86_64 native), identical output on x86_64 and aarch64. These are
Gabbro-vs-Gabbro numbers, not against GCC `-O3` — the `ARM-PLAN.md` 80 %/110 %
targets are still unmeasured.

## 7. Isabelle-Beweise (`grammatik/Beweise/*.thy`): was sie beweisen, wo es im Backend steht

15 Theorien, 188K, 3512 Zeilen. Jede beweist eine Eigenschaft, die der C-Erzeuger
braucht — und jede steht im LLVM-Erzeuger an derselben Stelle, weil die
Absenkungsregeln dieselben sind. Wächterverdrahtung: `pruefe-beweise.sh`
(Sitzung), `zaehle-theorien.py` (KENNZAHLEN), `pruefe-waechter.py`. 18 Zitate
in `emit.rs`. Darum bleiben sie: Löschen bräche Wächter, ohne ein Byte zu sparen.

| Theorie (Hauptsatz) | Was bewiesen ist | LLVM-Backend |
|---|---|---|
| `Table_Ops_Erhaltung` (`einfuegen_erhaelt`, `blatt_loeschen_erhaelt`) | ops erhalten Erreichbarkeit/Blätter | `senke_ops_ruf`: insert hängt ein + setzt belegt, remove setzt alles zurück |
| `Table_Absenkung` (`absenkung_deckt_genau`) | Layout deckt genau die Indizes | benannte Layouts, GEP-Indizes |
| `Table_Indexschranke`, `Table_Zaehlung`, `Table_Induktion` | Indexdisziplin, Zählung, Induktion | prüfer-seitig; Senkung erhält Breiten |
| `Format_Roundtrip` | Schreiben stört getrennte Felder nicht | gepackte Structs, `volatile` |
| `Verbund_Konstruktor` (`deckt_setzt_jedes_genau_einmal`) | Konstruktor setzt jedes Feld genau einmal | `insertvalue`-Kette |
| `Device_Konstruktor` (getrennte Register, Bänke überlappen nicht) | Versätze disjunkt | Versätze aus der Deklaration, `volatile` |
| `Accumulates_Monoid` | Faltung reihenfolgeunabhängig | eine Zelle: max/min/add gelten trivial |
| `Consuming` | Verbrauchsordnung | Nachordnungs-Abstieg |
| `Gruppe_Erhaltung` (`rangordnung_azyklisch`) | Rangordnung | prüfer-seitig (Ränge radiert) |
| `Intervall_Aussen` (Summe in gerechneter Schranke) | M104-Bereiche | Breiten gehalten, `angleiche` |
| `Option_Sonderwert` (`kodiere_injektiv`) | Tag-Kodierung injektiv | `%gabopt` Tag + Bytes |
| `Restrict_Alleinzugriff` | `restrict` gerechtfertigt | `noalias` an `own` |
| `Absenkung_Parametrisch` | Absenkung parametrisch | generische Layouts |
