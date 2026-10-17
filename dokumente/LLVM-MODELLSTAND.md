# LLVM backend: standing against the Lean model

*Updated 2026-10-17. The denominator is the Lean language model, never
examples. Run `python3 instrumente/pruefe-llvm-modelldeckung.py`.*

The checked register is `dokumente/llvm-modelldeckung.tsv`. It enumerates every
constructor/declaration field in the selected core syntax, signature, program,
arena and G-continuation families directly from their Lean definitions. Missing,
removed or duplicate entries and missing implementation anchors fail the check.
`LOWERED`, `PARTIAL`, `REFUSED`, `ERASED`, `MODEL_ONLY` and `OPEN` are explicit
implementation classifications, not compiler correctness theorems. In particular,
partial source-to-G export stays partial even when a surface form emits LLVM.
The register is authoritative where the older prose tables below simplify a case.

Execution tests are witnesses for lowering rules: the existing LLVM tests plus
`llvm::stackless` and `llvm::memory` execute deep recursion, indirect/mutual calls,
aggregate continuations, small-slot reuse, page reclamation, range reset and
thread groups on both targets at `-O0`/`-O3`. They do not define coverage.

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

The following measurements are the historical reservation/commit snapshot. The
current implementation adds the metadata base and separate free links/counts
described in the next section (five fixed words, 40 bytes).

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

## Slot release and physical page reclamation

Free links are now a separate, lazily touched anonymous metadata region, with
one live-slot counter per approximately 1 MiB payload chunk. This preserves the
`FreiZustand` LIFO semantics for every supported element width, including `u8`.
Freeing the last live slot discards only whole interior pages of that chunk;
neighbouring chunks and all free links survive. `reset` clears counts/list/high
water and returns used payload pages. Metadata is virtual address space, not
up-front physical RAM; touched links cost 8 bytes per freed slot, counters cost
8 bytes per chunk, and the arena has five fixed words including the metadata base.

`madvise(DONTNEED)` retains mappings/access rights and the committed prefix.
There is no revoked-page bitmap: physical residency and virtual commit are distinct.
With pressure sampling, reuse of an empty chunk samples before consuming its free
head; a failed sample takes the existing allocation-failure path. Returning pages
is best effort. Small ranges can retain partial boundary pages.

Lean storage rule: `discard_live` in `ArenaSeiten.lean` preserves live payload and
`discard_preserves_reuse` preserves the exact next logical allocation. The G
exporter's `free`/dynamic-form remainder remains open; this is no binary proof.

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

## Recursion without native stack growth

Every cyclic direct/compatible indirect call component becomes a loop dispatcher
with explicit continuation frames, irrespective of tail position, return type or
error channel. SSA values and address-taken locals remain in stable frames across
suspension. Existing pure tail cycles retain their jump-only fast path. Checked
anonymous chunks grow as needed and are released while unwinding; allocation
failure traps explicitly, rather than falling through `unreachable`. Finite RAM
is still finite: avoiding native stack overflow does not mean constant memory
for non-tail recursion.

`SchablonenStapel` states the storage/resource obligations over the actual G
frames and reuses the existing join contract. It does not certify Rust lowering.
See `LLVM-SPEICHER-STAPEL.md` for the implementation and test boundary.

## 5. Open against model constructs

| Model/surface boundary | Remaining work |
|---|---|
| `Deklaration.maskiert` | IRQ masking and interrupt nesting |
| `Deklaration.Reg`, `Stmt.regSchreib`, `Block.regLies*` | Model-register/export bridge; surface volatile MMIO is separate |
| `Stmt.publish` | Nonempty payload hand-off |
| `Stmt.locks` | Shared acquisition |
| `Deklaration.Ax`, `Block.bindAxiom*` | Stack-carrying/paired/unbound gates and `child` semantics |
| `Programm.unterbricht` | Hardware-dispatched entries; boot/entrust/asm lowering |
| Library call surface | Library resolution and payload model |
| Static pointer decay | Global array-address initializer |
| `ArenaForm` / `DynForm` | Full G exporter/statement bridge remains partial |

`start` now starts all roots before joining, with per-invocation guarded mappings,
atomic completion reads, and stack reclamation after kernel-reported thread exit.
It is a Linux runtime implementation, not a per-access target-to-GX proof.
Static range reset now zeroes the checked interval; declared page-return bindings
can reclaim its whole interior pages. The G-export remainder is unchanged.

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
| `own` pointer parameter; a writable pointer parameter of an internal function whose effects name only its own pointers | `noalias` | 10 |
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
- `noalias` only where the checker holds the WHOLE call (2026-10-17, `A1-OWN-PAPER.md` slice 4):
  an `own` parameter, and a WRITABLE pointer parameter of a function that is not `pub`, is called
  from a body of its unit, has its address nowhere taken, is named by no entry/boot/concurrent
  item, and whose declared `effects` name nothing but its own pointer parameters (`E008` keeps
  that list a superset of its callees'). Calls into it are held by `R014`; it rests on the named
  `R015` assumption of exported callers. A unit with a function value outside a function body
  gets no extension. Never guessed. Measured over `beispiele/` + `messung/*/`: 10 `noalias`
  (was 2). Not proved in Lean: the LLVM lowering is not a Lean judgment (O27); the model side is
  `Logik/Vertraege/Objekt*.lean`.
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
