# The write side: a census of every place that collects a declaration name

**Written 2026-09-04.** Today's other lane closed one live `M103`-shape hole
(`emit::Namen::geraete`, `beispiele/gift/669-two-devices-share-a-name.gab`) and named a
second as open debt (`emit::Namen::typen`, `traegertyp`) — both bare-keyed maps built by
walking every `module` block into ONE table, with no module qualifier anywhere in the key.
**That is a shape, and a shape is counted, not hunted one instance at a time.** This
document is the count: every place in `crates/gabbro-check/src` that populates a table from
a *declaration's* name, whether the key is bare or qualified, and — for every bare one —
whether two declarations of that kind can actually collide under a bare key today.

No fourth defect was gone looking for. Where the classification below implies a table is
live and open, that implication follows from reading the collection site, its declared
scope (`fuer_jedes_item` / `fuer_jedes_item_im_modul` vs. one item), and the two rules that
could have closed it (`N001`, `N039`) — not from building and running a new poison example.
**Nothing here was repaired.**

## The measure

A **collection site** is an `.insert(...)` (or `.push`/set-`.insert`) that writes a
*declaration's* name — a `device`, `type`, `table`, `format`, `function`, `lock`, `spec fn`,
`static`, `const`, `atomic`, `walk`/`table`/`group` invariant, `rcu`, `axiom` — into a table
read back later by name. It is **bare** if the key is the identifier's own text with nothing
else in it, and **qualified** if the key carries the declaring module (via
`crate::umgebung::qualifiziere`, its call-graph twin `schluessel`, or an equivalent `q(...)`
closure). A bare key can **collide** when two declarations of that kind, in two different
`module` blocks, can legally carry the same short name and nothing already refuses that
before the table is built.

A raw grep for `.insert(` against a declaration-shaped key (`name.text`, `text.clone()`,
`pfad()`, `arch`) finds **186** call sites across `crates/gabbro-check/src/*.rs`. Most of
those write into a table that is rebuilt **per item or per function body** — a `let`-binding
map, a per-function type environment, a per-device register scratch map — and a table that
lives only for the duration of one declaration cannot collide across `module` boundaries by
construction, whatever its key looks like. Rolling those up by the **table** they populate
(the natural unit: "which struct field, or which named local, holds the fact") gives the
denominator below.

| | count |
|---|---:|
| **raw `.insert(...)` call sites (declaration-name-shaped key)** | 186 |
| — of those, into a table rebuilt fresh per item/function body and discarded after it (a `let`-binding map, a per-function type environment, a per-device register scratch map) — cannot span modules regardless of key form, and not counted below | most of the 186 |
| **`N` — distinct WHOLE-UNIT tables identified by rolling the remainder up per struct field / named local** | **70** |
| — bare-keyed (`K`) | **48** |
| — of `K`, deliberately and narrowly protected (documented, see `bindung.rs` below) | 1 |
| — of `K`, closed today by a named refusal at the collection site (`emit::Namen::geraete`) | 1 |
| — of `K`, **collision-capable and open** (`J`) | **46** |
| — qualified by module at the point of insertion (`qualifiziere`/`q(...)`/`schluessel(modul,…)`) | 22 |

**`N = 70` whole-unit tables, of which `K = 48` are bare-keyed across module boundaries, of
which `J = 46` are open and collision-capable.** That is not a small tail: it is nearly
two-thirds of the whole-unit collectors in this crate. Confidence is not uniform across the
list — the 23 tables marked "read" below were read in full, including their reader, before
being counted; the other 23 were classified by the same structural test (`fuer_jedes_item`
family + a bare `name.text.clone()` key, no subsequent duplicate check) applied consistently,
without independently deriving a poison example for each one.

## Why `J` is not `K`: the two refusals, and what each one actually reaches

Two passes could, in principle, stop a same-named pair from ever reaching a bare
collection site. Neither reaches most of them.

* **`N001` (`namen.rs::geltungsbereich`, `doppelt`)** refuses two declarations of one name in
  one **scope** — but `geltungsbereich` recurses into `ItemArt::Modul(m) =>
  geltungsbereich(&m.items, absagen)` with a **fresh, empty `gesehen` map at every
  recursion**. A name declared once at the top level and once inside a `module` — or once in
  each of two sibling modules — is two different scopes to this pass, and it reports
  nothing. This is not an oversight to fix; it is the correct reading of `SPRACHE.md`'s own
  module semantics (`Foo` and `m::Foo` are different names) — **the mistake is downstream,
  in a table that forgets which one it saw.**

* **`N039` (`bindung.rs::pass`)** is the one place in this crate that is bare **on
  purpose**, and says so in its own module doc: *"that one knows no modules"* — because the
  emitter does not mangle, so two `pub` declarations of one name really do collide, at the
  linker, regardless of which modules they came from. But `ausgefuehrter_name` returns `None`
  for anything without a visibility word at all (`device`, `lock`, `spec fn`/table
  invariant, `rcu`, `walk`, `axiom`, `state`, …) and for anything not marked `pub` — so
  `N039` only ever sees the **exported** half of the corpus, and only when **both**
  colliding declarations are `pub`. `beispiele/gift/669`'s two devices were not `pub`; `N039`
  would not have seen them either, and did not need to — the fix landed at the specific
  collection site instead.

So: for any declaration kind that has no visibility word (`device` is the one exception —
it does carry `pub`, but the poison that closed it today used two *private* ones), or for
any pair where at least one side is private, **nothing between `N001` and `N039` stands in
the way of a bare table silently picking one module's fact for both.** That is the shape
`J` counts.

## How this relates to `zaehle-karten.py` (the READ side)

`zaehle-karten.py` counts a **different population under a similar name**. Its subject is
`Umgebung`'s own maps, which **are already keyed by qualified name** (`umgebung.rs` calls
`qualifiziere`/`q(...)` at every one of its dozen collection sites — the reference-correct
pattern below). Its question is: does some *other* pass bypass the module-aware `suche(...)`
candidate walk and hit `Umgebung`'s qualified map with a bare `.get`/`.contains_key`, so that
it only ever matches a name that happens to already be fully qualified? Read at
**45 direct looks, 40 unqualified** as of today's `5165cd8` mark (`instrumente/zaehle-karten.py
--stellen`).

This document's population is upstream of that one and does not overlap with it. A bare
*read* against `Umgebung` is recoverable by fixing the read alone, because the *write* side
already qualified the data — the module information survived construction and was merely
looked up wrong. **None of the 46 tables below have that safety net.** Their bare `.insert`
is the *first and only* place the module is ever known; by the time anything reads the
table, the fact that two declarations came from different modules has already been thrown
away, and no read-side fix — however module-aware — can put it back. `zaehle-karten.py`'s
population is a *fixable-by-the-reader* class; this one is *fixable only by rebuilding the
table*, which is exactly the shape of the fix `emit::Namen::geraete` got today
(`emit.rs`:804, a `contains_key` guard right at the insert, not a smarter reader).

## The reference pattern already in the tree

Twenty-two of the 70 tables already do this correctly, and they show the fix is not exotic
— `umgebung.rs` alone carries a dozen of them, ALL through one two-character habit:

```rust
// umgebung.rs:738
self.geraete.insert(q(&d.name.text), felder);
```

`q` is `|s: &str| qualifiziere(pfad, s)`, and every one of `Umgebung`'s public maps
(`konstanten`, `typen`, `globale`, `kapazitaeten`, `tabellen`, `formate`, `geraete`,
`funktionen`, `verbundtypen`, `walknamen`, `walkschranken`, `erschoepfende_gruende`) goes
through it. `aufrufgraph.rs`'s call graph keys every node with `schluessel(modul, &name)`;
`kosten.rs`'s cost tables and `opsruf.rs`'s call registry go through
`crate::umgebung::qualifiziere(modul, …)`; `m2.rs`'s `ergebnistyp`/`reihenfolge` do the same.

**The telling fact is `umgebung.rs:738` itself.** It is a *third*, independent, and
correctly-qualified table mapping a device's bare name to its declared shape — sitting
beside `emit::Namen::geraete` (bare, fixed today by a refusal) and `m3::geraetetabelle`
(bare, open — see below). **The same fact, about the same construct, recomputed three
times, with three different qualification postures**, is a `W7` violation
("one register per fact") wearing the collision defect's clothes: the emitter and the
register-class checker each grew their own copy of the device table instead of reading
`Umgebung`'s, which already carries the module. That is very likely the actual *cheapest*
fix for the two device-info collectors below, once someone chooses to make it — but making
it is not this document's job.

## The 46 open, collision-capable tables

Grouped by file. `depth` marks how the entry was established: **read** — the collection
site, its scope, and at least one reader were read in full; **pattern** — classified by the
same `fuer_jedes_item(_im_modul)` + bare-`name.text.clone()` + no-guard test, matched against
the file's own style, without separately tracing every reader.

| File : site | Table (what it maps) | Feeds | depth |
|---|---|---|---|
| `emit.rs`:937 (`traegertyp` reads it) | `Namen::typen` — type name → declared type expr | casts/returns/`let` narrowing against a `type` decl | read — **named OPEN DEBT today at `5165cd8`, identical shape to the closed `geraete`** |
| `emit.rs` (`emittiere_mit`, ~770–1280) | `Namen::{formatfelder, uebergaenge, atomics, markierte, ergebnistyp, funktionen, kapazitaet, konstwert, statiken, verbundfeld, tabellen/tabellenglobal/benutzt}` | C emission: field readers, transition dispatch, atomic memory order, tagged-variant sets, result types, ghost-erasure signatures, table storage decision | pattern (13 sibling fields of the same struct, same collection routine, same missing guard) |
| `m3.rs`:518 `geraetetabelle` | device name → per-register class/fields/phase/fallibility | `m3::registerklassen` (`R002`/`R003`), `m1.rs::Pruefer.geraete` (`«B26»` fallible-read binding), `phasen.rs::Regumfeld.geraete` (`«B18»` per-phase class) | read — **structurally identical to `emit::Namen::geraete`; not yet named anywhere** |
| `m1.rs`:180 `sammle_spec_fns` | spec-fn name → arity | `refines` (`M131`/`M132`) — and even a *qualified* `refines mod::name` is truncated to the bare last segment before this lookup (`m1.rs`:3943) | read |
| `m1.rs`:192 `sammle_spezifikationen` | spec-fn/table-invariant/walk-invariant/group-invariant name → arity | `maintains` (`M112`) | read |
| `m1.rs`:301 `programm`, `unveraenderliche_statiken` | non-`mut` static name → "is it a pointer" | assignment-target classification for `static` writes | read |
| `namen.rs`:700 `maschineneigenschaft`, `fordert` | axiom/function name → required machine features | cross-checking a caller's guaranteed features against a callee's `requires Has(...)` | read |
| `namen.rs`:980 `geraetezusage_nennt_ihre_stelle`, `bekannt` | every declared name (+ last `use` segment) | "is this identifier known" gate in a register's `requires` | read — widening only; a collision can *miss* a real unknown-name refusal, not fabricate a wrong value |
| `namen.rs`:1504 `entrust_annahme`, `erklaert` | every declared name | "does `entrust … at SPACE` name something declared" | read — same widening-only shape as above |
| `namen.rs`:3559 `fehlerkanal`, `kann_scheitern` | function name → declared `or R` error type | `let … else` fallibility (`N028`/`N029`) | read |
| `namen.rs`:2598 `verbund_ohne_groesse`, `orte`/`wert_kanten` | record-type name → span / by-value field edges | infinite-size-record cycle detection | read |
| `namen.rs`:4017 `formatklauseln`, `konstanten` | `const` name (unit-wide) | name resolution inside a `format` field's `where` clause | pattern — widening only |
| `namen.rs`:4095 `bootschritte`, `advances`/`bekannt` | boot-step function/axiom/assume name → advance-chain edge | boot-sequence chain well-formedness | read |
| `namen.rs`:3762 `namenstypen`, `sig` | function name → (nominal parameter types, nominal result type) | nominal-type mismatch at call sites — **re-derives its own bare signature table instead of resolving the call through `Umgebung::suche`, which is module-aware** | read |
| `m2.rs`:104 `pass`, `linear` | linear type names (set) | linearity/`leaves` checking | pattern |
| `m2.rs`:~140 `pass`, `divergent` | names of functions that provably never return | divergence propagation | pattern |
| `geteilt.rs`:208 `pass_mit`, `sperren` | **lock name → rank, protected places, span** | the whole deadlock/lock-order family (`H006`, `H012`, `H014`, `H016`) — `modul` is already threaded through to resolve the RANK value (`u.konst_wert(modul, …)`, itself a 2026-08-19 fix for a sibling bug), but the KEY is still bare | read |
| `geteilt.rs` `rcu_domaenen`, `rueckgaben` | rcu-domain name → protected places; guard-return type → domain name | RCU read/write domain checking (`H007`, `H009`) | pattern |
| `gruppe.rs`:48 `sperren_je_traeger` | **protected-place bare name → (lock name, rank)** | group rank-consistency (`U005`) — doc comment already records a 2026-08-24 fix for the RANK value reading `0` from the wrong module; the KEY was not part of that fix | read |
| `paarung.rs` `geteilte` | module-level shared/mutable place names (`static mut`, `atomic`, `accumulates`, `table`) | foreign-place classification (`V009`) | pattern |
| `paarung.rs` `schreiber` | write-target bare name → set of qualified writer functions | who wrote the payload (`V010`) | pattern |
| `paarung.rs` `beobachtet` | atomic names with a foreign counterpart | `«V9»` cross-unit atomic pairing | pattern |
| `pflichten.rs` `spezpraedikate` | spec-fn/table-invariant/group-invariant name → predicate span | `gabbro pflichten` manifest printer only — reporting, not enforcement | read — lower severity: a wrong **span** gets printed, not a wrong verdict |
| `lean.rs` `foreign_calls` | device/transition/generated-op name → call classification | Lean/Isabelle proof-obligation generation | read |
| `lean.rs` `tables`, `records` | table/record-type name → field shapes | same Lean channel — `module` is an available closure argument and is unused for the key | read |
| `lean.rs` `callee_params` | function name → parameter names | same channel; call-argument binding for a generated goal | read |
| `lean.rs` `static_carriers`, `verdicts::fns` | static/function name → table it points at / (module, decl) | same channel | pattern |
| `blindstellen.rs` `typklassen`, `tafel_orte::art` | type/format/table/device/static/atomic/accumulates name → coarse class label | `gabbro blindstellen` coverage measurement ONLY — not part of `pruefe`/`emit` | read — lowest severity: a coarse, usually-identical label distorts a coverage statistic, nothing a program depends on |

That is 28 rows; several stand for more than one sibling table populated by the same
collection routine under the same missing guard (`emit.rs`'s 13, plus two-table pairs in
`namen.rs`, `geteilt.rs`, `lean.rs` and `blindstellen.rs`), which is where the 46 comes
from — counted precisely, not estimated: 28 rows, 46 tables, 23 read + 23 pattern. The severity
spans a wide range on purpose — from `m3::geraetetabelle` and `geteilt.rs::sperren` (both
structurally identical to the headline defect: the WRONG module's per-declaration fact gets
used, silently, for something safety-relevant) down to `blindstellen.rs` (a coverage count
can drift by a cell and nobody's program is wrong for it). **Severity was not the sorting
key for inclusion — bareness across a module-crossing walk was.**

## The one deliberately bare table, and why it does not count against `J`

`bindung.rs::Bindungsregister`/`pass`'s `belegt: BTreeMap<String, …>` (`N039`) is bare by
design, for exported names, across a whole build. It is the one table in this population
whose author wrote down *why* bare is correct here (no C mangling, so the C name really is
global) and *what it deliberately does not cover* (non-`pub` items, and two runs linked
after the fact by `ld`). It is not part of `J` because it is not a defect looking for a
fix — it is itself the refusal mechanism, and its scope is exactly as wide as its stated
guarantee.

## What is NOT open

* **`emit::Namen::geraete`** — closed today (`emit.rs`:804, `beispiele/gift/669`).
* Everything in `umgebung.rs`, `aufrufgraph.rs`'s graph nodes, `kosten.rs`'s cost tables,
  `opsruf.rs`'s call registry, `m2.rs`'s `ergebnistyp`/`reihenfolge`, and `domaene.rs`'s
  per-item local maps — all qualified at the point of insertion, or freshly built per
  declaration and discarded (Category 3: cannot span modules regardless of key form, because
  the table never outlives the one item it was built for).
* **`cnamen.rs`** and `erzeugernamen.rs`'s cross-reference against it — these hold *C's own*
  reserved names (a fixed, measured reference table) and the names the *generator itself*
  forms, not a table of program declarations; out of this population by definition.

## Verdict

**`J = 46` is not zero, and it is not close to zero.** The two `emit::Namen` fields that
opened this investigation are not an isolated pair — they are two instances of a shape that
recurs, largely unremarked, in the checker's oldest and newest passes alike: `m1.rs`'s
`refines`/`maintains` machinery, the entire lock-ordering family in `geteilt.rs` and
`gruppe.rs`, and the Lean/Isabelle proof-obligation generator in `lean.rs` all build their
own bare, module-crossing name table instead of reading `Umgebung`'s already-qualified one.
**Nothing above was reproduced with a poison file or repaired.** Whoever picks this up next
has, for the first time, a denominator to work against instead of a third anecdote.
