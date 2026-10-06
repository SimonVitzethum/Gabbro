# Language gaps: what cannot be written today (Lane 1395)

Date: 2026-10-06. Author: muse-agent-1395.
Scope: current Gabbro language (checker + emitter + model/exporter).
Excluded by task: unbounded dynamic data structures (heaps without a ceiling, OFFEN O29).

Method note: the `gabbro` binary could not be executed in this lane
(`bash` tool calls are rejected in this session, so neither `./cargo-pruef`
nor a prebuilt binary could be run; a file search additionally confirmed
no `target/debug/gabbro` exists in this clone). Every row below is therefore
reasoned from the grammar (`dokumente/SYNTAX.md`), the refusal sentences
(`crates/gabbro-check/src/saetze.rs`, read), the ledger (`dokumente/OFFEN.md`),
the walls (`TODO.md` §-1/§0/§0c), the census
(`messung/SCHREIBLAST-EFFECTS.md`), and the write probes
(`messung/schreibprobe/S01`–`S22`), whose headers record their own
`gabbro pruefe` / `gabbro emit` measurements verbatim. Each row marks
**measured** (a probe or corpus file demonstrates it) vs **assessed**
(my judgement from the grammar/refusal text, not re-run here).
Caprock note: the read-only OS source (`../caprock-messbasis`) named in
the task is unreachable from this session (outside-clone reads are
denied by the sandbox), so OS-component needs below are cited via
`OFFEN.md`/`TODO.md`/probe references, not by direct Caprock reads.

Class key: LANGUAGE (cannot be said) · GUARANTEE (can be said, checker
refuses a true program) · CEREMONY (sayable, large boilerplate) ·
LIBRARY (belongs in a binding/library, not the language).

## Ranked gaps

### 1. No type parameters / generics (LANGUAGE) — blocks the whole standard library
- Need: one ring buffer, one queue, one memory copy for every element type
  (TODO §0b L1/L2; firewall needs ring + timer wheel before anything else).
- Smallest demonstration (measured, `S20-typanwendung.gab` header):
  `type Queue(T) = { kopf : u32, ende : u32, w : T, };` parses with
  **0 errors** (the `(T)` list exists for `linear ghost type Held(Lock)`,
  not as a parameter), `gabbro emit` is byte-identical to the
  unparameterised type, and using `T` in a field falls at the emitter with
  `[C001] no lowering: field type`. The other spellings never parse:
  `type Queue<T> = …` → `P001` (`;` expected, `<` found),
  `table Queue(T) …` → `P001` (`{` expected, `(` found).
- Workaround: monomorphise by hand — one copy per (source, target) pair
  (`S22`: the copy is writable once per pair; F3 wrote its ring
  monomorphised for this reason). Cost: library size ~ number of shapes;
  TODO §0b's generic question is still undecided (per-type by hand,
  generator with byte-identity guardian, or type parameter; the last
  touches deliberately non-recursive `Ty`, OFFEN O15's rule applies).
- Measured.

### 2. Record as a value has no `Ty`; exporter refuses it (LANGUAGE) — blocks completion/error values
- Need: F4/F5/F6 completion values, `reply(EP, […])`, any `-> Completion`
  function (`S18`, FRAGMENTE «B7», OFFEN O15/O16).
- Smallest demonstration (measured, `S18-verbund-als-wert.gab` header):
  `return Completion(id: k, len: n);` checks with 0 errors and emits
  (`return (Completion){ .id = k, .len = n };`), but
  `gabbro lean-g` refuses with `LG002` (a record has no `Ty`; `Typen.lean`
  §1 has no product). Passing `ptr<normal, r> Completion` works.
- Workaround: out-pointer or split results; cost: lost value semantics,
  one extra indirection per call, and the program stays outside the goal
  theorem (O27 registers it UNCERTIFIED). Priced and REFUSED 2026-09-15:
  a `Ty.prod` gains zero of 113 corpus programs; what pays first is the
  `Endblock` binder (row 9) and the C side of aggregates (O16, also zero).
- Measured (probe headers + O15/O16 census numbers).

### 3. `traverse` has no label: no early exit from a table walk (LANGUAGE) — blocks first-hit search
- Need: firewall IPC fastpath ("stop at the first live receiver"),
  F1 `peak_revoke_ops`, any find-first over a table (S13, TODO §0c,
  wave-B residue).
- Smallest demonstration (measured, `S13` header + `SYNTAX.md:1247`):
  `leave i;` inside `traverse i over …` → `S001` (`leave i` targets no
  enclosing loop label); `traverse runde i …` → `P001`. The `ident`
  after `traverse` is the binder; only `retry`/`forever` take labels.
- Workaround: walk the whole table guarded by `if !gefunden` (64 passes
  where C does 1), or `retry` with hand-threaded index + re-proved range
  at every use. Cost: linear waste per search, or manual plumbing
  (exactly what the grammar's head sentence calls a refutation).
- Measured.

### 4. No windowed `traverse … from <start> count <len>` (LANGUAGE) — blocks windowed scans / hold chunking
- Need: firewall windowed scan, K002 hold chunking (TODO wave-B residue:
  parses to `P001`, builds no AST node; bounds/effects/lowering wait).
- Demonstration: `traverse … from s count n` → `P001` (grammar has no
  window arms; `intmatch`/`absenkung` own nothing for it).
- Workaround: `retry` with hand-threaded window + `narrow` per access.
  Cost: per-access bound proof instead of one entry check (SYNTAX §2
  «SG-27» names this as manual plumbing).
- Assessed from grammar + TODO; the `P001` itself is the long-standing
  recorded behaviour.

### 5. `option` only over table indices, never over an ordinary type (LANGUAGE) — blocks F5/F6 shapes
- Need: F5 `let mut capacity : option Sectors = none;`,
  F6 `frei_min : option Bytes` (S12, FRAGMENTE «B14», OFFEN O5).
- Smallest demonstration (measured, `S12` header):
  `-> option Sektoren` → `[P001]: 'index' expected, identifier found`.
  `option index into T` works in all four positions (slot, static,
  parameter, local); `option u32` does not parse at all.
- Workaround: hand-written two-case `tagged` sum per type; `match` over
  it is exhaustive by shape. Cost: one declaration + constructor +
  match per optional type (~10 lines each), no `None` literal sharing.
- Measured (probe header; O5 closed as DEMAND G1 of a second kind —
  premise supply — so this row is the remaining half of that demand).

### 6. `count … : …` exists as a computation, not as a predicate (LANGUAGE) — blocks the F1 refcount invariant
- Need: F1 `refcount_matches` as a table `invariant` / `spec fn`
  (S11, FRAGMENTE «B13»).
- Smallest demonstration (measured, `S11` header):
  `let n = count k in slots of T : p;` → 0 errors (`beispiele/71:33`);
  the same predicate in `invariant` or `spec fn` → `D021`
  (``k`` … is not declared here). Cross-table count is refused by
  design (SYNTAX:554 — a `group` invariant instead, «SG-10»).
- Workaround: hand-counted loop variable + comment (`beispiele/19:67`,
  `46:51`). Cost: manual bookkeeping the invariant should carry; the
  count-as-computation plus `ensures` naming it is the honest nearby form.
- Measured.

### 7. Strings refused in aggregates, constants, statics and slots (LANGUAGE, deliberate cut) — blocks string-carrying tables/messages
- Need: any table slot, record field, `const`/`static`, array, variant,
  pointer or `fn` type carrying a string (OFFEN O24, `N465`).
- Demonstration: representation (`gabbro_string_N`: length word + bytes),
  limit (`1 ..= 65535`, `N486`) and literals (`"hi"`, `ExprArt::Kette`)
  all landed (lane 261); `N465` still refuses the aggregate positions
  (a cut, not a model gap — length flow facts cannot reach them).
  Max-bound over-approximation also stands (`+`/copies compare maxes;
  a copy whose actual length would fit is refused — sound, incomplete).
- Workaround: parallel byte array + length field with manual discipline.
  Cost: the length invariant hand-maintained per site; no `Char`/UTF-8
  bridge either (`ZeichenfolgeC.lean` states the gap).
- Measured (O24 + `beispiele/32`, `161`).

### 8. Byte pointers / region answers: emit-only, never certified (LANGUAGE) — blocks 183-style programs' proofs
- Need: `beispiele/183-region-vom-tor.gab` shape (region from a gate),
  `ptr<normal, r> u8` byte work (OFFEN O37, `C186`, `LG003`).
- Demonstration: gate region answers emit (`C186` refuses a region
  answer without its `or R` channel; gifts 1383–1387 pin the shapes);
  byte pointers have no G form, so 183 stays `UNCERTIFIED LG003`
  (behind it `LG002`). Nothing releases a region.
- Workaround: none that certifies — programs run uncertified.
- Measured (C-free lane rows + register).

### 9. `Endblock` has no binder forms: `let x = f();` and `return` under `locks` at body top level (LANGUAGE) — blocks certification of ordinary tails
- Need: `beispiele/21-verbundwert`, `98`/`99` (arena `alloc` at top
  level), `beispiele/110`, `125` (return under `locks`), any tail-let
  of a call (OFFEN O14(2), O15, O27 model decisions).
- Demonstration: `Block.arenaAlloc` is a `Block` former, a body is an
  `Endblock` — same wall `let x = f()` hits; refused by name in the
  exporter (`LG002`/`LG004` family). O27: 176 accepted programs
  uncertified; the tail-let and return-under-locks shapes are among the
  named model decisions blocking them.
- Workaround: restructure the tail (bind earlier inside a block).
  Cost: small per site, but it is the highest-leverage single form —
  O15 measured it unblocks 21/98/99 and every top-level tail-let.
- Measured (O14/O15/O27).

### 10. `bool` static checks clean, never becomes C (LANGUAGE) — blocks the service-loop stop flag as written
- Need: F5 service loop `static mut anhalten : bool` (S15/S16, TODO §0c).
- Demonstration (measured, `S15:26-28`): `gabbro pruefe` 0 errors,
  `gabbro emit` → `[C001] no lowering: static with a non-constant
  initialiser`.
- Workaround: `u32` flag (`0`/`1`). Cost: one word + comparisons;
  trivial, but every boolean piece of shared state pays it.
- Measured (probe header).

### 11. Payload hand-off to a plain carrier after `awaits` refused (GUARANTEE-by-design, open rely) — blocks lock-free message passing
- Need: release-publish a flag, `awaits` it, then read a PLAIN payload
  (OFFEN O25c: `N485`, gifts 1205–1210 reserved, unused).
- Demonstration: the rely IS the goal now (`PrueferX`/`NutzerPflichtA`/
  `ZielFX` over GX; `beispiele/116`, `162` certified payload-free);
  the plain-payload rule needs happens-before race freedom + flow facts
  (producer writes only before `publishes`, consumer reads only after
  `awaits`) and is not built. Linked units sharing an atomic, payload
  `awaits`/`exchange`/atomic-array export likewise open.
- Workaround: guard the payload with a lock instead. Cost: lock traffic
  on a path designed to be lock-free; the guarantee is kept, not lost.
- Measured (O25c; class is GUARANTEE only in the weak sense — the
  refusal is a named open premise, not a false rejection).

### 12. Dense 256-way dispatch over a full `u32` (CEREMONY) — costs, not expressiveness
- Need: firewall 256-way dispatch (TODO §0c: 1797 ops as comparison
  chain; integer arms + `switch` lowering landed via lanes 222/227,
  coverage `N411`–`N414` built by fix lane F1).
- Demonstration: arms cap at 256 values each, so a full-`u32` dispatch
  must narrow the scrutinee first; flow passes read an integer match as
  possibly skipped (review G07, precision cost only). The Lean
  correspondence for `stmt:switch-int` is still tied to a constructed
  `CS.sw`, not to what `emit.rs` writes.
- Workaround: flat comparison chain. Cost: measured 1797 ops shape;
  writable, just expensive.
- Measured (TODO §0c + G07).

## Expressly not gaps (checked, to avoid re-reporting)

- Unbounded heaps without ceiling: excluded by task (decided).
- `tagged` construction: closed (lane 167, O8; `beispiele/120/121`).
- `accumulates … pub` across modules: closed (server lane phase 2;
  `reason` as 13th `pub`-carrying item, `N038`/`N025` keep names).
- Pointer indexing `p[i]`: closed (server lane; `M101` arm fix, gifts
  1367/1368, example 168).
- `narrow` beside same-name pointer / `let … else` annotation: closed
  (server lane; examples 169/170/171, gifts 1369/1370).
- Cross-unit table access / `gabbro link` / `gabbro build` multi-unit:
  closed (server lane §0e; `N501`–`N505`, `N516`).
- Worker pool / symmetric pool: closed (fix lane F10, O18).
- Per-core accumulator write half + atomic order checks: closed
  (`N481`–`N483`, O25–O26); read/payload half is row 11.
- `bool` static is row 10 — listed because TODO §0c still names it.
- `transition`/`advances` vocabulary without measurement: not a gap
  finding of this lane (no program in the surveyed probes needs them;
  noted only as unmeasured).
- Missing stdlib CONTENT (copy/ring/sort/format/PRNG, TODO §0b L1–L6):
  LIBRARY work, blocked in turn by row 1. Named here once so no row
  above is mistaken for it.

## Ranking rationale

Rows 1–2 block whole program CLASSES (every generic container; every
function returning a record). Rows 3–4 block every table search/scan
with an exit or a window (the firewall fastpath and every driver loop
of that shape). Rows 5–7 block concrete F5/F6/driver shapes (optional
values, counted invariants, string-carrying tables). Rows 8–9 block
CERTIFICATION (programs run but carry no proof). Rows 10–12 are paid
per site (a flag spelling, a lock instead of a hand-off, a comparison
chain).
Class coverage note: no ranked row carries LIBRARY — missing stdlib
CONTENT (copy/ring/sort/format/PRNG) is library work gated behind row 1
(no generic container to put it in) and is therefore booked under
"Expressly not gaps" rather than ranked as its own gap.
