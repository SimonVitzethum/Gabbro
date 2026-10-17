# Heap and memory discipline: arenas, ceilings, commit, release, sampling

*Rewritten 2026-10-17 from the design of 2026-09-17 (wave D) and everything built on it since.
Status: **built** in the checker, the Lean model and the LLVM backend; the C backend (deprecated)
carries the earlier forms. Section numbers 2, 3, 4 and 7 are cited by code comments and keep their
meaning. The generated representation and the stack/recursion side are in
[`LLVM-BACKEND.md`](LLVM-BACKEND.md) section 4; the surface syntax is `SYNTAX.md` section 9.1.*

## 0. The rule and what exists

> A heap is allowed but never unbounded (`dokumente/PRUEFER.md` section 3): every region has a
> declared ceiling and refuses on full. The one opt-in beside it is an explicitly sampled form
> without a static ceiling (section 5.3), in which every allocation may fail and must be handled.

| Form | Declaration | Meaning |
|---|---|---|
| pool | `table T count N` with generated `insert`/`remove` | fixed element, per-element release; the table form |
| static arena | `arena A capacity lo .. hi of T;` | monotone region: `lo` the reservation (no `else` owed within), `hi` the hard bound; `alloc` bumps, `reset` starts a fresh generation |
| dynamic arena | `arena A capacity lo .. hi max M of T;` | address reserved for `M`, storage committed up to `hi`, grown explicitly with `grow A by n else { … }` |
| sampled unbounded arena | `arena A capacity lo .. hi of T pb P blw B;` | no `max`; the ceiling is the counter room (`u32::MAX`); before each commit the program's probe `P` is asked for free bytes, below `B` the `else` runs |
| slot release | `free A[i];` | gives one slot back (intrusive LIFO), the name dies statically |
| range give-back | `reset X at i count n;` on a `static` array | zeroes the range and, through the program's own binding, returns whole pages |

## 1. Binding constraints (Simon) and where each lands

1. **No OS hard dependence in the language, checker or Lean model.** Reservation, commit and page return
   are runtime; the model knows only regions with a declared extent. The program's own binding
   (`bibliothek/linux/linux.gab`: `gabbro_os_reserve`, `_commit`, `_seitengroesse`, `_seiten_zurueck`) is
   the hosted source of the OS calls. The LLVM backend currently books the Linux gate numbers itself
   (`LLVM-BACKEND.md` section 4), an open profile gap, not a language fact.
2. **A static, checkable ceiling.** `max M` is a translation-time constant; growth beyond it is a refusal
   (section 4). Every commit is a visible, costed statement.
3. **An efficiency budget.** At most one word load more than the static lowering on the `alloc` fast path
   (`used < committed` against `used < hi`), no per-object header, no ghost bytes at run time.
4. **Memory follows load.** The ceiling is a limit, not a standing allocation: take, give back, release to
   the OS, hold nothing useless (the `pb` probe, `free`, `reset at`, page return).

Scope reading: `max` goes on the arena declaration (the monotone form with the `N210`-`N214` machinery).
A `max` clause on tables is reserved future syntax: not parsed, not refused, not built.

## 2. Clause syntax

```
arena Log capacity 2 .. 8 max 64 of u32;

impl fn nutzen() -> u32 effects { writes Log } costs <= 24 ops {
    let c = alloc Log (x) else { return 0; };
    grow Log by 8 else { return 0; };
    reset Log;
}
```

* `max M`: optional third bound, a translation-time constant (`N210` family, the same constness rule as
  `lo`/`hi`). With it: `0 <= lo <= hi <= M`, `M >= 1`, `M <= u32::MAX`. Without it: the static meaning,
  byte for byte (`M = hi`, no new checks).
* `hi` keeps its meaning (initially committed count) and is the commit floor; `lo` the reservation; `M`
  the ceiling.
* `grow A by n else B;`: explicit commit request, `n` a constant `>= 1`. The `else` runs when the runtime
  cannot commit below `M` (the only runtime failure left); it does not fall through, like the `alloc`
  `else`. The `else` always stands (the grammar demands it).
* `pb P blw B`: `P` names exactly one nullary gate or function answering an integer with no error
  channel; `B` is a translation-time constant (`N584`, `N585`).
* No shrink statement: commit is monotone within a run.

## 3. Reservation versus commit

| | reservation (virtual) | commit (usable storage) |
|---|---|---|
| what | address range for `M` slots, nothing touched | prefix of `c` slots, `hi <= c <= M`, readable and writable |
| who | the runtime at load | the runtime on `grow` / on demand, counted by the checker |
| checker fact | `M` from the declaration | the per-path pair `(count, committed)` (section 4) |
| Lean | `Fin M`, `DynArena.M` | the committed prefix `c <= M`, monotone |
| failure | the load refuses | the `else` branch, or a checker refusal |

Commit is monotone within a run: `reset A;` sets `used` to zero and leaves the commit alone (one store, as
for a static arena). There is deliberately no decommit statement: a shrinking primitive would need its own
checker domain and Lean model for a pressure payoff no corpus program measures. What the runtime may do
instead is return the physical pages of dead chunks (section 6.2), which changes residency and never the
committed prefix or the semantics.

## 4. Checker obligations

Per function body and per path the pass (`crates/gabbro-check/src/arena.rs`) tracks `(count, committed)` per
arena, starting at `(0, hi)`: `reset` restores `(0, hi)`; `grow A by n` sets `(count, min(committed + n, M))`
on the main path and leaves the state untouched in the `else` branch (the `else` walks from the state BEFORE
the request); joins take `max` of counts and `min` of committed (what both paths guarantee); loops saturate
the count, and committed needs no saturation (capped by `M`).

| Rule | Code | What it refuses |
|---|---|---|
| declaration shape | `N210` | non-constant bounds, `0 <= lo <= hi (<= M)` violated, `hi` not fitting the emitted counter |
| generations | `N211` | use of an index outside its generation (also across a `reset` in a callee or started routine, a stale index handed to an `index into A` parameter, an index through a global/field/slot/call result wherever the program resets that arena) |
| owed `else` | `N212` | an `alloc` whose static count since the last reset may exceed the reservation `lo`, without its `else` |
| undeclared arena | `N213` | `alloc`/`reset`/`grow` naming no declared arena |
| arena place | `N214` | a place over an arena that is not exactly `A[i]` with an index of `A` |
| commit cover (R-commit) | `N466` | an `alloc` from a dynamic arena whose count may stand at or past the path's committed prefix, `else` or not; scoped to arenas with a usable `max` |
| commit ceiling (R-max, R-grow-const) | `N426` | a `grow` amount that is no constant, and every `grow` whose UPPER bound plus amount may pass `M`, branch or no branch |
| sampling | `N584`, `N585` | a probe naming no (or no unique) gate/function; a probe with parameters, an error channel or no integer answer; a threshold that is no translation-time constant |
| release | `N586` | read after `free`, second `free`, free of a borrowed (parameter) or computed place; one rule, shared faces |
| range give-back | `N569`, `N570` | `reset X at i count n` on anything but a known-length `static` array; `aligned N` that is no constant power of two in 1..65536 |
| concurrency | `N521`, `N522` | a `reset` of an arena in a routine that may run concurrently with a use of it; counter touches from two concurrent routines without a guarding lock held at every access (the counters are plain words) |
| costs | `K001`-`K003` | growth points are costed like any statement: `alloc` is one primitive plus the value plus the `else`, `reset` one primitive, `grow` one plus the runtime's declared commit cost; a `grow` inside `locks` counts against `held` (`K002`) |

**Two joins, because "usable" and "can pass `M`" are different questions** (fix lane F2). The LOWER bound
(`min`-joined committed) answers what may be touched; the UPPER bound per arena answers how much the run may
have committed and holds the ceiling. The upper bound joins with `max`, is left alone by `reset` (nothing is
decommitted), saturates after a loop whose body may commit without a constant pass bound (`forever`,
`traverse`, a non-constant `retry`), multiplies by the pass bound of a `retry … bounded N`, and crosses
function boundaries: each routine gets a per-invocation bound (its own `grow`s plus its callees' and
started roots'; unbounded in a recursion or through a call through a place), and the whole-program total is
the sum over the ROOTS of the call graph, each entered once per load (a `concurrent` body once per naming, an
`entry … dispatch` target without bound). The run model is the goal theorem's (declared starts; separately
linked units NOT CLAIMED): a routine entered again by a caller the unit does not see can still reach the
runtime's past-ceiling stop.

`R-max` as its own code is not wired: with `M = hi` it would fire on `beispiele/99`'s boundary demo, a
tightening of the kind lane 184 was rejected for; on a dynamic arena a count that may reach `M` is already past
the committed prefix and falls at `N466` first. The allocation count stays per function (like `costs`); the
commit ceiling is whole-program.

## 5. Decisions

### 5.1 Growth trigger: explicit `grow`, with a cost

Every commit is a program step the checker counts, the cost pass prices and the model carries. A page fault is
the most invisible commit possible: no statement, no cost, no checker fact, and a latency term on every
store. `grow` concentrates commit at named points the WCET story can carry; the runtime needs two functions
(reserve, commit) instead of a fault handler. **Rejected:** fault-driven commit with a latency assumption.
Revisit only if a deployment measures `grow` placement costing more than the fault-handler trust base saves.

What the `else` of `grow` catches: it runs when the platform REFUSES the commit. Under default Linux
overcommit that practically never happens (out of memory then surfaces at first touch); only strict accounting
(`vm.overcommit_memory = 2`) makes the `else` reachable. The branch is the program's answer to a refused commit,
not a promise that every out-of-memory reaches the program; no test exercises it.

### 5.2 Release: reset for phases, slot release for the rest

`reset A;` is unchanged (generation consumed, one store). The earlier decision "no per-slot free" was REVISED
by a measured need: interleaved lifetimes that no phase boundary separates. `free A[i];` is the result:

* the slot is exactly one arena slot, the index a bare name bound by `alloc` to the current generation; the
  name dies statically (`N586`): copies died with it, rebinding clears it, joins take the union, `reset`
  clears it; a parameter index is borrowed (the owner frees); a computed place names no death to carry;
* no `else` (freeing a live slot cannot fail);
* at run time the slot carries the link word (intrusive LIFO), so the next `alloc` reuses it without commit and
  without sampling; free links live in a separate metadata mapping so any element width works (the earlier
  "elements under 8 bytes carry no link, `Y103`" refusal is gone);
* the per-slot liveness domain the first design feared is the static death of the name, not a bitset.

Per-element release for long-lived objects still belongs to tables (`insert`/`remove`); programs with phase
lifetimes use arenas.

### 5.3 The sampled unbounded form

`pb P blw B` switches the unbounded form on: no `max`, and before every commit the generator asks `P` for free
bytes; below `B` the `else` runs (the OOM path). One probe per MiB, none on the fast path; freestanding, `P`
measures itself. The static whole-program memory bound is lost for such a program, which is what makes the
language Turing-complete in the model. `beispiele/1160-halde-mit-abtastung.gab` is the example (checker-clean;
LLVM-runnable on both targets, the out-of-memory branch taken correctly at 100 bytes free). An unbounded heap
WITHOUT sampling is unwritable: without the clause no-`max` is the static form with ceiling `hi`.

## 6. Runtime shape

### 6.1 Descriptor and interface (cited as "section 7" in older comments)

Per dynamic arena the program carries a descriptor of base, `used`, `committed` and the constant `M`/`hi`;
the runtime never names an arena any other way. The interface is two operations: reserve at load (a failed
reservation refuses the load, never a smaller range) and commit on `grow`/on demand (success bumps
`committed`, failure runs the `else`). `alloc` lowers as the checked static form with `committed` in place of
the `hi` immediate; `grow` as `if (commit(desc, n)) {} else { <else> }`; `reset` as `used = 0`.

* **LLVM backend (current):** the five-word generated representation, reserve/commit/release as IR over raw
  gates, the chunked free-link metadata and the page discard are described in `LLVM-BACKEND.md` section 4.
* **C backend (deprecated):** the hosted driver writes the arena runtime (`treiber.rs::ARENA_LAUFZEIT`, template
  `arena.dyn`, `gabbro runtime arena`) over the program's `gabbro_os_*` binding; the kernel-module and bare-metal
  drivers carry the `arena.modul` / `arena.metall` templates. `grow` and `free` lower in `emit.rs`; the G
  exporter refuses them by name (`LG005`).

### 6.2 Page return

Freeing the last live slot of a ~1 MiB chunk returns its whole interior pages (`madvise(DONTNEED)` in the Linux
profile); `reset` returns the used payload pages; both keep the reservation, access rights and committed prefix.
Residency is not virtual commit; page return is best effort and partial boundary pages can stay. `reset X at i
count n` on a static array zeroes exactly the checked interval and, with declared bindings, returns its whole
interior pages (the retired `pruefe-seiten-zurueck` measured the resident-set drop; not guarded today). Nothing is decommitted
and no revoked-page bitmap exists.

## 7. Lean model

`grammatik/Grammatik/Bausteine/Arena/`: `Arena.lean` (the static arena: `alloc_innerhalb_reserve`,
`keine_fragmentierung`, `reset_used`, generations as a type index), `ArenaZucker.lean` (`ArenaForm D`: sugar over
a table of `count = hi` plus a `used` global; `arenaAlloc_unter_schranke`), `ArenaDyn.lean`, `ArenaSeiten.lean`,
`ArenaReset.lean`.

* `DynArena` (ceiling `M`, floor `hi`, committed prefix `c`) with `dynGrow` (`dynGrow_monoton`,
  `dynCommit_innerhalb`, `dynGrow_ueber_M`, `dynGrow1_gdw_alloc`), and the block form `DynForm` over a
  declaration: `dynGrowB`, `dynAlloc`, `dynGrow_commit`, `dynCommit_monoton`, `dynAlloc_unter_commit`,
  `dynAlloc_ueber_commit` (the model halves of `N466`) and the simulation `dynAlloc_simuliert` (a dynamic run
  whose allocations stay under the committed count simulates the static-max program step for step). Witness
  namespace `DynZeuge` on a concrete declaration.
* `FreiZustand`: high-water mark plus freed slots; `freiAlloc`, `freiFree` (a double free gives `none`);
  `freiAlloc_unter_marke`, `freiAlloc_marke_monoton`, `frei_rundlauf`, `frei_doppelt_nein`.
* `ArenaSeiten.lean`: `discard_live` (dead-chunk discard preserves live payload) and `discard_preserves_reuse`
  (it preserves the exact next logical allocation of `FreiZustand`). It does not prove the producer or the kernel.
* Assumption texts in the one list of `Zielsatz/Kern/Spec.lean`: `Laufzeit.reserve` ("the loader reserves the virtual
  range for every dynamic arena's `M` before any start runs; a failed reservation refuses the load") and
  `Laufzeit.commit` ("every admitted `grow` either commits before the next statement or takes the `else`; a
  successful commit names readable/writable storage; commit latency is bounded by the runtime's declared per-slot
  cost"). Fault-latency text was recorded and not inserted (explicit `grow` is the trigger).

## 8. What is not covered

* `free` across function boundaries and aliases outside the tracked ownership discipline (a copy the flow does
  not track reads freed memory silently; the alias question is `A1-OWN-PAPER.md`'s).
* A `reset` in a routine running concurrently with the index holder is refused as a pair (`N521`), but generations
  are tracked along one thread of control otherwise; memory safety does not depend on it (a stale index stays
  below `committed`), the residue is a logical dangling reference.
* The G exporter: the complete `ArenaForm`/`DynForm` export and the G form of `grow`, `free` and the range reset
  (`LG005`, OFFEN O14).
* The binary-level proof that the generated runtime and the kernel do what the model assumes (`LLVM-BACKEND.md`
  section 8; `PLAN-UEBERSETZUNGSVALIDIERUNG.md`).
* The commit cost: the runtime's per-slot commit cost is a declared number (`K003`), not measured here.

## 8a. Plan: dynamic data structures and their invariants inside the goal (2026-10-17, Simon's order)

**Order rule (Simon, 2026-10-17): the Lean model first, then exporter, checker, compiler.** Nothing in
this plan is built in Rust before the Lean part it rests on exists and `gabbro_ziel` still prints exactly
`propext`, `Classical.choice`, `Quot.sound`. Every change of the statement is a reviewed `Spec.lean` diff.

**Target.** Structures that grow without a static element bound (lists, stacks, trees, hash chains over
arena slots, capability trees) are IN the statement, and `table`/`group` invariants over them are claimed
legs (`invRuhe`, `invSicht`), not vacuous. Today both are false: dynamic structures are NOT CLAIMED
(OFFEN O29, now scoped in), the exporter writes `Inv := Empty` and refuses `maintains` (`LG001`), and every
arena program (examples 98, 99, 153, 154, 158, 1160, 1161) is UNCERTIFIED (`LG005`, OFFEN O14).

**The approach that exists (what is built on):** an arena is sugar over a table of `count = hi` plus a `used`
global (`ArenaZucker.lean`, `arenaAlloc_unter_schranke`); `DynArena`/`DynForm` add the committed prefix
(`dynGrow`, `dynAlloc_simuliert`: a dynamic run under its committed count simulates the static-max program);
`FreiZustand` models slot release (`freiFree`, double free gives `none`, `frei_rundlauf`); invariants are
declared on `table`/`group`/`walk` (`maintains`, `breaking`, `ops`, kind `E` preservation duties, `N275`–`N277`,
`N496`, `N583`); `traverse`/`walk` express a bounded path through linked slots (`by consuming`, `floor`).
A link is an INDEX into an arena table, never a pointer, so a link is well-formed iff it is below `committed`
and its slot is live (`N586` makes use-after-free a static error).

**Phases, in order:**
1. **Model the missing statements in machine G (Lean, `Bausteine/Arena/`).** `grow` and `free` as `Block`
   forms over the existing sugar (they exist as lemmas, not as G blocks), with the proof that each
   preserves memory safety and the contract legs; `reset` generations as a type index (exists) lifted to G.
   Exit: `ArenaForm`/`DynForm` have G constructors; `dynAlloc_simuliert` extended by `dynGrow_simuliert`,
   `freiFree_simuliert`.
2. **Invariants over live slots (Lean, `Erhaltung.lean`, `Durchgaenge.lean`).** A new invariant family
   `InvDyn`: a predicate over the set of LIVE slots of a table plus the links among them (links in range,
   acyclic along a declared walk, tree shape for the capability tree, freelist disjoint from live slots).
   Preservation theorems for the three mutators (`alloc`+link, `free`+unlink, link update under a lock) in the
   style of the existing table invariants, plus non-degenerate witnesses (`..._zeuge`) and a counter-model
   (a broken invariant that the model rejects). Closes the proof side of O4/O5/O6 (capability derivation tree:
   `delete_leaf`, `revoke`, the sibling consistency demand).
3. **Concurrency (OFFEN O20).** Generations and the commit ceiling assume one control thread. Model `grow` as a
   locked commit (the commit is a lock-guarded step, per-thread allocation from a guarded arena) and prove the
   leg `Laufzeit.commit` as a consequence of the lock discipline instead of a named assumption where possible.
4. **`Spec.lean` diff.** Remove 'dynamic data structures' from NOT CLAIMED, let `invRuhe`/`invSicht` carry
   content for exported dynamic programs, keep every old leg word for word. Re-prove `gabbro_ziel` on the new
   statement; two independent verdicts as for every extension of the goal (AGENTS.md section 1).
5. **Exporter (`lean_g.rs`).** Lift `LG005` for arenas and `LG001` for `maintains`/invariants only for the forms
   phases 1–3 cover; everything else stays refused by name. Regenerate `REGISTER.txt`: the booked success
   measure is the number of CERTIFIED arena programs.
6. **Checker.** Only afterwards align the Rust checker with the model: O11 (an invariant no function maintains
   is accepted by nothing but `N583`'s online case), `maintains` completeness, walk bounds; a form the checker
   accepts and the model lacks is a checker bug (a refusal, never a warning).
7. **Compiler.** No new lowering is needed: the LLVM backend already lowers arenas, `grow`, sampling and slot
   release; the certificate's `llvmArenen` rows are checked against the model (the Lean consumer of `llvm-cert`
   is the open item of PLAN-UEBERSETZUNGSVALIDIERUNG).

**Evidence for done:** three new examples (a singly linked list over a dynamic arena, a binary tree with a
sibling-consistency invariant, a hash chain) that are CERTIFIED with a non-vacuous invariant, each with a
poison probe whose broken invariant the checker refuses AND the model rejects; `gabbro_ziel` on the standard
axioms; the guardians green.

**Decisions Simon has to make before phase 1:**
(a) first structures: list and tree (recommended; the tree is the capability tree of O4–O6) or hash chains first;
(b) element links stay indices into one arena (recommended: no pointers, no int-to-pointer, consistent with
`own`) — or links across arenas are in scope;
(c) whether `free` across function boundaries (needs the `own` boundary rule of `A1-OWN-PAPER.md`) belongs to
this round or follows it.

**Size and critical path.** Phases 1–2 are the long Lean pieces (Opus agents, one at a time on `grammatik/`,
each with a warm `.lake`); phase 4 is the reviewed statement change; 5–6 are small Rust. Counts are not
completion evidence: the exit conditions above are.

## 9. Re-measuring

```
./instrumente/pruefe-llvm.py                              # runs teile/llvm-modelldeckung.py: which arena/slot model members the LLVM backend lowers
# resident-set drop after a range/page return (legacy C runtime): measured by the retired pruefe-seiten-zurueck (2026-10-17); not guarded today
cargo test -p gabbro-check --lib llvm:: --no-fail-fast    # small-slot reuse, page discard, range reset, thread groups
cargo test -p gabbro-check --test paesse --no-fail-fast   # arena_* checker rules with their clean twins
```

## 10. The cost ledger (a sidecar specification, not wired)

`crates/gabbro-check/src/kostenledger.rs` is a standalone module (`std` only) that renders, parses and
`verify`s a deterministic sidecar `kosten-ledger v1`, one row per function (`modul::funktion`), recording
what the checker PROMISED and what it counted: `costs` (promise text, constant value if readable, input
names), `per_pass` (one entry per `forever`), `bounded` (one entry per `retry`), `deadline` (date, constant,
`arch`, falsifier name and class), `body_ops` and `absenkung` (statement counts per primitive). A bound the
checker cannot read as a constant is recorded as `?` with its text. Format: `key value` lines, `function <name>`
opening each row, `|` between structured fields (`\\`, `\n`, `\p` escapes), byte-stable `render`, `parse`
rejecting unknown keys, blank lines and incomplete rows loudly, `Ledger::verify` reporting every divergence.

It **decides nothing** (no refusal, no `K` code, no conversion between ops and cycles), is a record and not a
proof (that a `bounded` budget is honest about the world is the probe run's job), and is emitted BESIDE the
artefact, never inside it. **Status: the writer's hook (`kostenledger::ablegen`) is not wired into any emitter**
(no call site exists in `crates/`), and the second-artefact reader the first design named
(`instrumente/nachpruefer.py`) is not in the tree; only the module and its unit tests exist
(`rustc --test crates/gabbro-check/src/kostenledger.rs`). The design stays as the answer to "a number that lives
only in the checking run is a number the artefact cannot defend".
