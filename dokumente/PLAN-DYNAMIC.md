# Heap and memory discipline: arenas, ceilings, commit, release, sampling

*Rewritten 2026-10-17 from the design of 2026-09-17 (wave D) and everything built on it since.
Status: **built** in the checker, the Lean model and the LLVM backend; the C backend (deprecated)
carries the earlier forms. Section numbers 2, 3, 4 and 7 are cited by code comments and keep their
meaning. The generated representation and the stack/recursion side are in
[`LLVM-BACKEND.md`](LLVM-BACKEND.md) section 4; the surface syntax is `SYNTAX.md` section 9.1.*

## 0. The rule and what exists

> A heap is allowed but never unbounded (`dokumente/CHECKER.md` section 3): every region has a
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
measures itself. Removing the source-level `max` alone does not establish Turing completeness: the current
LLVM representation still caps the slot count at `u32::MAX`, and `DynArena` has an explicit finite `M`.
The general machine-G model has unbounded call stacks, but a universal-machine simulation remains unproved
(`grammatik/Grammatik/Berechenbarkeit/`, THEOREM-MAP section 91). `beispiele/1160-halde-mit-abtastung.gab` is the example (checker-clean;
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

* `free` across function boundaries (Lean audit and implementation plan: section 12) and aliases outside the tracked ownership discipline (a copy the flow does
  not track reads freed memory silently; the alias question is `A1-OWN-PAPER.md`'s).
* A `reset` in a routine running concurrently with the index holder is refused as a pair (`N521`), but generations
  are tracked along one thread of control otherwise; memory safety does not depend on it (a stale index stays
  below `committed`), the residue is a logical dangling reference.
* The G exporter: the complete `ArenaForm`/`DynForm` export and the G form of `grow`, `free` and the range reset
  (`LG005`, OFFEN O14).
* The binary-level proof that the generated runtime and the kernel do what the model assumes (`LLVM-BACKEND.md`
  section 8; `PLAN-TRANSLATION-VALIDATION.md`).
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
   phases 1–3 cover; everything else stays refused by name. Run `cargo test --test zertifikate -- --nocapture`: the booked success
   measure is the number of CERTIFIED arena programs.
6. **Checker.** Only afterwards align the Rust checker with the model: O11 (an invariant no function maintains
   is accepted by nothing but `N583`'s online case), `maintains` completeness, walk bounds; a form the checker
   accepts and the model lacks is a checker bug (a refusal, never a warning).
7. **Compiler.** No new lowering is needed: the LLVM backend already lowers arenas, `grow`, sampling and slot
   release; the certificate's `llvmArenen` rows are checked against the model (the Lean consumer of `llvm-cert`
   is the open item of PLAN-TRANSLATION-VALIDATION).

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

### 8a.1 Phase 2 status (2026-10-18): `InvDyn` for the list and the tree, proved in Lean

**What is proved in the first pass** (`grammatik/Grammatik/Bausteine/Arena/Struktur/`, axioms `propext`/`Classical.choice`/`Quot.sound` at most; no
`sorry`; `gabbro_ziel` untouched: none of these modules is imported by `Zielsatz/`):

| Piece | File | Statement |
|---|---|---|
| chain `KetteF`, `ListOkF` | `ArenaKette` | finite chain from a head, pairwise distinct slots, every slot live; `push_ok`, `pop_ok`, `unlink_ok` (delete after a predecessor, by a permutation argument), `push_doppelt_bricht` (pushing a linked slot gives a self loop: no chain exists) |
| tree `BaumF`, `BaumOkF` | `ArenaBaum` | tree shape = `Nodup` of the preorder slot list (subtrees disjoint, no slot its own ancestor); `einfuegen_ok`/`blatt_aus_ok` (left) and `*_rechts_ok` (mirror), `einfuegen_doppelt_bricht`, `InBaum.links/rechts` |
| live slots `Lebt` | `ArenaLebt` | `Lebt = below the counter and not on the free list`; `lebt_bump` (alloc from the counter), `lebt_abheb` (alloc from the free list), `lebt_frei`: every other live slot stays live, the new slot is live, the freed slot is dead |
| the allocator's frame `Fremd` | `ArenaFremd` | the EXECUTED forms `arenaRumpf`, `freiNimm`, `freiRumpf` write only counter, free head, payload and free link (`*_fremd`); `frisch_lebt`, `nimm_lebt`, `frei_lebt` bundle execution, frame, free list and liveness |
| list `ListOk` | `ArenaListe` | `liste_frisch`, `liste_nimm` (both alloc branches: list and free list stay well formed, the new slot is live and unlinked), `liste_frei` (free of a live, unlinked slot), `liste_push`, `liste_pop`, `liste_unlink`, `liste_pop_frei` (stack discipline) |
| tree `BaumOk` | `ArenaBaumWelt` | `baum_frisch`, `baum_nimm`, `baum_frei`, `baum_einfuegen_links/rechts`, `baum_blatt_aus_links/rechts`, `baum_frei_nach_blatt` |
| witnesses, planted defect | `ArenaDynZeuge` | a concrete full arena (4 slots) with slot `1` on the free list, list `2 -> 0` and tree `2 (left 0)`; `pop_zeuge`, `einfuegen_zeuge`, the EXECUTED `alloc` from the free list (`nimm_zeuge`); the defect "a linked slot is also on the free list" is rejected (`liste_defekt_bricht`) |

**Shape of the guarantee.** The invariant is a predicate over the world (`ListOk A L G σ`, `BaumOk ...`), not a new
carrier. The allocator moves are proved on the executed `Block` forms (the three blocks of `ArenaFrei.lean`); the
link stores (`lnk[p] = ..`, `head = ..`) are plain `assignSlot`/`assignGlob` and are proved as statements about the
worlds they leave (`liste_push` and the rest take the store facts as hypotheses, exactly as `abheben_sicher`).
Hypotheses are the checker-visible ones: single release and no use after release (`N586`: the freed slot is live and
no longer linked), a pushed slot is unlinked and live, a hung leaf has an empty child place, and `k.n = stand` is
what `arenaAlloc`'s guard binds.

**Closed since (2026-10-18, second pass, all in `grammatik/Grammatik/Bausteine/Arena/Struktur/`; the dynamic-structure modules moved there for the 20-entry limit):**

| Open item of the first pass | Now | File |
|---|---|---|
| executed forms of the link stores | PROVED. `Block.linkPush`/`linkPop`/`linkUnlink` (list) and `Block.blattEin`/`blattAus` (tree, left and right) over `assignSlot`/`assignGlob`/`narrow`, for any bound index variable and any continuation. `*_ausfuehren` give the store facts, `liste_push_zug`/`liste_pop_zug`/`liste_unlink_zug` and `baum_einfuegen_*_zug`/`baum_blatt_aus_*_zug` keep `ListOk`/`BaumOk` ON THE EXECUTED BLOCKS. `linkKopfBind`/`linkNachBind` read the head/successor. Guard failures (`*_voll`) end in the `else`. | `ArenaLinkForm`, `ArenaBaumForm` |
| `LinkKopf` excludes `komm`; `grow` composes | PROVED. `LinkKopf.h3 : g ≠ komm`, `Fremd` names `komm`; `nachGrow_gleich`; `grow_liste`, `grow_baum`: the executed `grow` keeps `FreiOk`, every liveness, `ListOk`/`BaumOk`; `dynGrow_voll`. | `ArenaWachs` |
| allocator moves in the middle of a body | PROVED. `Block.freiVar` (`free` of ANY bound index), `frischAlloc_ausfuehren`, `nimmAlloc_ausfuehren` (+ `*_voll`) for every continuation; `arenaRumpf_ausfuehren`. | `ArenaAllocForm` |
| the recognizer | PROVED FOR THE LIST (and the free list). `Erk a b a'` (`ArenaErkenner`): a body is accepted iff it is built from the proved moves (alloc from counter / free list, `free`, push, pop, unlink, head and successor reads, `grow`, guards with a store-free `else` (`Rein`), payload stores, branches) over an abstract state per bound variable (`frei` owned, `glied` member, `offen` unknown; the Lean model of the `N586` name table). **`erk_erhaelt`**: `Erk a b a'`, `StrukturOk σ`, `StrukturPasst a σ ρ` give `StrukturOk` at EVERY exit of the run of `b` and `StrukturPasst a'` when it falls off; **`erk_koerper`**: a body that knows nothing at entry. The proof applies the executed-form theorems; their hypotheses are exactly what the abstract state says. Witnesses: `nimmPush_konkret` and `kopfUnlinkFrei_konkret` RUN accepted bodies on the real arena; planted defects with NO derivation (rejected through the soundness theorem and a real run): `nimmPushPush_abgelehnt` (a slot linked twice), `nimmFreiFrei_abgelehnt` (double release), `nimmFreiPush_abgelehnt` (use after release), `pushFremd_abgelehnt` (a slot the body does not own). | `ArenaErkenner`, `ArenaErkennerLemmas`, `ArenaErkennerBeweis`, `ArenaErkennerZeuge`, `ArenaAuf` |
| sibling consistency (O6), abstract half | PROVED over the abstract binary tree. `SibF` (first child has parent `j`, next sibling has the parent of `j`); the slots after a leaf in/out (`einfuegen_mitglieder`, `blatt_aus_mitglieder`); `sib_einfuegen_links/rechts` (the new child gets parent `p`, the new sibling the parent of `p`), `sib_blatt_aus_*`; planted defect `sib_ohne_vater_bricht` and concrete witness/defect (`sib_einfuegen_zeuge`, `sib_defekt_bricht`). | `ArenaSibling` |
| hash chain, abstract half | PROVED over the abstract link function. `HashOkF` (every bucket a `ListOkF`, chains pairwise disjoint); `hash_push` (the slot is on NO bucket), `hash_pop`, `hash_unlink`; witness `hash_push_zeuge`, planted defect `hash_defekt_bricht` (a slot on two buckets). | `ArenaHash` |

**Closed in the third pass (2026-10-18, all in `grammatik/Grammatik/Bausteine/Arena/Struktur/`; sub-folders `Formen/` (executed forms) and `Erkenner/` (recognizer); axioms `propext`/`Classical.choice`/`Quot.sound` at most, no `sorry`; `gabbro_ziel` untouched):**

| Open item of the second pass | Now | Files |
|---|---|---|
| recognizer for TREE bodies; bodies that hold a list AND a tree | PROVED, as ONE recognizer. `Erk K a b a'` runs over a declaration `K : Dekl A` of the arena (`liste`, `baum`: one list, one tree, both or neither; `getrennt`: different words). Status per variable `frei` (live, in NEITHER structure) / `liste` / `baum` / `offen`. The invariant is `Dekl.Ok` = free list + `ListOk` + `BaumOk` + DISJOINTNESS of the two (so a slot that leaves the list may be released: it is no tree member). Tree moves are GUARDED forms (the guard is part of the form, its `else` store-free): `haengen` (`check Cp[p] == nil`), `abschneiden` (`narrow` + `check leaf`), `wurzelEin` (`check root == nil`), `wurzelAus`; reading the root/children reuses `linkKopfBind`/`linkNachBind`. **`erk_erhaelt`**: every exit keeps `K.Ok`, a body that falls off meets its abstract state, and no recognized body ends in `leave`/`next`. The old list-only recognizer is REPLACED (it is the case `baum := none`). | `ArenaDekl`, `ArenaErkenner`, `ArenaErkennerLemmas`, `ArenaErkFallAlloc`, `ArenaErkFallListe`, `ArenaErkFallBaum`, `ArenaErkFallSchleife`, `ArenaErkennerBeweis`; forms `ArenaBaumFormG`, `ArenaBaumFormZug`, `ArenaBaumWurzel`; frame `ArenaRahmen` |
| loops in the recognizer | PROVED for `forever`, `traverse`, `retry`. A loop is recognized when its body, started in a LOOP STATE `k0`, ends in a state at least as strong as `k0` (`Abs.Schwacher`); `traverse`/`retry` fall off in `k0` (`retry` also through the overflow block), `forever` never falls off. `leave`/`next` are not in the vocabulary (an `else` is only `return`/`return why`), which is what makes the rules sound without an exit state. Inductions on the fuel (`foreverLauf`), the index list (`traverseLauf`), the bound (`retryLauf`). | `ArenaErkFallSchleife` |
| function bodies | PROVED. A function body is an `Endblock`; `ErkE K a e` accepts a run of recognized statements ending in `return`/`return why`; block forms enter through a branch (`if true { <block> }`). `erkE_erhaelt`/`erkE_koerper`: the body returns or fails in a world where `K.Ok` holds. | `ArenaErkEnde` |
| executed form for the PARENT store | PROVED. `Block.blattEinErst` (first child, `par[i] = p`) and `Block.blattEinBruder` (next sibling, `par[i] = par[p]`) over `blattEin`; `parStore_ausfuehren`, `blattEin{Erst,Bruder}_ausfuehren`; **`sib_haengenErst_zug`, `sib_haengenBruder_zug`, `sib_abschneiden_links/rechts_zug`** keep `BaumOk` AND `SibOk` (`SibF` on a world) on the executed block. | `ArenaSibForm`, `ArenaSibZug` |
| `revoke` of a subtree | PROVED for the tree and the sibling demand. `unterbaum_aus_ok` (abstract: cutting a whole subtree at a child place keeps the tree well formed; the remaining members are old members outside the subtree; the subtree's slots are not members any more) with right mirror and `sib_unterbaum_aus_*`; **`baum_unterbaum_aus_links/rechts_zug`** on the executed `Block.blattAus` WITHOUT the leaf hypotheses: `BaumOk` and `SibOk` hold on the remaining tree and every slot of the cut subtree is a live ORPHAN, so a release of one slot keeps the tree (`baum_frei`). | `ArenaBaumUnter`, `ArenaSibZug` |
| bucket head in a TABLE field | PROVED. `BucketKopf` (a field of a second table holds the head), `Block.hashPush/hashPop/hashKopf`, `hashPop_ausfuehren`, `hashUnlink_ausfuehren`; **`hash_push_zug`, `hash_pop_zug`, `hash_unlink_zug`** keep `HashOk` (`HashOkF` with the heads read out of the table field) on the executed blocks; the popped/unlinked slot is live and on NO bucket. | `ArenaHashForm`, `ArenaHashZug` |
| witnesses and planted defects | RUN by evaluation (`rfl` for short runs, `decide +kernel` for long ones) on real worlds, the soundness theorem applied: tree `baumHang`, `baumSchnitt`; list+tree `kombiHang`, `kombiVersetzen` (a slot moves from the tree to the list), `kombiEnde` (a function body); loops `drain` (`retry`), `drainForever`, `fuell` (`traverse`); parent/revoke `erst_zeuge`, `bruder_zeuge`, `revoke_zeuge`; hash `push_zeuge`, `pop_zeuge`. Defects with NO derivation (soundness theorem + a real run that breaks the invariant): double hang, hang of a non-owned slot (the root below itself), use after release (tree); a slot pushed into the list that is a tree member (`doppelGlied`: each structure well formed, the DISJOINTNESS fails); a slot linked in again on every pass of a `retry`. Planted defects of the forms: a new sibling without the parent of `p`, a child released while still linked, a slot pushed into a second bucket. | `ArenaErkZeugeBaum`, `ArenaErkZeugeKombi`, `ArenaErkZeugeSchleife`, `ArenaErkZeugeSib`, `ArenaErkZeugeEnde`, `ArenaHashZeuge` |

Design notes: (1) the executed forms each carry their FRAME (`LinkRahmen A fs gs σ σ'`: every link field outside `fs` and every link head
outside `gs` reads as before), so the move of one structure is shown not to touch the other (`Dekl.getrennt`); (2) `Erk` takes the loop and
guard shapes from `Code/Refine/Loop.lean` only as a reference for the machine-G semantics, the soundness proofs are about `execBlock`;
(3) a long run is stated through an equation (`erk_koerper_lauf`), because the elaborator unfolds a long `execBlock` term at great cost.

**Still open inside phase 2 (not claimed):**
* the recognizer is NOT yet a component of `Akzeptiert` and `Spec.lean`/`gabbro_ziel` do not mention it (8a.3 stays a proposal): there is
  no generic statement that every ACCEPTED unit's writers of a dynamic structure are `ErkE`-derivable, and no `Block` that the Rust checker
  accepts is translated to an `ErkE` derivation (the exporter does not exist for these forms); `ErkE` is a Prop (a certificate), there is no Bool
  decision procedure;
* calls: a recognized body calls no function (`Erk` has no call constructor); a writer that calls a helper needs the callee's contract (its
  `ensures` must say what it does to the structure);
* the release of EVERY slot of a revoked subtree: after the cut the orphans are live and releasable one by one, but a walk that frees them all is a
  loop whose abstract state (the not yet released orphans) the recognizer does not carry; `revoke` as one recognized body is therefore only the cut;
* a recognizer for hash chains (`HashOk` has executed forms and witnesses, `Dekl` has no hash component) and for the sibling demand (`SibOk` has
  executed forms, the recognizer does not track the parent store: a body that hangs a slot with the plain `haengen` and no parent store is accepted
  although it breaks `SibOk`; the capability tree needs `Dekl` to name the parent field and the moves to be the `blattEinErst/Bruder` forms);
* `leave`/`next` inside loop bodies (a loop body can only exit by `return`/`return why` or by falling off);
* the vocabulary is closed: any other store into a link field or head, a `bind` that copies an owned index (aliases), has no derivation and is
  refused; widening it means a new constructor with its theorem;
* a link field that holds an index of ANOTHER arena (decision (b) says: not in scope).

### 8a.2 Concurrency of arenas (O20): design note and Lean status (phase 3, step 3, 2026-10-18)

* **Per-thread arena (per cpu, thread-local carrier).** The footprint rule already forbids another thread from
  touching the carriers; the free list, the counter and the links change in one thread, so `ListOk`/`BaumOk` hold at
  every step boundary of that thread by `ArenaListe`/`ArenaBaumWelt` plus the statements above. No new leg.
* **Shared arena under a lock.** The counter, the free head, the commit word and the link fields are carriers guarded
  by one lock `L` (`protects`). The existing lock legs already say what is needed: `sperrWechsel` (every acquire starts
  from and every release leaves a memory where `S.inv L` holds) and `sperrSicht` (no other thread moves a carrier while `L`
  is held). The structure invariant IS the lock invariant: `S.inv L := FreiOk ∧ ListOk ∧ BaumOk` (and the commit bound
  `stand <= komSt`). The proof obligation is a whole critical section: acquire with the invariant, run the
  alloc/link/unlink/free moves, release with the invariant. Between two stores the invariant is broken (`free` after
  its first store, a linked slot not yet pushed): that is why it is claimed at the lock moves and NOT inside the section,
  and why `invSicht` (observed by the guard holder) is the weaker, already present form.
* **`grow` as a locked commit.** `grow` writes only `komm` (`dynGrow_commit`); `Lebt`/`ListOk`/`BaumOk` read slots below
  `stand <= komm` and the free list, so they are untouched (a `dynGrow_fremd` lemma, same proof as `*_fremd`, once
  `LinkKopf` excludes `komm`, DONE). The leg `Laufzeit.commit` (the OS gate's contract: success names readable storage) stays a
  named hardware/binding assumption; what changes is that two threads cannot interleave a commit with an allocation,
  because both hold `L`.
* **What the model still lacks:** a statement that two sections on one arena commute up to slot names (no ABA on a
  freed and re-allocated slot across a section boundary: a thread must not keep an index across a release; that is
  `N586` per thread and needs the cross-thread form: a slot a thread holds is not on the free list unless that thread
  freed it). A lock-free free list (Treiber stack) is phase B item 5, not this.
* **Next steps (2026-10-17 note), now answered:** (1) the section theorem: PROVED (`abschnitt_erk`, `abschnitt_rufe`, below); (2) `dynGrow_fremd`: DONE
  (`nachGrow_gleich`, `grow_liste`, `grow_baum`); (3) the slot-ownership predicate for the ABA point: NOT done (see "Still open").

**What is proved in step 3** (`grammatik/Grammatik/Bausteine/Arena/Struktur/Sperre/`, 13 modules, imported by `Grammatik.lean`; axioms `propext`/`Classical.choice`/`Quot.sound`
at most, no `sorry`; `gabbro_ziel` and `Spec.lean` untouched: none of these modules is imported by `Zielsatz/`, they import `Spec.lean`):

| Piece | Statement | File |
|---|---|---|
| the arena as a lock invariant | `Dekl.orte` (table, committed word, counter, free head, list head, tree root); `ok_gleich_wort` (= premise `dekl_ok_traeger`: `Dekl.Ok` reads only those words, and not the trace); the lock family `Dekl.sperr K L0` (`inv L0 = Dekl.Ok`, `orte L0 = K.orte`, every other lock `true`); `sperr_inv_iff'`, `sperr_lokal` (`SperrInvLokal`, the user's duty, discharged once for every arena), `sperr_ok` (`SperrInvOk` from the one declaration fact `Bewacht c L0`) | `ArenaSperreTraeger` |
| a recognized body is lock-free (= premise `execEndH_eq_execEnd`) | `Rein.ohneLocks`, `erk_ohneLocks`, `erkE_ohneLocks`; `erkE_execEndH`, `erk_execBlockH` (the existing `Block/Endblock.execH_ohne` applied); `erk_erhaeltH`, **`erkE_koerperH`**: the soundness theorems over `execBlockH`/`execEndH` for ANY lock family and environment move | `ArenaSperreOhne` |
| **the section theorem** | `freiH_post` (a release after an arena-preserving outcome keeps the arena and the check cannot fail); **`abschnitt_erk`**: `locks L { body }` with `Erk K Abs.leer body a'` under `HavocOk (K.sperr L) U`: every exit meets `Dekl.Ok`, none is `leave`/`next`, and the only `logik` outcome is one the body already had (the release check adds no failure); `abschnitt_start` (the world a section starts in meets the invariant, from the third clause of `HavocOk`); the CALL form: `Rufe` (a section body that is a run of calls of recognized functions), `RErhaelt`, `rufe_post`, **`abschnitt_rufe`** | `ArenaSperreAbschnitt` |
| a recognized callee through the program semantics | **`rufAt_erk`**: for every `f` with `ErkE K Abs.leer (P.rumpf f)`, `rufAt P O passes n` answers (value or reason) in an arena-consistent world from one (the premise `RErhaelt` of the call form; also for the patched `rufFrei`, which only maps `logik` to `hardware`) | `ArenaSperreRuf` |
| the three legs of the goal on the arena family | `arena_ruhe` (`sperrInv`), `arena_wechsel` (`sperrWechsel`: acquire starts from and ends in a whole arena, release hands over a whole arena), `arena_sicht` (`sperrSicht`), `komm_nur_halter` (the committed word is accessed by a holder alone, and no other thread moves it while `L` is held), `arena_ziel` (all three from `Ziel P (K.sperr L) ..`) | `ArenaSperreMaschine` |
| **`grow` as a locked commit** | `lesGlobs_ne_komm`; **`grow_ok_iff`, `grow_atomar`**: a commit is ONE store to `komm`, no word the structures read is `komm`, so the arena invariant holds after it iff before, every liveness and the counter are as before, `komSt' = komSt + n`; `komm_wachstum`; **`grow_gesperrt`** (a section whose body starts with `grow` is an `abschnitt_erk` instance) | `ArenaSperreWachs` |
| the writer obligation of an arena invariant (D3), against the proposed meaning (D2) | `InvHaeltD2` (`arena i = some ⟨A, K⟩ ↦ K.Ok σ`), `InvAmRueckD2`, `InvGutSM` (`InvGutS` with an arbitrary meaning; `invGutS_iff_M`), **`invGutSD2_arena`**: if every owed arena invariant of `f` has `ErkE K Abs.leer (P.rumpf f)`, the arena is whole at entry and the user's obligation covers the other invariants, then `InvGutS` of the proposed meaning holds; `invGutSD2_ohne` | `ArenaSperreInv` |
| the machine bridge (premise 2) | **`erkE_maschine`**: from a thread of the call machine whose world meets the arena invariant at the entry of a writer's body `b` with `EndR A (Tief P A n) b` (coverage) and `ErkE K Abs.leer b` (certificate), the steps of the thread reach a machine whose frame is popped with the return value, whose shared memory is the return world's AND meets the arena invariant (`rufG_adaequat_ruf` + `erkE_koerper`, joined at `execEnd`) | `ArenaSperreBruecke` |
| coverage from the certificate | `Stmt/Block/Endblock.schleifenfrei` (looks through the statement forms of the fragment, refuses `forever`/`traverse`/`retry`); **`erk_blockR`, `erkE_endR`**: a loop-free `Erk`/`ErkE` derivation IS `BlockR`/`EndR` (every move unfolds into `narrow`/`check`/`assignSlot`/`assignGlob`, every `else` is a bare return); **`erkE_maschine_erk`**: the machine bridge with the ONE certificate (`ErkE` + `schleifenfrei`), no separate `EndR` | `ArenaSperreAbdeckung` |
| witnesses and planted defects | the declaration `FDL` (the four-slot arena, shared under one lock; only the lock fields differ from `FD`), `KLL`, `w0L`, `ok_w0L`, `sperr_ok_zeuge`; the section `locks () { nimm; push }` RUN over an environment move of the acquire (`abschnitt_zeuge`: ends `.ok`, arena whole, head `1`, release check passed; `havoc_U0` shows the hypothesis `HavocOk` is satisfiable); PLANTED DEFECT `lnk[2] = 2` in a section (`stray_bricht`, `abschnitt_defekt_schleife`: the release check FIRES, the section ends `logik schleife`; `stray_abgelehnt`: no `Erk` derivation; `stray_kein_havoc`: no environment move hands the stray world to an acquirer); `grow_zeuge_L`, `grow_ueber_decke`; PLANTED GAP `wachs_negativ_schrumpft` (below); the machine witness `erkE_maschine_zeuge` (a thread holding `()` runs the writer by machine steps, covered AND recognized, memory whole, head `1`); the call form: `rErhaelt_PL`, `abschnitt_rufe_zeuge`, `abschnitt_rufe_lauf` (`locks () { f(); }` over `rufAt`, run) | `ArenaSperreWelt`, `ArenaSperreZeuge`, `ArenaSperreWachsZeuge`, `ArenaSperreMaschZeuge` |

**Findings of step 3 (each named, none hidden):**
 1. **The footprint of a pure `pop` escapes `schuldet`.** `InvTraeger` and `schuldet` count TABLES only (`D.traeger : Inv → List Tab`). The recognized moves `pop`
    (`head = lnk[i]`) and `wurzelAus` (`root = nil`) write ONLY a global (a head word) that `Dekl.Ok` reads: a function that does just that owes no arena invariant by `schuldet`,
    and premise (iii) of D5 ("a step of a thread outside every writer moves no carrier of `i`") is false for it. (`invRuhe` stays TRUE for such a function, because one store
    `pop_ok` keeps `Dekl.Ok`; it is the footprint ARGUMENT that fails.) Repair, needs a decision: arena carriers are `Tab ⊕ Glob` -- `Deklaration.traeger` becomes
    `Inv → List (Tab ⊕ Glob)` and `schuldet` counts `D.gschreibt` too, or an arena invariant is owed by every function that writes ANY word of `Dekl.orte`
    (`K.orte.any (writes f)`), which needs no change of `Deklaration` but a case in `schuldet`.
 2. **The arena at ENTRY.** `erkE_koerper` gives the arena at every exit FROM an arena-consistent entry; `InvGutS` runs from any world meeting `ReqAmEintritt`, and an expression
    `requires` cannot say `Dekl.Ok`. For a shared arena the entry is the lock invariant at the acquire (`abschnitt_start`); for a per-thread arena it is the start memory and `invRuhe`.
    `invGutSD2_arena` takes it as the premise `hein`; the Spec diff must say where it comes from (a `requires`-pseudo clause `arena_whole` that the exporter writes and the
    caller discharges, or the premise "every call of a writer is inside a section or a closed machine").
 3. **A `locks` body cannot hold `return`.** `Rein` demands `Λ.Perm V.ende` and a `return` inside `locks L` has `held L` in `Λ`; so the inline form `abschnitt_erk` is typable
    only where `V.ende` contains the held lock (a writer that returns holding the lock), and the realistic section is the CALL form `locks L { f(..); }` with `f` requiring `L`
    (`abschnitt_rufe`, run in `abschnitt_rufe_lauf`).
 4. **The commit bound `stand <= komSt` is NOT in the lock invariant.** `Dekl.Ok` does not read `komm`; the recognized alloc `frisch` is guarded by the static bound `hi`
    (`Block.arenaAlloc`), not by `komSt` (`Block.dynAlloc` is not a recognized form); the executed forms' frames name the link words, not `zaehl`/`komm`; and the model's `grow` accepts
    `n < 0` (`wachs_negativ_schrumpft`: `komm 2 -> 1`; the surface demands `n >= 1`, `R-grow-const`) -- `Erk.wachs` now carries the premise `0 ≤ n` (repaired in step 3: before it
    accepted any `n`; the soundness proof is unchanged because the Ok-invariant never reads `komm`). The theorems say: the commit never breaks anything the structures read
    (`grow_atomar`) and is a lock-guarded carrier (`komm_nur_halter`); "every live slot is committed storage" needs (a) `n >= 0` in `Erk.wachs` (DONE), (b) a `dynFrisch` constructor
    over `Block.dynAlloc`, (c) the frame of every form extended to `zaehl`/`komm`. Lean-only repairs; (b) and (c) not done.
 5. **The machine bridge covers loop-free writers.** `EndR` has no guard inside a loop body (`narrow`/`check` need `Block D V false`), so a recognized body with a loop is a statement about
    `execEnd` (`erkE_koerper`) only; its machine correspondence needs the loop fragment extended to guards.
 6. **`Erk` and `EndR` were two separate derivations; now one.** `erkE_endR` (`ArenaSperreAbdeckung`) derives the coverage from a loop-free certificate, `erkE_maschine_erk` is the bridge
    with that single premise (the Rust side needs only the exporter's `ErkE`; the checker's `programmImFragmentG` is no longer a second source of the same fact).

**Still open in 8a.2 (not claimed):** the ownership predicate for the ABA point across a release (a slot a thread holds is not on the free list unless that thread freed it; the cross-thread
form of `N586`); two sections commute up to slot names; per-thread arenas need nothing new (the legs above do not mention them); a lock-free free list (Treiber) is Phase B item 5;
the commit bound (finding 4); the footprint repair (finding 1).

### 8a.3 The combined `Spec.lean` diff for decisions 1-3 (plan of 2026-10-18; NOT applied, nothing built)

**This section replaces the third-pass proposal (D1-D5 of the arena diff) and §11.3 (D1-D6 of the payload diff).** One `Spec.lean`
diff carries three decisions Simon took on 2026-10-18 (strongest variant for safety and power, effort irrelevant):

1. **Footprint.** `Deklaration.traeger : Inv → List (Tab ⊕ Glob)`, COMPUTED from `Dekl.orte` for an arena invariant instead of being listed
   by hand; `schuldet` counts `gschreibt` too.
2. **Arena invariant, inductive.** One more invariant name in `D.invs` whose meaning is `Dekl.Ok`; established in the initial state by the
   start obligation (`StartPflicht`), preserved by every function that owes it; a SHARED arena is the lock invariant (`abschnitt_start`).
   No exporter-written pseudo-`requires`.
3. **Payload.** The order is derived per atomic (no free `ord` quantifier for racy-payload flags); flag invariants are the target
   (havoc only as a named intermediate stage); `D.nutzlast` widens to table cells; the design anticipates re-publication (epochs), the
   first cut is one-shot.

Legend used below: **[V]** read in the tree or measured in this session; **[M]** measured by running Lean 4.33.1 on a throw-away mock
(`kratz`, not committed); **[U]** unverified estimate or assumption, to be checked at the step named. Nothing in this section was built
against the real tree: the worktree has no `.lake`, so no `lake build` ran. Order rule (CLAUDE.md): everything is Lean first; the Rust
exporter changes by ONE line (A.9); the checker and the compiler follow only after both verdicts.

#### 0. Findings that shape the diff (reported, not resolved silently)

No pair among decisions 1-3 is contradictory in intent. Eight constraints surfaced while planning; T1 and T3 change the text of the
earlier proposals, T2 and T6 are costs the earlier text did not carry. Simon should confirm T1 and T3 before the work starts.

* **T1. Decision 1 forces the arena declaration into `Deklaration` (changes 8a.3's old D1: `Programm.arena`).** The arena structures
  (`ArenaForm`, `DynForm`, `FreiForm`, `LinkFeld`, `LinkKopf`, `ListDekl`, `BaumDekl`, `Dekl`) mention only `Tab`, `Feld`, `Glob`, `count`,
  `typ`, `gtyp` and `Ty` [V: read in `ArenaZucker`, `ArenaDyn`, `ArenaFrei`, `ArenaListe`, `ArenaDekl`] and are parameterised by a
  `Deklaration`. A field of `Deklaration` cannot mention `Dekl D`. So `D.traeger` can only be computed from `Dekl.orte` if the arena
  carries no `D` in its type: `Deklaration extends DeklBasis` where `DeklBasis` holds exactly those six fields (and their `DecidableEq`
  instances), the arena structures are parameterised by `DeklBasis`, and `Deklaration` gets the field `arena : Inv → Option (Dekl ..)`.
  **[M]** A mock with this shape elaborates: `where` literals in the style of the ~84 fixtures [V: 84 `Deklaration … where`], a computed
  `traeger`/`schuldet`, `rfl` proofs of `traeger = orte`, and `CoeOut Deklaration DeklBasis` so that `(A : ArenaF D)` still elaborates
  (`/…/scratchpad/exp1.lean`, `lean` exit 0). Not measured: the 60 real Arena files, `D.mitRuhe`, universe or instance trouble at scale.
  Consequence: `Programm` gets NO new field, so its 80 `Programm … where` literals [V] and the exporter's `Programm` literal stay untouched.
  Fallback R1 if the spike (M1) fails: keep `traeger` a field and add the premise `∀ i K, arena i = some K → traeger i = K.orte` to (a);
  that is "listed by hand and checked", not "computed", and Simon should decide whether it is acceptable before it is used.
* **T2. `rufAt` cannot see `Dekl.Ok` (the layering fact the earlier text missed).** `rufAt` (`Kern/Semantik/Semantik/T2.lean`, lines 397-399)
  evaluates `P.invariante i` at every return of an owing function and answers `logik .invariante i` on failure; every statement `InvAmOrtG`,
  `invRuhe`, … rests on that check. Its import closure is 9 modules; the closure of `Dekl.Ok` is 68, of which 59 are not below `rufAt`
  (20,296 lines, including `Kern/Semantik/Maschine/T1-T9`, `RufMaschineD`, `Wettlauf`) [V: `deps2.py` over `import` lines]. So the new meaning
  `InvHaelt … := Dekl.Ok` is NOT available where the semantics checks it. Chosen resolution (L1): a Bool `Dekl.okB` defined in a new Kern
  module between `Semantik/T1` and `T2` (fuel-bounded walks over `World` readers) plus `okB_iff : K.okB σ = true ↔ K.Ok σ` proved downstream
  (O5). Rejected alternatives: (α) `rufAt` skips arena invariants and `InvAmOrtG` for them is proved from the certificate by induction over machines
  (leaves `P.invariante i` junk for an arena name, adds a special-case branch to the one proof that serves every other invariant, and the
  semantics that defines every other leg would no longer check this one); (L3) a `Programm` field `invOk : Inv → World → Bool` with a premise
  tying it to `Dekl.Ok` (the meaning would again be exporter-written). Either remains an option if O5 proves too costly; (L1) is the strongest.
  Remaining wart of (L1) and (α) alike: `Programm.invariante` stays total, so for an arena name it carries an ignored expression
  (the exporter writes `tru`); planted-defect O7b shows the meaning does not come from it.
* **T3. A shared arena is the lock invariant ONLY; it is NOT a `D.invs` member.** `Deklaration.invarianten_gehalten` (U003 as a declaration
  fact) says: a function whose signature writes a carrier of an invariant holds EVERY guard lock of every carrier in its signature
  (`haelt`). The realistic shared shape is `g := locks L { f(); }` (finding 3 of 8a.2): `g` writes the arena through `f` but takes `L`
  itself, so `L ∉ haelt g`; with the arena as a `D.invs` member `invarianten_gehalten` would forbid exactly the program the section
  theorem covers [U: read from the field text and the 8a.2 finding; not run]. Decision 2 already says "shared via the lock invariant";
  this entry records that it is also a REQUIREMENT. Per-thread (unguarded, thread-local) arenas are `D.invs` members and are the only ones
  decision 1's footprint concerns. A shared arena needs no new text in `Spec.lean`: `sperrInv`, `sperrWechsel`, `sperrSicht` already say it
  for the user's lock family `E.S`; the new content is the section certificate (O17) and that the certificate's statement forces `E.S = K.sperr L0`.
* **T4. A flag invariant is not a `D.invs` member either.** The payload is written BEFORE the publish, so an `InvRuhe`-style claim ("holds
  whenever no thread is inside a writer", hypothesis: holds at the start memory) is false or vacuous for it. It is a hand-off invariant
  (publisher duty at the `publish` step, reader's rely after the confirmed `awaits`), the structural twin of a lock invariant (duty at
  the release, rely at the acquire). It rides in the same family: new defaulted fields of `SperrInv` (A.3, C9). Its payload carriers are
  exempt from `VertragsFrei` for their OWN flag only (A.4).
* **T5. The statement runs over `D.mitRuhe`.** `GabbroZiel` ends in `ZielFX E.P.mitRuhe E.S.mitRuhe …` over `D.mitRuhe` [V: Spec.lean
  2295], whose `typ`/`gtyp` are `tyR` of the old ones and whose `Fn` is `Option D.Fn` [V: MitRuhe.lean 150-200]. Every new field of
  `Deklaration` needs a `mitRuhe` line, and the arena needs a translation `Dekl.mitRuhe` with `Dekl.Ok (worldR σ) ↔ Dekl.Ok σ`
  (O6). Not in either earlier text.
* **T6. The entry fact needs a joint induction (the cost 8a.3's D5 understated).** `InvGutS` quantifies over EVERY world meeting
  `ReqAmEintritt`. `erkE_koerper` gives `Dekl.Ok` at exits only from a world that meets it at entry, and a body started in a broken
  arena may fail the `rufAt` check, i.e. answer `logik`. So (b) for an arena invariant must carry the entry assumption (the inductive
  reading of decision 2: `InvGutSE`, O9). The replay that proves `invRueck` applies the user obligation at the world of every call, so
  it needs the entry fact there, while `invRuhe` (the only source of that fact) needs the replay's returns (`hIR`
  in `invRuhe_erreichbar` [V]): a circle. It is broken by one joint induction over reachable machines (O10), not by the proof
  structure as it stands. For a per-thread arena written by one start (`Getrennt`) the entry fact at a call by a thread outside every
  owing frame IS `invRuhe` at the previous machine; inside a writer frame it is the abstract state of the recognizer
  (needs the call constructor, T7). `invGutSD2_arena`'s premise `hein` is exactly this fact.
* **T7. `ErkE` covers only leaf writers: callers and section owners have no derivation.** `Erk` has no call constructor and no `locks`
  constructor [V: 8a.1 "Still open"]. `schuldet` is derived from transitive effects, so a function that merely CALLS a writer owes the
  invariant too and needs its own certificate; likewise `g := locks L { f(); }`. Soundness of the diff is NOT affected (an uncertifiable program
  just cannot satisfy the premise and is outside the statement; it is never unsoundly inside), usability is: a program with nested writers
  cannot instantiate the theorem until O14/O15 exist. Named in the header and in the NOT CLAIMED list.
* **T8. Decision 3's order premise narrows a universal; the choice of how far is open.** `SchwachX` quantifies `∀ ord`. Restricting
  `ord` at ALL flags with a payload (derived order) is the simplest and matches the language (`publishes` forces release, LANGUAGE 11.1);
  it removes from the statement the (absurd) lowerings of an unraced payload flag as relaxed, and `GabbroZielSC` can then no longer
  be derived from the order-restricted `SchwachX` for such units, only from the direct proof `Beweis.lean` already contains
  (`gabbro_ziel_sc` [V: header, Beweis.lean]). Restricting only at `PubFlagge` (flags of a RACY payload, vacuous elsewhere) loses
  nothing. The plan takes the second (no unit and no run covered today is dropped), with the derived order `D.ordnung` as its content.

#### A. The merged edit list

**A.1 `Kern/Syntax/` (a ROOT change: every one of the 714 modules rebuilds; do all of it once).**

| # | Edit | Where | Fallout |
|---|---|---|---|
| A1.1 | New `Kern/Syntax/Basis.lean`: `structure DeklBasis` = `Tab`, `[decTab]`, `count`, `Feld`, `[decFeld]`, `typ`, `Glob`, `[decGlob]`, `gtyp`; `attribute [instance] DeklBasis.decTab …` | new | the `attribute [instance] Deklaration.decTab …` line at `Syntax.lean` 183 moves; instances then resolve through the parent projection **[M]** |
| A1.2 | New `Kern/Syntax/Arenen.lean`: the STRUCTURES `ArenaForm`, `DynForm`, `FreiForm`, `LinkFeld`, `LinkKopf`, `ListDekl`, `BaumDekl`, `Dekl` over `DeklBasis`, plus `Dekl.lesGlobs`, `Dekl.orte` (def only; both mention only structure fields [V]) | moved declarations: `ArenaZucker` 106, `ArenaDyn` 271 (namespace `ArenaDyn` renamed at its uses), `ArenaFrei` 46, `ArenaListe` 38/46, `ArenaDekl` 29-47, `ArenaSperreTraeger` 30/35 | their readers (`stand`, `komSt`, `wert`, `st`) need `World`/`Wert.umTyp` and STAY in `Bausteine/Arena/`; `Wert.umTyp` is not needed by the structures **[U: re-check at the spike]** |
| A1.3 | `Deklaration extends DeklBasis` (the six fields leave the list at line 111); `CoeOut Deklaration DeklBasis` | `Syntax.lean` 111-208 | 0 literals break (`where` syntax, 84 of them); `{ D with … }` forms unaffected **[U]**; the lemma statements `(A : FreiForm D)` elaborate through the coercion **[M, mock only]** |
| A1.4 | New field `arena : Inv → Option (Dekl toDeklBasis) := fun _ => none` (needs `FreiForm`, so after `Inv`) | `Deklaration` | default: every old declaration keeps its meaning; `Deklaration.mitRuhe` gets `arena := fun i => (D.arena i).map Dekl.mitRuhe` (T5) |
| A1.5 | The old list field becomes `traegerFrei : Inv → List (Tab ⊕ Glob)` (carriers of an EXPRESSION invariant); `def Deklaration.traeger i := (D.arena i).elim (D.traegerFrei i) Dekl.orte` | `Deklaration` | 85 lines say `traeger := …` [V]; 79 are `nomatch`/`.elim`/`[]` and only need the rename, three list tables (`InvZeuge` 99, `MehrfadenZeuge` 116, `ZielOrtInvGrundZeuge` 92) and need `.inl`, `MitRuhe` 179 copies the field, `Extraktion/T1` 379 and `Geteilt` 358 belong to the unrelated `Bau` structure [V]. EXPORTER: `lean_g.rs` 5541 writes `traeger := fun e => nomatch e`: one line, same commit (A.9) |
| A1.6 | `invarianten_gehalten` restated over `Tab ⊕ Glob`: `(traeger i).any (Sum.elim (sigNr n).schreibt (sigNr n).gschreibt) = true → ∀ c ∈ traeger i, ∀ L, Sum.inl L ∈ (Sum.elim braucht gbraucht c) → L ∈ (sigNr n).haelt` | `Deklaration` | the exporter writes `fun _ i => nomatch i` (lean_g.rs 5594), still valid; 84 fixtures prove it by `nomatch` [U: spot-checked, not all]; `MitRuhe.lean` 196 follows; used in `Satz/T4` 431, `AtomarInv` 32, `Interferenz` 162 |
| A1.7 | `D.nutzlast : Glob → List (Tab ⊕ Glob)`; `Stmt.publish` and `Block.awaits` payload parameter `List (D.Tab ⊕ D.Glob)` (the equation `payload = D.nutzlast g` is unchanged) | `Syntax.lean` 131, 520-521, 573-574 | mirrors: `Hoare/HoareRegeln/T1` 110/142, `Satz/T1` 179-184, `Code/Conc/Await`, `CFormenH`, `PaarungAusgenommen` (`InterferenzAllgemein/T1` 615); literals with a non-trivial `nutzlast` are few (`AtomarZeuge` and kin) [U: count at the spike] |
| A1.8 | `invSicht i` (line 647) folds `Sum.elim braucht gbraucht` over `traeger i` | `Syntax.lean` 647 | `Programm.invariante : Expr D [] (invSicht D i) .bool` keeps its type; for an arena name the value is ignored (T2) |
| A1.9 | NOT edited: `Programm` (no new field), `Einheit` (no new field), `Programm.mitRuhe` | | the 80 `Programm` literals and the 47 files that mention `Einheit` are untouched |

**A.2 `Kern/Semantik/` and the arena base.**

| # | Edit | Where |
|---|---|---|
| A2.1 | `schuldet f i := (D.traeger i).any (Sum.elim (D.schreibt f) (D.gschreibt f))` | `Semantik/T1.lean` 478 |
| A2.2 | New Kern module `Semantik/ArenaPruef.lean` (between `T1` and `T2`): `Dekl.okB : Dekl A → World D → Bool` by fuel-bounded walks (free list, list, tree preorder with `Nodup`, disjointness) over `World` readers | new |
| A2.3 | `rufAt` check: `invPruef P i σ' := (D.arena i).elim (wahr? (eval σ' (P.invariante i) σ' .nil)) (fun K => K.okB σ')`; the read recording uses `P.invariante i`'s `orte` for `none` and `K.orte` for `some` (guarded by `invSicht D i`, which holds by A1.8) | `Semantik/T2.lean` 397-399 |
| A2.4 | consumers of the old check (30 files [V: 14 `RufLogik`, 6 `RufAtNachB`, 14 `MitRuheSemantik/T3-T4`, 19 `Extraktion/T3-T4`, 8+4 `CFormenR/M`, `RahmenTreu`, `HandlerKongruenz`, `VertragOrtB`, `ObjektRahmen/T2` …]) restated through `invPruef`; each lemma has a `none` case that is the old proof | listed files |

**A.3 `Nebenlaeufigkeit/Sperren/SperreSem/T1.lean` (`SperrInv`) and the H-semantics.**
`structure SperrInv` gains two DEFAULTED fields (stage P2, flag invariants):
```
+ pub    : D.Glob → Speicher D → Bool := fun _ _ => true      -- the hand-off invariant of the flag `g`
+ pubOrte : D.Glob → List (D.Tab ⊕ D.Glob) := fun g => D.nutzlast g  -- derived, not listed by hand
```
`execBlockH`/`execBlockHA` get a `publish` case beside the lock-release check: the publisher's world after the store must satisfy
`S.pub g`, else `logik` (the twin of `freiH_post`). The family `Block/Endblock.execH_ohne` ("a body without `locks` runs the same under
`execBlockH`") gains the matching premise (no `publish` with a failing `S.pub`; with the default family it is the old lemma). `SperrInv.mitRuhe`
(`⟨S.orte, fun L s => …⟩`, an ANONYMOUS constructor [V]) becomes a record literal. Literals of `SperrInv` that use `⟨_, _⟩` break: count
at M2 **[U]**.

**A.4 `Spec.lean`: the exact edits, in file order.** (No text of `GabbroZiel`, `GabbroZielSC`, `GabbroZielVerbund` changes: they quantify
over the structures edited below.)

* **C1 `InvTraeger`** (line 1922). The arena reads exactly `K.orte` (`Dekl.ok_gleich_wort`, a THEOREM), the expression invariant reads its list:
  ```
  def InvTraeger (P : Programm D) (i : D.Inv) : Prop :=
  - ∀ c ∈ (P.invariante i).orte, ∃ t ∈ D.traeger i, c = Sum.inl t
  + match D.arena i with
  + | none => ∀ c ∈ (P.invariante i).orte, c ∈ D.traeger i
  + | some _ => True
  ```
* **C2 `InvHaelt`** (`ZielOrt/Rahmen/ZielOrtInv.lean` 41, not `Spec.lean` but part of the reviewed diff, the statement mentions it):
  ```
  def InvHaelt (P : Programm D) (i : D.Inv) (σ : World D) : Prop :=
  - wahr? (eval σ (P.invariante i) σ .nil) = true
  + invPruef P i σ = true            -- `Dekl.okB` for an arena name, the evaluation otherwise (A2.3)
  ```
  `InvHaeltD2` of `ArenaSperreInv.lean` (the compiled proposal) is deleted afterwards (no legacy); its lemmas are restated over `InvHaelt`.
* **C3 `InvRuheG`** (1939): the start hypothesis is dropped for an arena name, because (b) now proves it (C4):
  ```
    ∀ i ∈ D.invs, InvTraeger P i →
  -   InvHaelt P i (M0.speicher.welt []) → InvZu M i → InvHaelt P i (M.speicher.welt [])
  +   (D.arena i = none → InvHaelt P i (M0.speicher.welt [])) → InvZu M i → InvHaelt P i (M.speicher.welt [])
  ```
  Same edit in `InvSichtG` (1946), whose guard clause becomes
  `∃ c ∈ D.traeger i, ∃ L, Sum.inl L ∈ Sum.elim D.braucht D.gbraucht c ∧ L ∈ offen (M.faeden t).spur`. For an expression invariant (`arena = none`)
  both legs are word for word the old ones when `traeger` lists only tables (the case today).
* **C4 `StartPflicht`** (1665): one more clause, the start obligation of decision 2:
  ```
  structure StartPflicht (E : Einheit D) : Prop where
    sperren : ∀ L, E.S.inv L E.sp0 = true
    req : …
  + arena : ∀ i K, D.arena i = some K → InvHaelt E.P i (E.sp0.welt [])
  ```
  Its proof for a closed `sp0` is `by decide` through `okB` (O5 gives the decision procedure); for `arena := fun _ => none` it is vacuous (an
  `autoParam` default `by intro i K h; simp at h` is the plan **[U]**; fallback: edit the 14 files that build a `StartPflicht` [V:
  `GvAtomRely`, `GvLuecken`, `GvStartPflicht`, `Pflicht104/108`, `GenOblig104/108`, `Beweis`, `SpecProben`, `Akzeptiert`, `FaedenVor`, `Proben`,
  `ZeugeTorModell`]). `StartPflichtVor` (`FaedenVor` 42) and `startZulaessig_aus` take the clause along.
* **C5 `SchwachX`** (2200): the order premise of decision 3, derived, vacuous without a racy payload:
  ```
  + /-- The orders a lowering may choose for the flags of a racy payload: at least the DERIVED order of the declaration. -/
  + def OrdAb (P : Programm D) (ws : List D.Fn) (ord : D.Glob → Speichermodell.Ordnung) : Prop :=
  +   ∀ g, PubFlagge P ws g → D.ordnung g = .freigabe → ord g = .freigabe
    def SchwachX … (Tg …) (M0 M) : Prop :=
  -   ∀ ord W W' u σ M'' wahl neu, RufErreichbarW … ord …
  +   ∀ ord, OrdAb P ws ord → ∀ W W' u σ M'' wahl neu, RufErreichbarW … ord …
  ```
  `SchwachX`/`ZielX` get the parameter `ws` (the declared starts; today they get `Tg := GeteiltV P ws`, from which `ws` is not recoverable).
  `Deklaration.ordnung g := if (D.nutzlast g).isEmpty then .entspannt else .freigabe` is a DEFINITION in `Speichermodell/Maschine/MaschineW.lean`
  next to `ordVon` (not a field: the language derives release for every flag with a payload, LANGUAGE 11.1/11.5). `PubFlagge P ws g :=
  D.atomar g = true ∧ ∃ c, c ∈ D.nutzlast g ∧ PubLesbar P ws c`.
* **C6 `AkzeptiertSpecX`** (2109): one new field and two changed ones, for payload carriers only (this is `PubRegel`, §11.4 R0-R4):
  ```
  + pub  : PubRegel P fs ws                       -- R0-R4, decided by the new component `pubB` (A.5)
    fuss : ∀ f, FussSX P S (lokW P fs ws) (GeteiltV P ws ∪ PubLesbar P ws) f   -- a payload READ is no longer refused at `fuss`
    renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → ¬ PubLesbar P ws c → SchreibGetrennt P fs ws c
  ```
  `PubLesbar P ws c`: plain, unguarded, in `D.nutzlast f` of ONE flag `f`, `VertragsFrei` except for `f`'s own flag invariant, written by ONE declared
  start that is not `Mehrfach`. `PubRegel` (one-shot first cut): single writer; on every path of that start's call graph (callees and loops
  included) every write of `c` is followed by the unique `publishes f` and by NO later write of `c` (`hstill`); `f` has one `publishes` site
  and a published value its initial value does not carry (`hnicht`); `rueck f = none` (the one-shot rule, A.6); every read of `c` in another
  start's graph is dominated by a confirming `awaits f` branch on every path. The order is not a field of `PubRegel`: it is `D.ordnung`.
* **C7 `NutzerPflichtA`** (2152): the rely set grows by the payload carriers (stage P1) and the unit carries the arena certificate:
  ```
    structure NutzerPflichtA (E : Einheit D) : Prop where
  -   logik : LogikPflichtA E.P E.S E.Q (GeteiltA E.P E.ws)
  +   logik : LogikPflichtA E.P E.S E.Q (fun c => GeteiltA E.P E.ws c ∨ PubLesbar E.P E.ws c)  -- reader: payload constrained by `S.pub` (stage P2)
      start : StartPflicht E
  +   arena : ArenaZeuge E            -- O14-O17, stage 1 of decision 2's certificate; moves to (a) with `ErkB` (O18)
  ```
  `LogikPflichtA`'s `InvGutSA` is restated for owed ARENA invariants as `InvGutSE` (entry assumption, O9); the user does not prove arena
  preservation by hand, `ArenaZeuge` carries `ErkE` (per-thread, per owing function) or the section certificate (shared, per `locks` statement).
  `KoerperGutSA`'s havoc at a confirmed payload read is `HavocPub` (O22): every value in `S.pub g`'s payload, no longer every value. Stage P1 is
  `S.pub := fun _ _ => true`.
* **C8 `ZielX` and `ZielFX`** (2218, 2254): ONE new leg, the view-level race freedom of a payload carrier (§11.3 D4, now over `OrdAb`):
  ```
  + pubSicht : PubSicht P O passes ws M0 M
  def PubSicht … := ∀ ord, OrdAb P ws ord → ∀ W W' u σ M'' wahl neu, RufErreichbarW … → W.g = M → SchrittW … →
      ∀ c, PubLesbar P ws c → (LiestG … ∨ SchreibG …) → ∀ m ∈ W.hist c, m.ts ≤ W.sicht u c
  ```
  `ZielFX.spawnSicht` already lists `InvRuheG` and takes the C3 change for free. `Ziel`/`ZielF` (the G statements) get NO new leg; they are
  the corollary `gabbro_ziel_sc_aus` (T8). `rennfrei` becomes `RennfreiBisGA` with the `PubLesbar` exemption, `¬ AtomarAusgenommen c → ¬ PubLesbar … c →`.
* **C9 `SperrInv`** (A.3): `pub`, `pubOrte` as above. `SperrInvLokal S` gets the twin clause (`S.pub g` reads only `S.pubOrte g`).
* **C10 `Einheit`**: no change (`S` carries the hand-off family). **`Einheit.ws`** unchanged.
* **C11 `Pruefer` / `PrueferX`**: the structure text is unchanged (its `korrekt` targets `AkzeptiertSpecX`); `Pruefer.alsX` and
  `akzeptiertX_pruefer` are re-proved for the new field.
* **C12 `GabbroZielVerbund`** (2486) and `NutzerTeilA`/`SchnittstelleSpec`: the arena certificate and `PubRegel` are per OWN function of each unit;
  a payload flag or an arena invariant ACROSS the link stays NOT CLAIMED and refused (`lok`), as an atomic across the link is today.

**A.5 `Zielsatz/Kern/Akzeptiert.lean` and `Atomar/AtomarAkzeptiert.lean` (the concrete Lean checker).** New component `pubB : Bool` with
`pubB_iff : pubB P fs ws = true ↔ PubRegel P fs ws` (a syntax-directed walk over `Endblock` with an abstract state "flags confirmed" and
"payload written since the publish", the same pattern as `Abs` of the recognizer, closed by the call fixpoint `reachB`); `AkzeptiertX` gains it
and `akzeptiertSpecX_of` its case. Stage 1 of the arena certificate is NOT in (a); at the target stage a component `arenaB : Bool` (decided by
`ErkB`, a Bool recognizer with `erkB_sound`, O18) moves `arena` from `NutzerPflichtA` into `AkzeptiertSpecX`.

**A.6 Re-publication anticipated (decision 3), first cut one-shot.** Hooks only, no semantics beyond one-shot:
(i) `SperrInv.pub g` and `PubFlagge` speak of the MESSAGE the confirming read returned, not of "the" publish (`erwartet_bestaetigt` already does);
(ii) `PubRegel` carries `rueck : D.Glob → Option D.Glob := fun _ => none` (the reverse flag) and the first cut demands `none`; the later rule
replaces `hstill` ("no write after the publish") by "no write between the publish and the reader's ack of THAT epoch" (an interval of the
flag's history, `StillBis c m_pub m_ack`, with `m_ack = ∞` in the first cut); (iii) the flag value carries an epoch number only at the later
stage (`D.epoche : Glob → Nat := fun _ => 1` is a reserved name, not added now); (iv) `payload_mp_wert` is stated per message, so the
epoch generalisation is an instance, not a rewrite **[U: reread the proof at O21]**. A ring or a Treiber stack (item 5) is the first user.

**A.7 `Nebenlaeufigkeit/Sperren/MitRuhe*.lean`.** `Deklaration.mitRuhe` (the field list at 150-200): `arena`, `traegerFrei`; `nutzlast := D.nutzlast`
unchanged in type; `SperrInv.mitRuhe` carries `pub` (translated back through `speicherZ`); `Programm.mitRuhe` unchanged. New: `Dekl.mitRuhe`,
`Dekl.ok_mitRuhe` (O6), `okB_mitRuhe`. The existing `invHaelt_mitRuhe`-type lemmas gain the arena case.

**A.8 Header text of `Spec.lean` and NOT CLAIMED (exact places, from the file).**
* Atomic-rely block, line ~185-187, "WHAT STAYS NAMED … hand-off of a PLAIN payload read without a lock (still refused, verdict P3; OFFEN O25's
  remainder)": REPLACED by: the one-shot hand-off of a plain payload (or table) read after a confirming `awaits` IS claimed (leg `pubSicht`, premise
  `OrdAb`, component `pub`); the reader's rely is the flag invariant `S.pub` (stage P2) or, named as the intermediate stage while P2's proof is open,
  every value (P1). The P3 remarks (lines ~854-861) get "UNGUARDED payload across threads is refused" replaced by the `PubRegel` conditions.
* Invariant block, line ~329 ("THE GAP") and ~412 ("an invariant reading carriers outside `D.traeger`"): `D.traeger` is computed for an arena;
  an arena invariant is established by `StartPflicht.arena`; `InvTraeger` is a theorem for it.
* Assumption (2) of the reading (the emitters lower atomics with the orders the declaration derives): add "load-bearing for the flag of a racy
  payload: `D.ordnung g = freigabe` is the lowering's lower bound".
* NOT CLAIMED, line ~1362: the entry "a table/group invariant … one that is false in the start memory (the start is the legs' hypothesis, not a
  (b) duty)" gets "except an ARENA invariant, whose start memory is (b)'s duty (`StartPflicht.arena`)"; the entry "the publish/await hand-off of
  an unguarded PLAIN payload (refused by the checker, see P3; …)" is REPLACED by the F-list below; the entry "DYNAMIC UNBOUNDED DATA STRUCTURES
  …, OFFEN O29" and the paragraph "NOT this case: an `arena A capacity lo .. hi max M of T`" (lines ~1437-1462) shrink to the F-list below.

**A.9 Rust (the only line).** `crates/gabbro-check/src/lean_g.rs` 5541: `traeger := fun e => nomatch e` becomes `traegerFrei := fun e => nomatch e`,
in the SAME commit as M2, so `pruefe-pruefer.py` (which builds exported Lean) stays green. Nothing else in `crates/` changes in this diff: the
exporter still writes `Inv := Empty`, `LG001`/`LG005` stay; lifting them is plan step 5 and needs the diff applied and both verdicts.

#### B. Lean proof obligations the diff creates, in dependency order

Every row needs: no `sorry`/`native_decide`/new `axiom`; `#print axioms` on the new theorem and on `gabbro_ziel` exactly `propext`,
`Classical.choice`, `Quot.sound`; a witness on a NON-DEGENERATE fixture (`Zeugenpflicht`) and a planted defect the model rejects.
"Exists" = [V] in the tree today.

| # | Statement | Lives in | Discharged by | Witness | Planted defect |
|---|---|---|---|---|---|
| O1 | `Deklaration extends DeklBasis` builds; every theorem of the tree compiles unchanged in meaning | Syntax, ~60 Arena files | refactor; build | `d0` shape **[M]**; a real arena fixture (`FD` re-stated) | none (pure refactor); `#print axioms gabbro_ziel` identical to the pre-refactor print (recorded at M0) |
| O2 | `traeger_arena : D.arena i = some K → D.traeger i = K.orte` and `traeger_frei` (both `rfl`) | `Syntax/Arenen` | by definition | a fixture whose `traegerFrei` lists junk for an arena name: `traeger` ignores it | a declaration that cannot list `komm` by hand any more: the bug class "footprint listed wrong" is unrepresentable; test is `traeger_arena_unabhaengig` |
| O3 | `schuldet` over `Tab ⊕ Glob`: `schuldet_pop`: a function whose only effect writes the list head owes the arena invariant (finding 1 of 8a.2) | `Semantik/T1`, `Interferenz` (`schuldet_hat_schreibtraeger` restated) | O2 + definition | `pop` body of `ArenaErkZeuge*` (a head-only writer) owes `i` | the same function under the OLD `schuldet` (tables only) owes nothing: `pop_alt_schuldet_nicht` documents what is repaired |
| O4 | `invarianten_gehalten` over `Tab ⊕ Glob`; proofs of the three consumers (`Satz/T4` 431, `AtomarInv` 32, `Interferenz` 162) | `Syntax`, those files | existing proofs generalised | an arena fixture whose writer holds the guard locks | a writer without the lock: the field is unprovable (`invarianten_gehalten_verletzt`) |
| O5 | `Dekl.okB` (Kern) and `okB_iff : K.okB σ = true ↔ K.Ok σ`; `okB` decides `Ok` on a closed world by `decide` | `Semantik/ArenaPruef`, `Struktur/Erkenner/ArenaOkB` | NEW: fuel-bounded walk is sound and complete for `KetteF`/`BaumF`/`FreiOk`; completeness needs the fuel bound `count` (the chain visits distinct slots below `count`: `Nodup` ⇒ length ≤ `count`) **[U: the hardest of the Kern pieces]** | `okB w0 = true` (the four-slot arena of `ArenaDynZeuge`), by `rfl` | `okB` false at the worlds of `liste_defekt_bricht`, `doppelGlied_abgelehnt`, a cycle |
| O6 | `Dekl.mitRuhe`; `Dekl.ok_mitRuhe : K.mitRuhe.Ok (worldR σ) ↔ K.Ok σ`; `okB_mitRuhe` | `Nebenlaeufigkeit/Sperren/MitRuhe*` | NEW; reads only ints through `Wert.umTyp` and `tyR (Ty.int a b) = Ty.int a b` **[U]** | the arena fixture under `.mitRuhe` | an arena whose `hz` proof would not survive `tyR`: not representable |
| O7 | `invPruef`; `rufAt` check restated; every consumer lemma (A2.4) keeps its statement for `arena = none` | `Semantik/T2` + 30 files | the old proof is the `none` case; new `some` case from O5 | `rufAt` on the arena fixture returns `ok` after a recognized body; **O7b** returns `logik (.invariante i)` after the planted `stray` store (reuse `stray_bricht`) | `P.invariante i := fun … => tru` for an arena name: the check still fires (`invariante_ignoriert`) |
| O8 | `InvHaelt` (C2) with `invHaelt_speicher` (reads only `σ.speicher`); `InvTraeger` for an arena is trivial and `ok_gleich_wort` gives the reads-only fact the leg needs | `ZielOrtInv`, `ArenaSperreTraeger` | `ok_spur`, `ok_gleich_wort` exist | as O7 | n/a |
| O9 | `InvGutSE`: `InvGutS` with the entry assumption for owed arena invariants; `invGutSE_arena`: from `ErkE K Abs.leer (P.rumpf f)` | `ZielOrtInv`, `Struktur/Sperre/ArenaSperreInv` | `invGutSD2_arena` (exists, takes `hein`); restated with `hein` as part of the hypothesis | `erk_nimmPush`-type body | a body whose derivation is missing (`stray_abgelehnt`) |
| O10 | **Joint induction** `arena_eintritt`: on every reachable machine, at every call entry of an owing function by thread `u` whose other frames are not owing, the memory meets `Dekl.Ok`; proved together with `invRueck`/`invGrund` (T6) | NEW `Zielsatz/Arena/ArenaEintritt.lean` | the induction of `invRuhe_erreichbar` with the replay (`ziel_ort`) as the other conjunct; per-thread uniqueness of the writer from `lokW`/`Getrennt` (`schritt_traeger` for the other threads) **[U: scope 600-1500 lines; the largest proof of the diff]** | the machine run of `erkE_maschine_zeuge` extended to two calls | a program whose first call enters a broken start memory: rejected by `StartPflicht.arena` (`start_defekt_abgelehnt`) |
| O11 | `invRuheG_aus`/`invSicht_aus` over `Tab ⊕ Glob` carriers and the dropped start hypothesis | `Eigenschaften/Invarianten.lean` 205-350 | the block `hgl` (205+ lines [V]) split by `Sum` case: tables by `schuldet`, globals by `gschreibt`; arena by `ok_gleich_wort` | an arena unit: `invRuhe` concludes `Ok` at a closed machine | closed-set violated: a thread inside a writer (the claim is not made: `invRuhe_nicht_im_schreiber`) |
| O12 | `StartPflicht.arena` is discharged for the declared `sp0` by `okB`; `startZulaessig_aus` and `FaedenVor` take the clause | `Zielsatz/Kern/Beweis`, `FaedenVor` | O5 + `decide` | `sp0` of the fixture | `sp0` with a head `0` (a valid slot, not `nil = count`): `startPflicht_arena_falsch` |
| O13 | Section for a shared arena: `locks L0 { … }` with `L0`'s family `K.sperr L0` | exists (`abschnitt_erk`, `abschnitt_rufe`, `arena_ziel`) | none new | exists (`abschnitt_zeuge`, `abschnitt_rufe_lauf`) | exists (`stray_bricht`, `abschnitt_defekt_schleife`) |
| O14 | `Erk.ruf`: a call constructor, soundness by induction on call depth through `rufAt_erk` (T7) | `Struktur/Erkenner/ArenaErkRuf` | `rufAt_erk` (exists, one level); new induction on `rufTief` | a writer that calls a recognized helper | a call to a function with no derivation |
| O15 | `Erk.sektion`: `locks L0 { Rufe }` and the inline form as constructors, soundness by `abschnitt_rufe`/`abschnitt_erk` (T7) | same | `abschnitt_*` (exist) | `g := locks L { f(); }` as an owing function | `f` not requiring `L` |
| O16 | `ArenaZeuge E`: per-thread arena: every `f` with `schuldet f i` has `ErkE`; shared: every `locks L0` statement body of a function is recognized and `E.S = K.sperr L0`; `ArenaZeuge E → InvGutSE …` | `Zielsatz/Arena/ArenaZeuge` | O9, O13-O15 | the fixtures | `E.S` not `K.sperr L0`: `arenaZeuge_andere_sperre` |
| O17 | `Dekl.sperr` section certificate over a statement walk (`Endblock.locksAlle`) | same | NEW syntax walk like `schleifenfrei` | as O15 | a section on another lock |
| O18 | TARGET stage of the certificate: Bool `ErkB`, `erkB_sound : ErkB K a b = some a' → Erk K a b a'`, loop states by a monotone fixpoint over the finite `Abs` lattice; then `arena` moves from `NutzerPflichtA` into `AkzeptiertSpecX` | `Struktur/Erkenner/ArenaErkB`, `Akzeptiert` | NEW **[U: the second-largest piece; `Erk` has loop-state constructors that guess `k0`, a decision procedure must iterate]** | the accepted fixtures return `some` | the rejected fixtures return `none` |
| O19 | `D.ordnung`, `OrdAb`, `PubFlagge`; `SchwachX` restated; the embedding "old `SchwachX` ⇒ new" (instantiation) and, for a unit with no `PubLesbar`, the equivalence | `MaschineW`, `Spec`, `Atomar/AtomarPflicht`-style embedding file | instantiation of a universal (easy) | a flag with payload, `ord` = release | `ord` relaxed at a racy flag: `OrdAb` fails, the counter-models `mp_flagge_*_erlaubt` apply |
| O20 | `PubLesbar`, `PubRegel`, `pubB` and `pubB_iff`; `fuss`/`renn` exemptions in `AkzeptiertSpecX` | `Atomar/AtomarAkzeptiert*`, new `Atomar/PubRegel.lean` | NEW walk (R1 `hstill` through callees and loops, R3 dominance with branch facts) | `PubRegel` holds for the first fixture | the five counter-models of 11.1 as five programs the rule refuses: write after publish, read before await, relaxed flag (`ordnung` is derived, so this one is refused by `renn`'s premise), two writers, two publish sites |
| O21 | Frame invariant `Merkmal.erwartet` (the confirming branch fact holds at the read, nobody wrote the flag since); `schritt_sichtInvA` extended with the payload disjunct; `pubSicht` for every reachable machine of GX | `Atomar/AtomarSichtPub` | `payload_mp`, `payload_mp_wert`, `payload_schreib`, `gesehen_einzelschreiber`, `still_of_kein_schreiben`, `erwartet_bestaetigt` (all exist, §80) | the first fixture's two-thread run (about five G steps, the scale of `w_nicht_sc`) | the rewrite-after-publish program: `pubSicht` fails there and `PubRegel` refuses it |
| O22 | `HavocPub`: at a confirmed payload read the environment answers a value the flag invariant allows; stage P1: any value; stage P2: `S.pub g`; the publisher's duty is the `publish` hook (A.3) and `execH_ohne` family restated | `Speichermodell/Atomar/AtomarSem` + `SperreSem` | NEW; mirrors `HavocOk`/`freiH_post` | a publisher that establishes `Φ` and a reader that uses it | a publisher that does not: the hook answers `logik` (`pub_defekt_schleife`) |
| O23 | The replay instantiation of `LogikPflichtA` for `T := GeteiltA ∪ PubLesbar` (the residue lemmas `ziel_ort_atomar_voll`, `AtomarReplay/T1-T3`) | `Atomar/AtomarReplay*` | if they use only "`T c` ⇒ `VertragsFrei c` and unguarded" it is a re-instantiation, otherwise the largest single cost of decision 3 **[U: read at M9]** | as O22 | n/a |
| O24 | `gabbro_ziel_sc_aus` and `gabbro_ziel` re-proved; `gabbro_ziel_sc` direct (`Beweis.lean`) kept | `Beweis`, `BeweisAtomar` | all of the above | the standing witnesses | `#print axioms` check in the guardian |
| O25 | First applied witnesses: one per-thread arena unit (`Inv := Unit`, `arena := some`, `invs := [()]`, a writer, a start memory) AND one racy-payload unit (a declaration, two bodies, ~5 G steps; the "first witness of the applied diff" 11.1 promised) | `Zielsatz/Kern/SpecProben*`, `AkzeptiertZeuge` | the diff itself | both units reach `Ziel` conclusions with CONTENT (`invRuhe` names `Ok`; `pubSicht` names a payload) | the unit of O7b and the rewrite-after-publish unit |

Planted-defect rule for the review (E): every row's defect is a PROGRAM or DECLARATION that the model rejects (theorem `…_abgelehnt` or
a run that ends `logik`), not a comment.

#### C. Migration order (green at every commit, `gabbro_ziel` on exactly the three axioms)

A commit is green when `./instrumente/pruefe-lean.py` is (it runs `lake build`, the axiom print and the layout check) and, for the
commits that touch the exporter line, `pruefe-pruefer.py` too. Heavy runs one at a time, `free -g` beside them, `cargo test` never in the
tree while `lake` runs.

| Step | Content | Rebuild | Green because |
|---|---|---|---|
| M0 | Baseline (documents only): `lake build` cold time and peak RAM, `#print axioms gabbro_ziel`, counts of the literals named above | 1 cold build, measured | nothing changed |
| M1 | **Spike, not committed**: A1.1-A1.3 only (`DeklBasis`, `Arenen`, `extends`, the coercion) in a scratch worktree, building the closure of `ArenaDekl` then `Grammatik` | full | decides T1: success keeps the plan, failure falls back to R1 (Simon decides) |
| M2 | **FR-1, everything that touches `Syntax.lean`, in ONE commit**: A1.1-A1.9 (split, `arena` field with default, `traegerFrei` + computed `traeger`, `invarianten_gehalten'`, widened `nutzlast`, `invSicht`), the `mitRuhe` field lines, A2.1 (`schuldet`), the three table fixtures, the exporter line | full (714) | every old unit has `arena := none`, tables-only footprints and `nomatch` payloads: each theorem is its own special case; consumers fixed in the same commit (~40 lines for `D.traeger`, `Interferenz`, `Satz/T4`, the `hgl` block of `Invarianten`) |
| M3 | **FR-2, Kern semantics:** A2.2 `okB` (definition only), A2.3 `invPruef`, A2.4 the 30 consumers; `okB_iff` NOT yet needed because no unit has an arena name in the corpus | full downstream of `T1` (~714) | for `arena = none` the check is the old one; the `some` branch is unreachable in every existing proof |
| M4 | O5 `okB_iff`, O6 `Dekl.mitRuhe`/`ok_mitRuhe`, O2/O3 witnesses, O8 | new files + dependents of nothing | additive |
| M5 | Arena obligations of the Spec diff: O9 (`InvGutSE`), O11, O12 as LEMMAS over the OLD `Spec.lean` (their statements mention `StartPflicht.arena`, which is not there yet: state them with the clause as a separate hypothesis) | partial (Zielsatz proofs) | additive; `Spec.lean` untouched |
| M6 | O10 joint induction (`arena_eintritt`), O14, O15, O16, O17 | new files | additive; this is the large proof, it can stall without turning the tree red |
| M7 | Payload Lean modules without `Spec.lean`: O19-O23 as lemmas over a copy of the legs, O25 payload witness | new files | additive |
| M8 | **THE `Spec.lean` COMMIT:** C1-C12, A.3, A.5, header text, the NOT CLAIMED edits, `gabbro_ziel`/`gabbro_ziel_sc_aus`/`Beweis` re-proved with the M5-M7 lemmas, `SpecProben` witnesses (O25 both) | Spec closure and dependents (~197 + ~120 [U]) | it applies lemmas that are already green; if O10 or O23 is not ready the commit takes the fallback stage named in B (arena: certificate premise with `ErkE` leaves only; payload: stage P1 havoc, named in the header as "the reader assumes nothing") and ships honestly |
| M9 | O18 `ErkB` (target stage of the certificate): `arena` moves from (b) to (a) (a SECOND `Spec.lean` diff, small, reviewed again) | partial | additive then a diff |
| M10 | Documents: `THEOREM-MAP`, `TODO`, this file, `SPRACHE` 11.5 rule text, `OFFEN` lists | none | texts |

`gabbro_ziel` keeps its three axioms because every new module is reviewed with `#print axioms` and the guardian prints it; nothing in this
plan adds an `axiom` or `Classical` beyond `propext`/`Classical.choice`/`Quot.sound` (the existing `Dekl.sperr` already uses `Classical.decide` [V]).

#### D. Rebuild cost

* Size [V]: 712 `.lean` files under `grammatik/Grammatik/`, 275,543 lines; `import Grammatik` pulls 714 modules; `Syntax.lean`'s own closure is 6, so
  an edit there rebuilds all of them; `Spec.lean`'s closure is 197 modules; `Dekl.Ok`'s is 68.
* Time [U]: the only whole-library figure in the records is 5 min 20 s at 6.86 GB peak for 247 jobs on `ki-pc-fisch-101` (2026-09-15,
  THEOREM-MAP §29) and 19 min 44 s for 226 jobs earlier (THEOREM-MAP lines 2646 and 2808). The tree has ~2.9 times the jobs; this
  machine has 20 cores and 31 GB (`free -g`: 20 GB cache). A linear guess is 15-40 minutes per cold full build. M0 replaces the guess.
* Number of full rebuilds the plan forces: **three** (M1 spike, M2, M3) plus the `Spec.lean` partial (M8) and its small sequel (M9). Splitting
  rule: (1) every `Syntax.lean`-level change goes into M2, reviewed as a diff BEFORE it lands, because a later correction costs another
  full rebuild; (2) develop each later step against its own closure target (`lake build Grammatik.Zielsatz.Kern.Spec`, or one module) and run
  `lake build Grammatik` only at the commit; (3) M4-M7 are additive modules with no dependents, so they rebuild only themselves and can
  proceed in parallel by two agents in their own worktrees (at most two Opus agents, each with a warm `.lake` and warm `programmlogik/.lake`,
  never two lakes in one tree); (4) M2 and M3 may be merged into one commit if a single full build is preferred over two, at the price of a
  bigger red window; the plan keeps them apart because the failure modes differ (types and instances vs the semantics of a check);
  (5) the RAM rule of CLAUDE.md stands: `lean-bau` only, one build at a time.

#### E. The two-independent-verdicts protocol (AGENTS.md section 1; applies to M8 and again to M9)

* **Reviewers:** one Muse lane and one Opus agent, each in its OWN worktree with its own warm `.lake`, neither seeing the other's output
  until both reports are filed. Both are told to ATTACK the diff (find an unsatisfiable premise, a free parameter, a vacuous leg, a unit the
  statement now drops, a unit it now wrongly includes), not to confirm it.
* **What each receives (identical packets):** (1) the exact `git diff master..branch` of `Zielsatz/Kern/Spec.lean`, `ZielOrtInv.lean`, `SperreSem/T1.lean`,
  `Kern/Syntax/*` and the new `Basis`/`Arenen`/`ArenaPruef`; (2) the rewritten header and NOT CLAIMED text; (3) `#print axioms gabbro_ziel`
  and the guardian output (`pruefe-lean.py`); (4) the list of every new definition and the position it is used in the statement;
  (5) the two applied witnesses (O25) and the planted-defect theorems of section B, as names to read, not as claims; (6) section A of this
  document as orientation. They do NOT receive: section F's claims, the author's own verdict, the migration log, or each other's text.
* **Questions both must answer in writing (each with a yes, a no or "found: …"):** is each new premise satisfiable on a non-degenerate unit
  (`StartPflicht.arena`, `ArenaZeuge`, `OrdAb`, `PubRegel`, `S.pub`)? Does any old unit lose coverage (the embeddings of B: O19, O24)? Is the
  meaning of an arena name fixed by the declaration and not by anything the exporter or the user writes (`P.invariante` of an arena name
  is ignored, O7b)? Does `D.traeger` for an arena equal `K.orte` by definition and does `schuldet` now count the `pop`-only writer (O3)? Is the
  flag order premise vacuous without a racy payload (diff of `SchwachX`)? Can a relaxed lowering of a racy flag still reach `Ziel` (it must not)?
  Does the NOT CLAIMED text say every gap of section F, and nothing claimed there is claimed in a leg?
* **What each reviewer also runs:** the planted-defect programs of section B (each must be rejected), `lake build`, the axiom print, and a
  counter-model hunt of their own on the new premises (the six earlier rounds found P1 unsatisfiable lock invariant, P2 free parameters, P3
  payload races, F1 out-of-range floats, G1 `einpassen`, W1 empty answer types: the same classes are the checklist).
* **Decision rule:** both "the goal with named gaps, no unnamed gap found" and the guardians green: merge, tag `milestone-…-spec-arena-payload`,
  push (after the key grep). One "found": a repair lane, then BOTH reviewers re-read the repaired diff (a repair is reviewed by the pair, not by the
  author). A reviewer may not be reused for the second verdict of the same diff.

#### F. What stays NOT CLAIMED afterwards

*Arena side.* A heap without a ceiling; recursive types; links across arenas; hash chains and the sibling demand until their recognizers exist
(`HashOk`/`SibOk` have executed forms, `Dekl` has no hash component); a walk that releases every slot of a revoked subtree; `leave`/`next` in loop
bodies; writers with loops in the MACHINE correspondence (`erkE_maschine` covers loop-free bodies; the big-step `erkE_koerper` covers loops);
until O14/O15, a writer that calls a writer and a caller of a writer (T7); the commit bound `stand ≤ komSt` in the lock invariant and in every
frame (finding 4 of 8a.2); the ABA ownership predicate across a release; two sections commute up to slot names; a lock-free free list (Treiber
stack, item 5); a thread that keeps a slot index across a release (`N586` per thread, the cross-thread form); an arena invariant read by a
second start (not thread-local: it must be a lock invariant, and the unit is refused otherwise); the arena invariant INSIDE a running writer
(the guarantee is at returns, `invRuhe` at closed machines, and at lock moves).
*Payload side.* A flag written more than once, an `exchange … publishes/awaits` (RMW pairing); re-publication and reuse of a payload cell (rings,
Treiber stack, seqlock, RCU: needs the reverse flag, hooks only, A.6); a payload published through TWO flags; cell-level separation inside one
table (the carrier is the whole table: two starts writing different cells of one payload table are refused, not covered); a device/DMA payload; a
payload or an arena ACROSS a link (O28); the `seq_cst` total order (item 4, `seq` is release/acquire in the model); `consume`; fences; a flag
invariant under stage P1 (named as such while P2 is open); a hardware lowering that is WEAKER than `D.ordnung` at a racy flag (assumption (2) of
the reading, now load-bearing).
*Standing items unchanged:* termination and waiting bounds, stack depth, the C and the hardware, starvation freedom, probabilistic statements,
floats beyond the kernel model, invariants inside a held section, a start declared once on several threads, the Rust checker as the Lean Bool
only as far as it is (it is NOT yet the Lean Bool for `PubRegel`, `ArenaZeuge`/`ErkB`).

#### G. Verification ledger (what this plan did and did not check)

[V] read or measured: every file, line and count quoted above (`Syntax.lean` 111/653/647, `rufAt` 397-399, `schuldet` 478, `InvRuhe*`,
`Spec.lean` 1481-2300, 1362-1470, the 84/85/80 literal counts, the 59-module/20,296-line layering fact, 712 files / 275,543 lines, the three
fixtures with a non-empty `traeger`, the exporter lines 5541/5594, the header places). [M] one mock (`exp1.lean`) compiled under Lean 4.33.1:
`Deklaration extends DeklBasis`, the computed `traeger`/`schuldet`, `where` literals, the coercion. [U] everything marked: no `lake` ran, no
real file was edited, the real `Arena` files were not recompiled against `DeklBasis`, O5's completeness, O10's scale, the literal fallout of
`SperrInv`/`StartPflicht`, all timings, the `autoParam` default, and whether T3's reading of `invarianten_gehalten` holds in the Rust U003.

#### H. Implementation checkpoint (2026-10-19, PAUSED at Simon's request)

**Status:** implementation is paused. No build or contributor is running. Nothing from this task has been merged or pushed.
The main checkout remains at `490af39abc21319718539e85b568bfe3caf9eabb` (Lean/Mathlib 4.35.0), apart from this checkpoint document.
The combined M8 claim change is **not applied**. Keep the current NOT CLAIMED text until the actual integration and both verdicts succeed.
This dated checkpoint supersedes G's planning-time verification status; it does not change the decisions or the scope of the plan.

**Location and recovery.** All paths below are relative to the repository root. The active, detached integration worktree is
`.claude/muse-arbeit/kratz/spec-arena-recovery/work/`. It contains uncommitted M2/M3 code, including the single Rust exporter field rename.
Do not remove this worktree or its recovery directory while the task is paused. Earlier scratch worktrees were externally deleted during a
pending tool call; their sources were recovered, and the main checkout's independent 4.35 upgrade was preserved.

The recovery directory contains:

| Artifact | Meaning |
| --- | --- |
| `latest-source.zip`, `latest-source-manifest.json`, `checkpoint.py` | Current M2/M3 changed/new sources, 151 files at pause; independent of the worktree's survival |
| `pause-snapshot.zip`, `pause-snapshot-manifest.json` | Pause snapshot of the current source checkpoint, contributor sources/patches, integration preparations and evidence logs |
| `m3-integration-green-435.log` | Successful 820-job M3 target closure, including the real top goal and its axiom print |
| `m3-full-address-limit-abort.log` | Complete failed full-build attempt; not a green result |
| `entry-source/M8-entry-on-M3.patch` | Unelaborated entry/certificate/goal migration, 30 source files; applies against the current M3 worktree (`git apply --check` passed before pause) |
| `entry-source/M8-fixtures-after-entry.patch` | Unelaborated migration of 26 fixture/internal-corollary files; apply after the entry patch |
| `entry-source/O25-goal-witness-after-fixtures.patch` | Unelaborated concrete arena goal witness; apply after both M8 patches |
| `entry-source/M8-STATUS.md`, `M8-FIXTURE-STATUS.md`, `O25-STATUS.md`, `O25-API-AUDIT.md` | Exact scope, known limitations, constructor audit and remaining elaboration risks |
| `okb-source/`, `okb-source/SHA256-CURRENT.json`, `okb-source/FIRST-VALIDATION-TARGETS.md` | 29 contributor Lean sources and their inventory; payload source remains unelaborated on 4.35 |
| `payload-source-transfer.txt` | The 21 active payload source paths selected for future transfer; excludes the contributor's baseline copies and arena files |
| `payload-interface/payload-low-on-M8.patch`, `payload-race-core.patch`, `STATUS.txt` | Unapplied, unelaborated dependency extraction and fixed-carrier race-proof preparation |
| `RECOVERY.md` | Detailed chronological recovery/build record |

**What is actually checked.** The historical M1 full spike on Lean 4.33.1 was green. This is historical evidence, not a 4.35 full-build result.
The recovered M2 target run on 4.35 was green (205 jobs). The final M3 target run on 4.35 was green (820 jobs):

- `Deklaration extends DeklBasis`, arena metadata in the declaration, computed sum-carrier footprints, sum-carrier `schuldet`/U003 and widened payloads.
- The executable `Dekl.okB` and its downstream `Dekl.okB_iff`, with genuine valid/defective structure witnesses.
- Actual `invPruef`/`invOrte` dispatch in `rufAt`; a recognized head-only mutation passes, while a broken head is refused despite `invariante := tru`.
- `Dekl.okB_mitRuhe` and `Dekl.ok_mitRuhe`; actual footprint locality/permissions and the migrated SC/atomic invariant consumers.
- `gabbro_ziel` and its SC/GX/link corollaries compile on **exactly** `propext`, `Classical.choice`, `Quot.sound`.
  This is the M3 statement, **before** the new entry-aware duties, start clause and payload leg.

**The full library is not green.** The first complete run reached 1629 jobs and failed in seven modules.
Six failures were thread-creation aborts (exit 134) under the author's unsuitable 12 GiB *virtual-address-space* limit, with physical memory
still available: `UebersetzeProben`, `UebersetzeProben2`, `UebersetzeProben3` in `Parser/Elab/Proben/Fruehe`,
`ArenaErkZeugeSchleife`, `ArenaSperreAbdeckung`, and `Code/Refine/Witness`.
The seventh was a deterministic 1,000,000-heartbeat timeout at `ArenaErkZeugeBaum.lean:116`.
These failures need a serial rerun with a physical-memory cgroup limit, and the tree witness needs a measured local proof/budget repair.
No proof guarantee may be weakened. The full run had already ended before the subsequent stop request executed; no process was killed.
The guard/negative-U003 witness did compile in this full attempt. The four guardians, final paired reviews and final publication have not run.
The matching 4.35 `programmlogik/.lake` cache and manifest were copied into the worktree for future checker/GabbroV tests.

**Proof obligations still outstanding.** “Draft” below means source exists but Lean has not accepted it; a textual import/API audit is not a proof.
“Missing” means the required result is not yet supplied by the draft.

| Plan obligation | Required theorem/result | Exact remaining work |
| --- | --- | --- |
| O9: automatic arena preservation | `invGutS_aus_arena`, `invGutGrund_aus_arena`, `invGutSA_aus_arena`, `invGutGrundA_aus_arena` (`ArenaKoerperZert`) | **Draft.** Elaborate all four variants. Their actual body duty takes the checked arena-entry fact; discharge the arena branch from `ErkE`, retaining the ordinary-expression duty. |
| O10: actual frame entry | `ausgewaehlte_schluessel_sind_start`, its `GA` variant, `ausgewaehlter_rahmen_startSpeicher*`; `arenaEintritt_rahmen*`, `arenaEintrittLauf_zertifiziert`, `arenaEintrittLaufX_zertifiziert` | **Draft for the writer-root fallback only.** Derive entry at the actual saved `s0` from source certificates and initial consistency, including suspended frames; never add it as a semantic user assumption. The general joint induction supporting two writer calls in one run is **missing**. |
| O10/O14/O15 boundary | General `arena_eintritt` together with return/ground preservation; call/section recognizer soundness | **Missing beyond fallback.** Current `ErkE` leaf certificates imply there are no calls to owing writers, since effects are transitive. Two fresh runtimes are not a witness for two calls in one runtime. Caller/section constructors and the joint induction are still needed for that broader claim. |
| O11/O12 and idle root | `arenaStart_mitRuhe`, `arenaEintrittLauf_mitRuhe`, `arenaEintrittLaufX_mitRuhe`; start-duty propagation; `invRuheG_aus`/atomic counterpart with the new start clause | **Draft.** Add `StartPflicht.arena` for declared arena names, propagate it through runtime/idle/link bridges, and reprove both invariant legs with the conditional ordinary-invariant start hypothesis. The corresponding M3 lemmas are green only with the old hypotheses. |
| O16/O17 certificate integration | `ArenaZeuge`/`ArenaZeugeF`, their body-discharge and owned-function/link packaging | **Draft, limited scope.** Validate all SC/atomic user-duty and fixture changes. Shared arenas remain lock invariants; no separate manual D2 meaning may remain. The draft also restricts shared-havoc reads in owing arena writers (`ArenaHavocFrei`); name this boundary explicitly. |
| O19/O20 decidable payload rule | `PubDirekt.pruef_iff`, `pubZeugnisB_iff`, `pubB_iff`, `pubB_ohne_nutzlast`; `pubB_aus_akzeptiert` | **Draft.** Compile the actual finite source rule and all positive/negative witnesses. Check initial flag non-confirmation against the real `sp0`; it cannot be inferred from `P/fs/ws` alone. Preserve all formerly accepted programs and order assignments where no racy payload exists. |
| O20 source-to-step soundness | `blatt_phase`, `blatt_phase_schreib`, `blatt_phasenwechsel`, `blatt_phasenwechsel_schreib`; `kopfOK_schritt`, `kopfOK_schrittW`; `Regel.rest_anfang`, `Regel.rest_erreichbarW` | **Draft.** Elaborate typed residual annotations and prove that actual step events **and changed memory** follow the source publication phase. `SchreibG` includes both. These lemmas are not a global no-later-write theorem yet. |
| O21 global source-to-history preservation | A new reachability induction combining `PhaseW`, actual source phase bits, publication history, unique writer and saved `FlagLesungW` | **Missing; the principal payload gap.** Derive the unique real publication, no later payload/flag write, and an actual matching publish/read `Uebergabe` for every confirmed reader access. Do not assume these facts in the user's duty. |
| O21 payload visibility/weak bridge | `wert_einzelschreiber`, `payload_sicht_uebergabe`, `payload_praesentiert`, `schritt_sichtInvX_payload`; then `PubRegel -> PubSicht` over every actual W run | Semantic helper sources were historically green on 4.33.1 and are **unvalidated on 4.35**. The final source-rule-to-`PubSicht` theorem is **missing**. Instantiate the semantic helpers from the global history induction, not from external hand-off premises. |
| O22/O23 replay and reader rely | Monotone replay over `GeteiltA ∪ PubLesbar`, real checked footprint/race exemptions, order-filtered `SchwachX` and new `ZielX.pubSicht` | **Missing integration.** Keep the actual machine havoc set atomic-only (`GeteiltV`); derive equality of presented/current plain payload from the W hand-off proof. Broaden only the user/replay rely. P1 may assume every payload value; P2's `S.pub` publish hook and constrained reader rely remain unproved. |
| O24 final goal preservation | `gabbro_ziel`, `gabbro_ziel_sc`, `gabbro_ziel_sc_aus`, `gabbro_ziel_gx`, linked variants after the M8 edits | **Draft for arena; payload integration missing.** Reprove all conclusions, old-unit embeddings, start/runtime/owned-function bridges and exactly-three-axiom checks after the actual combined statement changes. Existing M3 green does not discharge this. |
| O25 applied arena witness | `ArenaGoalZeuge.geprueft`, `nutzer`, `ausfuehrung`, `arena_im_zielsatz` | **Draft.** One real accepted writer start, idle other slots, seven concrete G steps, finished writer/`InvZu`, and `gabbro_ziel_gx.invRuhe -> KL.Ok` in changed memory. Kernel Bool checks and dependent step/memory equalities are not elaborated. |
| O25 applied payload witness | A concrete accepted publisher/reader unit and actual two-thread W execution whose goal has nonempty `pubSicht`, plus rejected defective programs | **Missing at goal level.** Source-rule fixtures alone do not replace this witness. Require rejection of write-after-publish, read-before-confirmation, wrong initial flag, multiple writers/sites and relaxed racy-flag order. |

**Named fallback boundaries, not completed claims.** The arena draft covers recognized writer roots, not calls to writers; an ordinary call
boundary cannot be manufactured by restarting the same live slot. The payload draft currently checks a direct, call/loop/lock-free one-shot
fragment and overrestricts unrelated flag operations. The planned repair to enumerate all publication candidates and preserve unrelated
`publish`/`awaits` operations has **not** been implemented. The reader's P1 arbitrary-value rely is only the plan's authorized intermediate
stage; no flag-invariant P2 claim is proved. O18 (`ErkB`/`erkB_sound`, moving certificates into the checker) is M9, after a reviewed M8 fallback,
not a completed part of the current work.

**Resume order (do not execute while paused):**

1. Recover from the worktree/source checkpoint, preserve 4.35, and finish the full M2/M3 library check with physical memory limits.
   Repair the explicit tree-witness timeout; retain the current axiom print. Save a green foundation checkpoint before claim changes.
2. Transfer only the selected payload sources, widen the direct fixture's `nutzlast` to `[.inr .zaehler]`, and obtain actual Lean feedback.
   First targets: `PayloadSicht`, `PubDirektZeuge`, `PubDirektRestLauf`, `PubRegelZeuge`, `PubEinbettung`, `PubOrdnung`
   in their documented `Speichermodell.Payload`/`Zielsatz.Payload` namespaces. Do not overwrite the parent-fixed arena files.
3. Apply the entry, fixture and O25 patches in that order, preserving the parent's latest M3 fixes. Compile the new arena duties/providers,
   then both goals and the concrete applied witness. The parent corrected O25's conditional start argument to `(fun _ => hstart)` in both
   its source and patch; the earlier contributor ZIP predates that correction.
4. Close the global payload history induction and actual applied payload goal witness. Apply/reconcile the prepared low-interface extraction
   (to avoid `Spec` import cycles) and race-core refactor, then integrate the actual combined M8 statement and its embeddings.
5. Only after proofs pass: rewrite the header/NOT CLAIMED scope honestly, update theorem-map/status documents, obtain independent Muse and Opus
   verdicts on the exact candidate, run all four guardians, commit through `./commit.sh`, and publish checked master. No code commit or push
   has yet been made for this task.

### 8a.4 The interrupt-mask state of machine G (O19 rest; Lean 2026-10-18; the `Spec.lean` diff is a PROPOSAL, nothing in `Zielsatz/Kern/` changed)

**Decision (Simon, 2026-10-18):** the strongest variant. Machine G gets a per-core interrupt-mask state, `KernHaltE` is derived from the model
instead of resting on a hardware schedule premise, and the mask enters `Code` as a hardware form with a named assumption. Status, measured by
`lake build` of the new modules and `#print axioms` (every theorem: `propext`, `Classical.choice`, `Quot.sound` at most; no `sorry`;
`gabbro_ziel` and `Spec.lean` untouched, no existing module imports the new ones):

| Step | Where | Result |
|---|---|---|
| 1. mask state + semantics | `Zielsatz/Eigenschaften/KernMaske.lean` | layer `KernZ` over `RufMaschineG` (G machine, `MaskeKern`, begun set), step `KernSchritt kern H` (entry only when the core is unmasked, run to completion, acquisition masks / release unmasks / nesting by recomputing the acting thread's entries from its held locks) |
| 1. embedding | same | `kernLauf_laufG` (a guarded run IS a G run: every leg of `Ziel` holds on it); `laufG_kernLauf` (with no handler every G run lifts, machine for machine); `mask_leer_ohne` / `kernLauf_ungemaskt` (no `masks irqs` lock: no core is ever masked); `maske_nichtleer_iff` (a core is masked iff a thread of it holds a masking lock) |
| 2. the sentence | same | `kernPlan_aus_lauf` (`KernPlan` DERIVED from the guards; uses `fertig_kein_schritt`: a finished thread has no step), `KernHaltM`, **`kernHaltM_aus`** (= `kernHaltE_aus` with the schedule proved; premises: closure `abg` and the discipline `masken` only) |
| 2. same statement | `KernMaskeGleich.lean` | `kernPlan_lift` (every run `KernPlan` admits lifts to a guarded run) and **`kernHaltE_iff_M`**: `KernHaltE ↔ KernHaltM` for a start in which no thread holds a masking lock (true for every declared root: `Akzeptiert.wurzeln`). Replacing the leg is therefore NOT a weakening |
| 2. witness + planted defects | `KernMaskeZeuge.lean` | ONE program (one lock, handler `h`, ordinary `t`), two declarations differing only in `maskiert`: `ohne_maske_verklemmt` (unmasked: the handler enters at a lock its core's thread holds, waits, every other thread is held by run to completion, `¬ KernHaltM`; `w_masken_falsch`: the checker refuses it), `mit_maske_verweigert` (masked: the core's mask is set, the model REFUSES the handler's entry step; the planted defect is that very step, a step of plain G), `mit_maske_nach_freigabe` (after the release the entry is admitted), `mit_maske_sicher` / `mit_maske_sicher_E` (`KernHaltM` and `KernHaltE` on every run), `einbettung_zeuge` |
| 4. `Code` | `Code/Model/{Syntax,Semantics}.lean`, `Code/Conc/{Mask,MaskNeed,MaskRel,MaskWitness}.lean` | `Instr.imsk d p v` (ISA-neutral word exchange on the core's mask word), lowering blocks `maskOn`/`maskOff` around the ticket lock (save/restore: nesting with no static caller knowledge), runs `maskOn_run`/`maskOff_run`; the named assumption **`MaskHw`** (H1 the mask word IS the register: nonzero means masked; H2 an interrupt is taken only on an unmasked core; H3 a masked core does not switch threads); the refinement: cover invariant `MaskCells` (G masked implies the word is nonzero: the hardware is only ever MORE masked than G), `mask_on_step`, `mask_off_step`, `maskCells_nach` (G's `nimmt`/`gibt`), `maskCells_ticket` (the ticket steps keep it), **`irq_guard`** (with `MaskHw`, a handler entry on core `c` happens only where `mk c = []`: the premise `eintritt` of `KernSchritt`); witness `mask_witness` (one thread through the lowered section, `LockRel` and `MaskCells` at both stops), `maskHw_witness` (satisfiable), `maskHw_planted` (a CPU that interrupts a masked core meets none) |

**The proposal for `Spec.lean` (step 3; to be reviewed as a diff with the combined diff of 8a.3, NOT applied):**
1. Move `MaskeKern`, `maskEintr`, `maskeNach`, `KernZ`, `KernSchritt`, `KernLauf`, `KernStart` from `KernMaske.lean` into `Spec.lean` just before
   `KernHaltE` (they use only `RufSchrittG`, `FertigG`, `offen`, `Faden`, `HandlerVon`, all already there); `KernMaske.lean` keeps the lemmas.
2. Redefine `KernHaltE` as today's `KernHaltM` (`∀ kern Z0 zs fs n, KernStart … → KernLauf … (HandlerVon P M0) … → …`) and delete `KernPlan` from
   `Spec.lean` (no legacy: `KernPlan` survives only as the hypothesis of the engine lemma `kernHaltG_gilt` in `Masken.lean`, where it is a lemma
   premise, not a statement). `Beweis.lean:178` uses `kernHaltM_aus` instead of `kernHaltE_aus`.
3. The atomic twin `KernHaltEA` (`BeweisAtomar.lean:164`, over GA runs) needs the same layer over `RufSchrittGA`: `kernPlan_aus_lauf` and
   `fertig_kein_schritt` are proved for `RufSchrittG`; the GA step is `RufSchrittG` plus the atomic-read answer, so the lift is expected to be
   mechanical but is NOT done (`[U]`).
4. The header's named hardware assumptions lose `KernPlan` ("a named core schedule") and gain nothing: the schedule is the machine's. What stays
   named is what only the program or the CPU can supply: the discipline (a), and, for `Code`, `MaskHw`.
5. Equivalence is proved (`kernHaltE_iff_M`), so the diff is a restatement and not a tightening or a weakening; the premise "no thread of the
   start holds a masking lock" becomes a field of the start obligation (it is `wurzelnB`'s `haelt = []` for every declared root).

**Findings (each named, none hidden):**
* No contradiction with the goal theorem: guarded runs are G runs.
* The mask list is DERIVED from the held locks (`maskeNach` recomputes the acting thread's entries), so it is an explicit state with a proved
  consistency invariant (`MaskeOk`), not an independent one; `Code` cannot derive it, which is why the hardware needs the cover invariant and the
  saved word.
* G's thread interleaving on one core is free beyond the handler rule. Real hardware saves and restores the mask per thread at a context
  switch; the cover and the LIFO restore of the saved word are faithful only under H3 (a masked core does not switch threads). H3 is a named
  premise of `MaskHw`; its composition with the interleaving of ALL threads of a core is NOT proved (the restore step has a ghost premise,
  `mk' c ≠ [] → saved word ≠ 0`, discharged only in the witness).
* The guard blocks EVERY other thread of the core while a begun handler is unfinished, including a second handler's first step: handler-on-handler
  preemption and re-entry are still out (as in `KernPlan`).
* The discipline stays load-bearing: without `masks irqs` the same program deadlocks (`ohne_maske_verklemmt`); the model derives the schedule, it does
  not conjure the lock declaration. `H102` still fires only on `via idt` roots.
* The Rust side is untouched: `Instr.imsk`, `maskOn`/`maskOff` exist only in the Lean `Code`; the LLVM backend and the exporter know no mask
  instruction (Lean first; the checker and the compiler follow after both verdicts, CLAUDE.md order).
* `Mem` semantics: the mask word is a memory cell only in the Lean model; that it is the CPU's register is H1.

### 8a.5 The reader/writer lock (Lean 2026-10-18; the `Spec.lean` diff and the syntax are PROPOSALS, nothing in `Zielsatz/Kern/` changed)

**Decision (Simon, 2026-10-18):** the strongest variant for safety and power, effort irrelevant: the language gets a reader/writer lock, and it
goes into the Lean model FIRST (CLAUDE.md order: model, then checker, compiler, `SYNTAX.md`/`LANGUAGE.md`; this round is the model only).
Status, measured by `lake build` of the new modules and `#print axioms` (every theorem: `propext`, `Classical.choice`, `Quot.sound` at most; no
`sorry`; `gabbro_ziel` and `Spec.lean` untouched, no existing module imports the new ones, `Grammatik.lean` does):

**The design (the smallest sound one), as a LAYER over machine G.** `Stmt.locks`, `Res.held`, the events `nimmt`/`gibt` and `RufFreiG` carry no
mode; a mode in them is a root change of `Kern/Syntax` (every module rebuilds) and a rewrite of everything about `offen`. The mask layer showed
the other way. The layer parameter is `lese : Faden → D.Lock → Prop` (thread `t` takes `L` SHARED; every other acquisition is exclusive; one
mode per thread and lock). A layer step (`RwSchritt`) is a G step, or a SHARED ACQUISITION `RwAcq`: the acting thread is a reader of `L`, every
other thread that holds `L` is a reader of `L`, and the step is machine G's own `dannLocks` step of the thread in the machine `ohneFremde`
(the other threads' traces blank, so `RufFreiG` holds there), the other threads kept. So the acquisition's content (rank premises `hr`/`hrang`,
`hself`, the event `nimmt L`, the residue) is G's, not restated; the release is G's `freiGib`; an EXCLUSIVE acquisition keeps G's `RufFreiG`:
NO other thread holds the lock, a reader included.

| Step | Where | Result |
|---|---|---|
| 1. layer + embedding + no change without a reader | `Zielsatz/Eigenschaften/RwSchritt.lean` | `RwSchritt`, `RwAcq`, `RwLauf`; `rwSchritt_of_G`, `rwLauf_of_laufG` (every G step and run is a layer step and run); **`rwSchritt_ohne_leser`, `rwLauf_ohne_leser`** (`lese = fun _ _ => False`: the layer's step IS G's step, its runs ARE `LaufG`: a program with no shared acquisition keeps its meaning, as a theorem); `rwSchritt_akteur` (every layer step is a G step of the acting thread in a machine that agrees on its record and the memory: how per-thread facts transfer), `rwSchritt_delta`, `rwAcq_speicher` (an acquisition touches no memory), **`rw_nimmt`** (a lock that enters the actor's held set was free, or the actor is a reader and every other holder is a reader) |
| 1. exclusion: many readers XOR one writer | same | **`RwExkl`** (two different holders of `L` are both readers of `L`), **`rwExkl_schritt`, `rwExkl_lauf`**, `rwExkl_start`, `rw_schreiber_allein` (a writer holds alone), `rw_leser_unter_sich`, `rwExkl_ohne_leser` (with no reader it is G's old exclusivity) |
| 2. rank order and the deadlock leg | `RwRang.lean` | `rangInvG_rw` (G's per-thread rank invariant along every layer run), **`kein_warteZyklus_rw`** (`KeinWarteZyklus` on every layer run: shared holders do not weaken the rank argument), `WartetAufRw`/`KeinWarteZyklusRw`/`keinWarteZyklusRw_aus` (a reader waits only for a writer, a writer for every holder: a SUBRELATION, so the plain statement carries), **`rw_leser_geht`** (progress: a reader at `locks L` while only readers hold `L` has a layer step; G alone would hold it back) |
| 2. race freedom, order through the lock | `RwOrdnung.lean` | `LeserLos` (the discipline: a reader of `L` writes no carrier `L` guards), `spurInv_rw_lauf`, `zugriff_haelt_rw` (every access to a guarded carrier holds the guard, before and after), **`sperre_ordnet_rw`** (`fs i` holds `L` after step `i`, another thread holds it before step `j`, one of the two a writer: `fs i` releases and then `fs j` acquires, `i < r < a < j`: `GeordnetRw`), **`rennfrei_rw`, `rennfreiRw_aus`** (no write-write and no write-read race on a guarded carrier, in the shape of `RennfreiBis`; read-read pairs do not conflict), **`rwSicht_schritt`** (the `sperrSicht` of a shared lock: a step accesses a guarded carrier only if its thread holds `L`; while ANY other thread holds `L`, as reader or writer, no step changes it) |
| 2. the lock invariant: visible to readers, re-established by writers only | `RwInv.lean` | `SperrInvRw` (every lock all of whose holders are readers has `S.inv`), **`sperrInvRw_schritt`, `sperrInvRw_lauf`** (the only owed step is a WRITER's release, G's `hfrei`; a reader's acquire and release owe nothing), **`leser_sieht_inv`** (a reader sees `S.inv L` at every machine of its section), `schreiber_erst_frei` |
| witnesses (kernel-checked runs) | `RwZeuge.lean`, `RwZeugeLeser.lean` | **`leser_schreiber_lauf`**: one run of twelve layer steps: thread 1 takes the lock, thread 2 takes it SHARED (G alone refuses: `nicht_bereit_an_sperre`; the layer admits: `RwAcq`), both hold at once; the writer stands at the lock with NO step; both readers leave; the writer takes the lock and holds it alone; a late reader is held back; `RwExkl` along the run; `GeordnetRw` at the reader-then-writer pair (the non-degenerate instance of `sperre_ordnet_rw`) |
| planted defects | same | (a) **a writer admitted while a reader holds**: the shared-acquisition recipe without `leser`/`andere` (the writer's lock step in the blank machine, kept next to the others) breaks `RwExkl` at the machine reached (last conjunct of `leser_schreiber_lauf`); (b) **a reader that writes a guarded carrier**: `leser_schreibt_rennt` (fixture `InvZeuge`: two readers hold the lock by signature and both write `konto[0]`; the accesses are not ordered, so `LeserLos` fails: derived from `rennfrei_rw`, not assumed); (c) **rank violation**: `leser_rekursiv_verweigert` (a reader taking the lock it already holds, the recursive read lock, is refused by `hr`: unprovable in a section that holds the lock; the typed syntax has no term for the violation, so the defect is the premise itself) |
| 4. `Code`: the lowering | `Code/Conc/RwLock.lean`, `RwLockRel.lean`, `RwLockWitness.lean` | ONE state word per lock (the cell `lblk`; the serving cell stays unused): `0` free, `2 k` held by `k` readers, `1` the writer. Blocks (ISA-neutral, release/acquire atomics, no fence, no ISA instruction): `wrTake` (`cas(state, 0, 1)`, acquire), `wrRel` (`astor 0`, release), `rdLoad` (`aload`, relaxed; again while `1`), `rdTake` (`rn := rs + 2`; `cas(state, rs, rn)`, acquire; again on failure), `rdRel` (`armw sub 2`, release); every outcome has its run (`wr_take_ok/fail`, `wr_rel_run`, `rd_load_wait/go`, `rd_take_ok/fail`, `rd_rel_run`). The invariant **`RwRel`** (ghost readers and writer, the word, G's held locks counted, the mode) and the steps: loads and failed takes G-silent; **`rd_take_ok_step`** IS the layer's shared acquisition (`lese u L`, every other holder a reader, `u` did not hold) and the relation holds for the machine whose `offen` gained `L`; **`wr_take_ok_step`** is G's `dannLocks` (`RufFreiG`: the word `0` means nobody holds); both releases are G's `freiGib`; **`rwRel_exkl`** (the invariant implies `RwExkl`); `rw_store_post` (a state-word store leaves the representation alone). Witness **`rw_witness`**: two loads, a winning take, a LOSING take (the race: the word moved), a reload, a winning take (both readers hold, word 4), the writer's take fails (word 4), both release, the writer's take wins with `RufFreiG`; `RwRel` after every step. ONE named assumption, `hroom`: fewer than `2 ^ (wbits - 1) - 1` readers at once (the counterpart of the ticket lock's outstanding-tickets bound). |

**The syntax, PROPOSED for `SYNTAX.md` (short English words, at most five letters; nothing implemented, nothing in the parser):**
* the declaration: `lock L rank N rw` (`rw` marks a lock that may be taken in both modes; a lock without it is exclusive-only and `reads L` on it is refused);
* the shared section: `reads L { ... }` (five letters; `locks L { ... }` stays the exclusive form, so no existing program changes);
* the signature clause: `reads L` beside `holds L` (a function that needs `L` held at least shared; `holds L` is exclusive and implies it; the call rule
  (`RufPasst`) compares modes: a shared holding cannot call a function that `holds L`);
* the discipline (to be derived by the checker, a refusal with its sentence and a poison probe): inside `reads L { ... }` and in a function whose
  signature has `reads L` no carrier guarded by `L` may be written, directly or through a callee (`TraegerSchreibt`), and `L` may not be taken
  again (the rank premise already forbids it: `leser_rekursiv_verweigert`). A reader that wants to write releases and takes `locks L` (no upgrade).

**The proposal for `Spec.lean` (step 3; to be reviewed as a diff together with the combined diff of 8a.3, NOT applied; `Deklaration` is split there, nothing here pre-empts it).**
Two ways, and the layer decides between them:
1. **(recommended for the final language) the mode in G.** `Deklaration.teilt : Lock → Bool := fun _ => false` (one more DEFAULTED field of the
   8a.3 list: the ~84 `Deklaration … where` fixtures stay unchanged); `Res.held L m`, `Stmt.locks L m hr body`, `Ereignis.nimmt L m h`, `gibt L m`
   with `m : Modus` (`excl`/`shared`), `offen` over `(L, m)`; `RufFreiG M f L m` becomes "every other holder of `L` holds shared, and `m = shared`
   (or there is none)"; `Akzeptiert` gains the component `leserlosB` (the discipline above). Then `lese` disappears (the mode is in the trace: this also removes the layer's
   one-mode-per-thread-and-lock restriction), every theorem of 8a.5 becomes a theorem about G itself (`rwSchritt_ohne_leser` becomes the statement that
   `m = excl` everywhere is the old machine), and EVERY leg of `Ziel` is proved once for the new G: the legs the layer does not prove (below) come for free.
2. **a layer statement** `GabbroZielRw` beside `GabbroZielVerbund`: `Ziel`'s legs over `RwLauf`, with `lese` an `Einheit` datum and `LeserLos` a component of `Akzeptiert`.
   It needs a layer twin for each leg that is proved by reachability induction over G (list below), i.e. a re-proof of the `ZielOrt/` development.

**Findings (each named, none hidden; NO contradiction with the goal theorem):**
* The goal theorem is untouched and consistent: `lese = ⊥` is G (`rwLauf_ohne_leser`), and a G step is a layer step. It says nothing about programs that take a lock shared;
  covering them is the `Spec.lean` diff above.
* **What the layer proves over layer runs:** `speicherSicher` (`spurInv_rw_lauf`), `rennfrei` (`rennfreiRw_aus`, with `LeserLos`), `sperrInv` (`sperrInvRw_lauf`, with the writer's
  release obligation), `sperrWechsel`/`sperrSicht` (`rw_nimmt`, `sperrInvRw_schritt`, `rwSicht_schritt`, `leser_sieht_inv`), `keinWarteZyklus` (`kein_warteZyklus_rw`).
  **What it does NOT prove:** `schwach` (`SchwachSC`, the DRF leg over the layer: the release/acquire edges of a reader's take and release are an exclusive lock's, but not re-proved),
  `vertrag`/`invRueck`/`invGrund`/`invRuhe`/`invSicht`, `folge`, `fortschritt`, `zeit`, `keinKernHalt`: they are proved by reachability induction over `RufErreichbarG`,
  and a layer-reachable machine is not G-reachable (the shared acquisition is no G step), so each needs a layer twin (the per-thread facts transfer through `rwSchritt_akteur`; the
  rely/guarantee ones through `rwSicht_schritt`). That is the cost of the layer, and the reason for recommendation 1: with the mode in G the legs are proved once.
* `LeserLos` is a PREMISE in the layer (a run property), as `KernPlan`/`masken` were for the mask; the checker rule that derives it (no write of a `L`-guarded carrier in a `reads L` section or a
  `reads L` function) is a proposal, not built.
* One mode per (thread, lock): a thread that takes `L` shared never takes it exclusively (a restriction of the layer, removed by recommendation 1).
* The lock is a spin lock without fairness: a stream of readers can delay a writer forever (the goal claims no starvation freedom; `FortschrittG` names no fairness either). A
  writer-preference variant (a pending-writer bit in the word, readers refuse while it is set) is NOT modelled; it would add one bit and no new soundness argument.
* The word's counter bound (`hroom`) is the one numeric assumption of the lowering and is named in every take step.
* **Spec.lean text that changes under recommendation 1:** the header's "exclusive lock" sentences, `RufFreiG` (T1), `Ereignis`, `offen`, `Res`, `Stmt.locks`, `D.Lock`'s companion field, and the definitions
  `SperrInvG`/`SperrWechselG`/`SperrSichtG` (which read `offen`): `SperrInvG` becomes the `SperrInvRw` form ("every lock whose holders are all shared holders has its invariant").
* The Rust side is untouched: the exporter, the checker (`U003`, `H`-rules) and the LLVM backend know no mode (Lean first; the checker and the compiler follow after both verdicts, CLAUDE.md).

### 8a.6 The hardware forms (pool, trap clause, process exit, task, targets) and the combined diff (2026-10-18; Lean layers proved, nothing applied)

`PLAN-HARDWARE.md` §16 designs the changes that take every system call, register and memory source out of the
compiler (`LLVM-BACKEND.md` §11, L1-L8) and proves their Lean layers (`Hardware/`, `Code/Gate/`, THEOREM-MAP §84).
Relation to the combined diff of 8a.3: **it needs no `Spec.lean` change** (the new forms are lowering data or named
assumptions; `gabbro_ziel_zusatz`/`gabbro_ziel_leer` prove that extra named assumptions never break the statement and
that `True` gives `GabbroZiel`). The OPTIONAL sharper statement (a `PoolAnn` conjunct of `HardwareAnnahmen`, role data
in `Deklaration`) is compatible with `Deklaration extends DeklBasis`: its fields (`rolle : Ax → Option (Nat × Rolle)`,
`seite : Nat → Nat`, both with defaults, so the ~84 fixtures stay unchanged) are NOT basis fields, and the arena
structures parameterised by `DeklBasis` are untouched. If both diffs are applied, `HardwareAnnahmen` gets ONE conjunct
list (`GutO ∧ RegLokal ∧ AxVertragO ∧ PoolAnn`); review them together. The arena's storage (8a.3 decision 1) reads from
a pool as `Hardware/Anbieter/Arena.lean` (`ArenaGut`, `arena_grow_geht`): the commit ranges are the existing template
arithmetic, so the `Dekl` of decision 1 and the pool do not interact.

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

## 11. Message passing with a plain payload (Phase B item 1, 2026-10-18): the model is proved; the `Spec.lean` diff is merged into 8a.3, the `N291` replacement is PROPOSED, nothing applied

*Why this file:* it already holds the other `Spec.lean` proposal (8a.3), and the lock-free structures of Phase B item 5 (SPSC/MPSC ring, Treiber
stack) are dynamic data structures whose payload reads this item makes possible. Lean side: `grammatik/Grammatik/Speichermodell/Payload/`
(`PayloadHb`, `PayloadLitmus`, `PayloadLB`); `THEOREM-MAP.md` §80. Nothing in `Zielsatz/Kern/Spec.lean`, the Rust checker or the exporter changed;
`gabbro_ziel` is untouched (`Grammatik.lean` imports the new modules, nothing imports them).

### 11.1 What is proved (memory model only, every program, no footprint premise)

The pattern: `payload store (t); flag = v publishes {payload} (t, order freigabe) ... branch on awaits flag (u, order freigabe); payload load (u)`.

| Statement | What it says |
|---|---|
| `HbSeen W u c m`, `HbRace W u c m` | the write message `m` of `c` happens before `u`'s next access to `c` (`m` is in the history and `u`'s view of `c` reached `m.ts`); the complement, where a read of `u` may legally return something older than `m`. View-based happens-before of RC11, read off machine W, no second relation |
| `payload_mp` | **message passing**: along the run (`MpAblauf`: payload write, run, release write of the flag, run, acquire read of the message that write added) the payload write happens before the reader's state after the await, and on every later state (`hbSeen_laufW`); the message carries the memory the writer produced. Built on `hb_uebergabe` |
| `payload_mp_lesen` | every read of the payload after the await returns a message at or above the written one |
| `payload_kein_rennen` | after the await there is no `HbRace` on the payload |
| `payload_mp_wert` | with two memory facts (the publisher had seen the whole payload history; nothing adds a message at the payload after its write) the reader's presented memory at the payload IS the memory the writer wrote |
| `gesehen_einzelschreiber`, `still_of_kein_schreiben` | those two facts from thread-level facts: only `t` ever writes `c`; no step after the write writes `c` |
| `erwartet_bestaetigt` | the **branch fact** of LANGUAGE 11.5 rule 2: if no message of the flag before the publish confirms (the initial value does not), nobody writes the flag between publish and await, and the reader branched on a confirming value, then the message it read is the one the publish added (the `erwartet` premise of `MpAblauf`) |

Litmus facts on the view machine of `Sicht.lean` (the same `beitrag`/`nachricht`/`Lesbar`/`Frisch` that `SchrittW` uses), with a run checker
(`lauf`, `gehe_schritt`, `erlaubt_of`: a list of choices is a reachable state; allowed outcomes by `decide`, forbidden ones by invariants):

| Fact | Verdict | Where |
|---|---|---|
| MP release/acquire, flag seen payload not | FORBIDDEN | `mp_ra_verboten` (Sicht) |
| MP, payload AND flag seen (non-degenerate) / the stale read is refused there | witness / `isNone` | `mp_zeuge`, `mp_alt_abgelehnt` |
| payload read BEFORE the await | ALLOWED (counter-model) | `mp_vor_erwartung_erlaubt` |
| flag read relaxed / flag written relaxed / both relaxed | ALLOWED (counter-models) | `mp_flagge_lesen_entspannt_erlaubt`, `mp_flagge_schreiben_entspannt_erlaubt`, `mp_rlx_erlaubt` |
| payload rewritten after the publish: reader sees the flag and the NEWER value | ALLOWED (the value claim fails, the `>=` claim holds) | `mp_umgeschrieben_erlaubt` |
| SB (release/acquire both 0) / SB on SC | ALLOWED / FORBIDDEN | `sb_erlaubt`, `sb_sc_verboten` |
| IRIW release/acquire, readers disagree | ALLOWED (also for `seq`: the model gives `seq_cst` no total order) | `iriw_erlaubt` |
| LB, both reads return 1 | FORBIDDEN (no promises) | `lb_verboten` |
| CoRR | FORBIDDEN | `corr_verboten` (Sicht) |

**Not built (honest):** a concrete two-thread run of machine W/GX over a program with this shape. The generic theorems apply to any W run with the
pattern, and `mp_zeuge` shows the pattern has runs on the view machine, but no `Programm D` with a plain payload and a payload flag exists among the
Lean fixtures (the nearest, the noninterference fixture, has `kern` write the flag only). Building one means a declaration, two bodies and about five
G steps (the scale of `w_nicht_sc`, a few hundred lines); it should be the first witness of the applied diff, not a separate item.

### 11.2 What the theorem needs from the program, premise by premise

| Premise of the theorem | Provided by | Status |
|---|---|---|
| `ordVon ord f = freigabe` (flag) | the language DERIVES release for a payload-carrying atomic (LANGUAGE 11.1, `V004`/`V005`, `holordnung` in the emitters); in the model `ord` is free | the model needs a premise on `ord` (D1); the counter-models show the relaxed flag fails |
| `c ≠ f` | trivial | - |
| payload write by `t` before the publish step by `t` | program order of the publisher; `V006` (Rust) refuses a payload written AFTER the publish in the same body | a fact of the run, no extra premise |
| `hgesehen` (publisher saw every payload message) | only `t` writes `c` (`gesehen_einzelschreiber`) | proved from the single-writer fact; statically `SchreibGetrennt`/`V010` |
| `hstill` (nothing writes the payload after it) | static rule: no write of `c` reachable after a `publishes f` on any path (loops included) until a handshake (item 5) | NOT a global checker rule today: `V006` is intra-body; needs the interprocedural form (R1) |
| the reader's flag message is the published one | `erwartet_bestaetigt`: confirming branch, flag initial value non-confirming, flag written once | the branch fact is in the language (LANGUAGE 11.5 rule 2); the checker needs the dominance rule R3 to use it |
| the reader's payload read happens after the confirmed await | the static dominance rule | R3; its dynamic form is a frame invariant (D5) |

### 11.3 The `Spec.lean` diff for the payload: SUPERSEDED by §8a.3 (2026-10-18, decisions 1-3)

The six items D1-D6 that stood here are merged into the ONE diff of §8a.3 and changed by Simon's decision 3 (2026-10-18). Where each went:

| Old item | Now | Changed by decision 3 |
|---|---|---|
| D1 order premise `PubFlagge` on a free `ord` | §8a.3 C5: `OrdAb`, content = the DERIVED order `D.ordnung g` (a definition from `D.nutzlast`, not a field and not a premise on a free function); vacuous without a racy payload | the order is derived per atomic |
| D2 static component `pub`, `PubLesbar`, `fuss`, `renn` | §8a.3 C6 and A.5 (`pubB`, `pubB_iff`, O20) | `PubLesbar` may mention the flag's own invariant; table carriers allowed (D6) |
| D3 rely set (havoc at payload reads) | §8a.3 C7: stage P1 (havoc) is the NAMED INTERMEDIATE; the target is stage P2, the flag invariant `S.pub g` (publisher duty at the `publish` hook, reader's rely after the confirmed `awaits`, `HavocPub`, O22) | flag invariants are the target |
| D4 race leg `PubSicht` | §8a.3 C8 (`pubSicht`, over `OrdAb`) and O21 | none |
| D5 proof obligations | §8a.3 section B rows O19-O25 (statement, location, discharge, witness, planted defect) | none |
| D6 widen `D.nutzlast` | §8a.3 A1.7 (`List (Tab ⊕ Glob)`, `Stmt.publish`, `Block.awaits`, the Hoare mirror, `PaarungAusgenommen`); the carrier is the whole TABLE (cell-level separation stays NOT CLAIMED) | table cells in the first diff |

Re-publication (the old "stays NOT CLAIMED: reuse of the payload cell") is anticipated by hooks (§8a.3 A.6: the reverse flag `rueck`,
an interval form of `hstill`, per-message statements) and still NOT claimed beyond one-shot. The header places and the NOT CLAIMED lists that
change are §8a.3 A.8 and F. `#print axioms gabbro_ziel` stays `propext`, `Classical.choice`, `Quot.sound` (checked for `PayloadHb`,
`PayloadLitmus`, `PayloadLB`; the new modules are checked at each step of §8a.3 C).

### 11.4 Checker-rule sketch: the replacement of `N291` for payload carriers (NOT implemented)

Today `N291` refuses a body read of a carrier that no held lock guards and no lock invariant protects (`fusswache2.rs`, `begehe`); `N301` refuses a
write-read race across starts and `N300` a write-write race. A payload read after `awaits` is refused by `N291` and `N301`, which is why 11 corpus
examples wait. The pairing pass (`paarung.rs`) already checks the LOCAL half: `V001`-`V005` pairing and strength, `V006` payload written after its
`publishes` in the same body, `V007` payload read before its `awaits`, `V010` payload writer outside the publisher's hull, `V011` expiry. The
replacement is a global footprint exemption built from those facts, not a weakening of `N291`:

* **R0 (carrier).** `c` is a payload place `p` of `atomic f ... publishes { p ... }` (name equality up to index substitution, as `paarung::form`),
  plain, unguarded, and no `requires`/`ensures`/invariant mentions it (a payload has no contract; the reader's logic is the rely).
* **R1 (single writer, single epoch).** Exactly one declared start `w₀` has `c` in its write hull (`N300`'s relation, kept). In `w₀`'s call graph every
  path from a write of `c` reaches the `publishes f` and then no write of `c`: an interprocedural `V006` (a write after the publish on ANY path,
  through callees and loops, is the new refusal, proposed `N587`). A loop writing `c` around a `publishes f` stays refused until a reverse-flag
  handshake exists (item 5).
* **R2 (one-shot flag).** `f` has ONE `publishes` site in the unit and its published value differs from its initial value (`hnicht`); a second
  site, an `exchange` on `f`, or a payload-free store to `f` is refused (proposed `N588`).
* **R3 (dominance).** Every read of `c` in a function reached from a start other than `w₀` is dominated by a confirming `awaits f` branch: on every
  CFG path from function entry to the read there is an `awaits f` whose bound value is compared to the published value in an enclosing `if`/`match`
  arm, or the function is called only from such a branch (a per-function summary `needs_await(f)` closed by the same fixpoint as `reachB`). A read
  not dominated is the NEW refusal `N589`, replacing `N291` at that site and naming the flag. A read of `c` in `w₀`'s own graph needs nothing
  (the writer sees its own writes) but may not follow a `publishes f` (R1).
* **R4 (order).** `f` is declared release/acquire (derived: `V004`/`V005` already); a `relaxed` flag with a payload stays refused where it is.
* **Exemptions.** `N291`/`N301` skip a carrier exactly when R0-R4 hold for it; `N300` stays (a second writer is a write-write race). Each new code
  needs its sentence in `saetze.rs`, a poison probe and a positive probe. Next free numbers: code `N587`, gift 1471, example 1165, alias rule `R016`.
  The positive set is the 11 waiting corpus examples; the planted defects are the counter-models of 11.1 (rewrite after publish, read before await,
  relaxed flag, two writers, two publish sites).
* **Lean first.** Nothing above is implemented before D1-D6 are applied in Lean; the Rust rule must decide `PubRegel` (the Lean Bool `pubB`), not
  approximate it; a form the rule cannot decide stays refused by name.

**Amendments by decision 3 (2026-10-18; the rule text above stays the model of what `PubRegel` decides, these lines change it):**
* **R0 (carrier)** widens: a payload place is a TABLE or a global (`D.nutzlast : Glob → List (Tab ⊕ Glob)`); the name equality of `paarung::form`
  is up to index substitution, but the Lean carrier is the whole table, so a table used as payload of flag `f` is written by the one publisher only.
  "No `requires`/`ensures`/invariant mentions it" becomes "except the flag invariant of its OWN flag" (§8a.3 T4).
* **R4 (order)** becomes the derived order: `D.ordnung g = freigabe` for every flag with a payload; the model quantifies over lowerings at least
  that strong (§8a.3 C5). A relaxed flag with a payload stays refused where it is (`V004`/`V005`), and the model no longer needs it as an assumption.
* **R5 (one-shot, anticipates re-publication)** NEW: `rueck f = none`; the later rule replaces R1's "no later write of `c`" by "no write between
  the publish and the reader's ack of that epoch".
* **R6 (flag invariant)** NEW, target stage: the publisher's world at `publishes f` meets `S.pub f` (checked by the semantics, like a lock release);
  a reader assumes it at the confirmed read. Until the proof of O22/O23 exists the header names the stage "the reader assumes nothing" (P1).
* Next free numbers are unchanged until the checker work starts (code `N587`, gift 1471, example 1165, alias rule `R016`).

### 11.5 Decisions (taken by Simon, 2026-10-18; they replace the four questions that stood here)

1. **D1, the order:** derived per atomic (`D.ordnung`), no free `ord` quantifier for racy-payload flags (§8a.3 C5, T8: the premise is on racy flags
   only, so no unit covered today is dropped).
2. **D3, the rely:** flag invariants are the target (stage P2); havoc (stage P1) is only the named intermediate stage while the proof of the hand-off
   hook and the replay instantiation (§8a.3 O22/O23) is open.
3. **D6, `D.nutzlast`:** widened to table carriers in the first diff.
4. **One-shot:** the first cut; re-publication is anticipated by the hooks of §8a.3 A.6 and stays NOT CLAIMED.

Open for Simon after the planning pass: §8a.3 T1 (the arena declaration lives in `Deklaration`, not in `Programm`) and T3 (a shared arena is a lock
invariant ONLY, not a `D.invs` member) change the text of the earlier proposal and should be confirmed before M1 starts.

## 12. Ownership of individual allocations across calls (Lean audit and plan, 2026-10-24)

**Status: implementation in progress; proved increments are recorded in section 12.6, full closure remains OPEN.** The question is whether a caller can hand one
allocation to a callee which may free it, return its ownership, or return a newly allocated object. Preserving the arena's structural
invariant across a call is already proved, but does not establish this ownership protocol. This audit did not run a fresh Lean build.

**Binding clarification from Simon:** providing sufficient RAM is user logic. The language must preserve its guarantees when allocation
fails; the unbounded heap must always have an explicit OOM path. A pressure sample does not replace that path. No OS guarantee or extra
hardware assumption may be introduced to discharge ownership, resource availability, or the OOM branch.

### 12.1 What the Lean model currently covers

All paths below are relative to `grammatik/Grammatik/`.

| Existing definition or theorem | What it establishes | What it does not establish |
|---|---|---|
| `Bausteine/Arena/Struktur/Erkenner/ArenaErkenner.lean`: `Abs.leer`, `StrukturPasst`, `Erk.frei` | Function-entry parameters have status `offen`; `frei` requires status `frei` (owned, live, unlinked), and changes it to `offen`. Two owned variables denote different slots. | No signature instantiates ownership of an argument in the callee. `offen` forgets knowledge; it is not by itself a prohibition on every payload read. |
| `Bausteine/Arena/Struktur/Erkenner/ArenaErkEnde.lean`: `ErkE.ret`, `ErkE.retWhy`, `erkE_koerper` | Recognized bodies preserve `K.Ok`; the entry theorem uses `Abs.leer`. | The returned value carries no proved ownership postcondition. The recognition of a return does not transfer an allocation to its caller. |
| `Bausteine/Arena/Struktur/Sperre/ArenaSperreRuf.lean`: `rufAt_erk`; `ArenaSperreAbschnitt.lean`: `RErhaelt`, `Rufe` | Calls to recognized bodies preserve `K.Ok` on value/reason returns, including calls in a lock section. | No ownership frame for caller-held allocations, argument-to-parameter ownership substitution, or returned allocation identity. |
| `Bausteine/Arena/Struktur/ArenaFremd.lean`: `Rahmen.frei_lebt`; `ArenaLebt.lean`: `lebt_frei` | Executed release kills the released slot, preserves other live slots and the allocator frame under explicit liveness/invariant premises. | No rule establishes those premises from a consuming function parameter or invalidates aliases in the suspended caller. |
| `Logik/Vertraege/Objekte.lean`: `Obj`; `ObjektRahmen/T1.lean`: `ObjPar`, `ObjRufOk`; `ObjektRahmen/T2.lean`: `rufAt_obj` | Object identity below a table is `(table, slot)`; arguments can name distinct objects; calls obey a write frame. | Separation at one call is not ownership over an object's lifetime. `ObjRufOk` transports a writable footprint, not a right to destroy an allocation. |
| `Kern/Syntax/Syntax.lean`: `Res`, `Signatur`, `nachSig`, `RufPasst` | Locks and declared linear marks are threaded through calls. | `Res` contains only `held` and `marke`; the consumed/produced mark lists do not depend on argument or result values. A carrier owner mark alone cannot identify one dynamically chosen slot. |
| `Bausteine/Arena/ArenaDyn.lean`: `Block.dynAlloc`, `dynAlloc_ueber_commit` | The dynamic allocation form contains `voll`; without committed space it executes that failure continuation. | This bounded-prefix theorem is not a complete semantics/proof of the sampled unbounded heap or physical allocation failure. |

**Verdict:** general ownership transfer of individual allocations across calls is not covered by these judgments. A manually proved
callee with a suitable liveness precondition can execute the existing release block; that is not an automatic theorem for all accepted
programs. Existing `own` pointer loans must keep their meaning: borrowing a carrier does not grant permission to destroy an arbitrary slot.

### 12.2 Alternatives and selected architecture

1. **Keep release in the allocating body.** Smallest change, but prevents ordinary allocator/destructor APIs and returning owned objects.
2. **Use the arena's existing owner mark as the release permission.** Reuses call plumbing, but is too coarse: it neither identifies the
   allocation being destroyed nor prevents a stale index from reaching a reused slot.
3. **Generalize the existing arena recognizer with object ownership and argument/result summaries. Selected.** Reuse `Obj`/`ObjPar`,
   `Lebt`, the allocator forms, and the existing call machine. Extend `Erk`/`ErkE` and their proofs rather than building a second allocator,
   a parallel checker, or a general lifetime language. Keep carrier guards and object lifetime rights as distinct obligations in one
   judgment. Only introduce a core syntax/resource change if the binding/substitution proof needs it; changing `Res` alone cannot solve
   its current lack of argument-dependent identities.

This is a model design, not new source syntax. Choose source notation only after the Lean judgment and its executable check are sound.

### 12.3 Semantic contract and safety obligations

* **Allocation identity.** Reuse `Obj = (table, slot)` for storage, but distinguish successive allocations of that storage by a fresh ghost
  incarnation. Bind aliases to that identity, not to the current occupant of the numeric slot. Allocation creates a right only on success;
  release consumes it. Reallocation of the same slot and whole-arena reset cannot revive old rights. The incarnation is proof state;
  erasure must be proved before claiming that no runtime tag is needed.
* **One owner, scoped loans.** A consuming parameter moves the allocation right out of the caller. Its aliases keep their provenance but
  have no access right. A borrowing parameter temporarily lends access, forbids release/reset/ownership escape, and restores the same
  right at return. No move or release is allowed while a loan is active. Initially loans are confined to calls; stored/escaping loans stay
  refused. Existing carrier `own` loans retain their semantics.
* **Value-dependent summaries.** Describe pre/post rights using typed argument positions and result positions, interpreted in actual
  environments using `ObjPar`-style references. A postcondition relates input identities, the actual output and allocation state; a fresh
  result must be backed by an executed successful allocation. Do not merely mark every index parameter `frei` at entry. Summaries must be
  checked against bodies, not trusted metadata or new named assumptions. Store them with signatures, and extend `SigPasst` so indirect
  calls cannot erase or change the ownership contract.
* **Call and return.** Prove argument substitution, disjoint partition into callee rights and the caller's retained frame, and return
  substitution back to the suspended frame. A consumed object never becomes usable under an old caller alias, even if returned under a
  new owning result. A destructor consumes its input; an identity function can return the same ownership; a factory returns a genuinely
  allocated identity. A declaration alone must never mint a right. Nested and recursive calls obey the same rule.
* **All executable accesses.** Require a valid owner/loan or a proved container access for every arena payload read, write and release,
  including expressions in arguments, returns, guards and indices. Cover direct slot access and pointer views; a copy or computed index
  cannot bypass the rule. In particular, the existing unconstrained payload-index shapes in `ErkE.nutzlast` and `Erk.nutzlast` must not be
  mistaken for a lifetime proof. Proof-only predicates may describe dead storage without authorizing an executable dereference.
* **Containers and reset.** Reuse the existing list/tree ownership transitions: inserting relinquishes the loose owner right to the
  structure, removing grants it back. Preserve rights and contents outside the operation's footprint, including other fields of the
  same table. Whole-arena reset must discharge/invalidate all rights, including those in suspended frames and structures; outstanding
  loans or retained caller rights prevent a callee reset. Generation checking and per-slot incarnation checking must agree.
* **Branches, loops and exits.** Track moves, releases and returned rights on every path, with a sound join and loop invariant. Give every
  value return and every declared reason return an ownership postcondition. Start with uniform effects on consuming inputs across all
  returning outcomes; reject path-dependent effects until the same judgment can express and prove the needed outcome relation. Losing
  knowledge is not a license to abandon a linear obligation. Do not claim eventual release for diverging programs or after hardware stops.
* **Concurrency.** First cover same-thread calls under the existing carrier/allocator guards. Prove the object-right partition across
  active and suspended frames and threads, preserving GA/GX and the current lock invariants. This does not enable new cross-thread
  ownership transfer or lock-free reclamation. Those require a separately proved handoff using the same identities and rights.

### 12.4 RAM availability and mandatory OOM handling

Model an allocation request with success or failure supplied through the program's memory-provider contract. Successful requests establish
freshness, disjointness, extent and access rights; failed requests create no object or ownership right. Any internal payload/metadata
reservation made before failure must be rolled back or remain accounted for. Preserve pre-existing objects and rights on the failure path.
Any stronger promise of sufficient RAM must be discharged as user logic, never silently inserted as a hardware assumption.

The unbounded form must contain a source OOM continuation for **every** allocation, including allocations below `lo`, free-list reuse
and reuse whose pages were returned. The continuation runs if the operation fails; it need not run on reuse requiring no new storage.
Sampling is a policy decision; a positive sample proves no later allocation success. Refused reserve/commit/metadata requests must reach
the declared failure channel, not an injected trap. This obligation does not claim recovery after a platform violates its provider contract.

**Static audit finding, not a measured run:** `crates/gabbro-check/src/arena.rs::reservierung` returns `lo` for sampled and bounded arenas
alike, and `Laeufer::alloc` requires `else` only when the count reaches `lo`. Thus this check alone does not enforce Simon's unconditional
OOM-path rule for a sampled arena with positive `lo`. Add the Lean admission rule first, then a positive-`lo` negative probe without
`else`, its explicit-`else` positive twin, and allocation-failure witnesses. Do not claim the requirement is already enforced end to end.

### 12.5 Implementation sequence and completion evidence

1. **Lean judgments and witnesses.** Define incarnations, right interpretation, checked summaries, entry/exit environments and sound
   substitution in the existing arena/object modules. Exhibit real accepted G bodies: allocate in caller/free in callee; allocate in
   callee/return ownership/free in caller; forward ownership through a nested call; borrow then continue using the owner. Each witness
   must jointly satisfy every premise and execute a store or allocator change. Prove the old no-transfer fragment embeds conservatively.
2. **Preservation on real execution.** Generalize `erk_erhaelt`, `erkE_erhaelt`, `rufAt_erk` and the call-frame bridges to carry ownership
   pre/postconditions and a frame. Connect the ghost incarnation transitions to executed `arenaRumpf`, `freiNimm`, `freiVar` and reset.
   Prove no duplication, no use after move/free/reset, no stale revival on slot reuse, and preservation of unrelated rights/objects.
   Do not assume a callee ownership-preservation premise instead of deriving it from checked bodies. Cover binding calls, reason returns,
   indirect calls and recursion explicitly; any temporarily unsupported case remains a named refusal, not a claimed theorem.
3. **Goal and checker boundary.** Add the executable Lean admission check and prove its soundness over syntax for every program. Integrate
   it into the actual `PrueferX`/`Akzeptiert` and `NutzerPflichtA` path; review any `Spec.lean` change and reprove `gabbro_ziel`, linked/SC
   variants and required GA/GX properties. Standalone arena lemmas are not completion evidence. Keep exactly the standard goal axioms.
4. **Rust/exporter/backend.** Only then implement the same summary/alias flow in the existing passes and exporter. Replace the blanket
   refusal of parameter `free` with the proved distinction between moved and borrowed inputs. Cover returned owning indices, all aliases,
   joins, loops and compatible function pointers without a second ownership pass or a bypass. Model runtime consequences before changing
   lowering; prove erasure and the source-to-model bridge. Final-byte validation remains separately open until its own proof lands.
5. **Negative and resource witnesses.** Reject double free split across caller/callee, use through a saved alias after a consuming call,
   freeing a borrow, duplicate consuming arguments, reset while a frame retains a right, a fabricated owning result, and an old handle
   after the slot is reused. Include success and provider-refusal/OOM runs, also positive-`lo` sampled allocation without `else` as a
   refusal. Prove semantic counterexamples when a necessary premise is removed; checker poison probes alone are insufficient.
6. **Acceptance.** Run the four existing guardians, including `#print axioms gabbro_ziel`, the Lean layout check and Rust tests with
   `--no-fail-fast`. Measure corpus diagnostic changes; ownership-transfer examples may newly pass, unsafe programs must not become
   accepted. Record proof, checker/exporter and binary evidence separately. Until these gates pass, this section remains a plan and
   section 8's open item stays open.

### 12.6 Implementation evidence (2026-10-24, in progress)

`grammatik/Grammatik/Bausteine/Arena/Ownership/` now contains the ghost ledger (`State`), its refinement of the existing G allocator
(`World`), the recursive call-contract theorem (`Calls`), generic source destructor/identity bodies and their proofs (`Bodies`), the
consuming G-call rule (`Boundary`), and joint witnesses (`Witness`). `Grammatik.lean` imports the witness and hence all six modules.

Proved: a successful move changes the owning grant without changing allocation identity; release consumes the grant; loans prevent
release and restore the lender; slot reuse cannot revive an earlier grant. The executed `freiVar`, fresh `arenaAlloc` and free-list
`freiNimm` update exactly the live cells described by the ledger. `rufAt_ownership` derives contract respect at every recursion fuel
from `Bodies`; `consume_call` connects a transferred argument to an actual G call and destruction. The joint witness calls the actual
source destructor through `rufAt`, changes the free-list head from 4 to 0, and denies every saved caller alias access afterwards.

Validation of this increment: targeted Lean compilation of the six modules; the displayed main/witness axiom lists contain only
`propext`, `Classical.choice`, `Quot.sound` (or a subset). No new axiom or proof hole. This is **not full closure**: `Bodies` remains a
semantic body obligation, not yet a computed source ownership judgment; owning result admission, all executable alias uses, general
source certificates and the `Akzeptiert`/`gabbro_ziel` integration still need the steps in 12.5. The Rust checker and binary are unchanged.


The next checked increment adds `Factory`, `Return`, `Borrow`, `FactoryWitness` and `Source/`. The actual source factory handles provider
refusal, fresh allocation and free-list reuse with explicit failure continuations. Generic result rules return ownership to the caller
or restore a scoped loan. A joint G witness allocates in the callee, returns the actual slot, and frees it in the caller; a separate
executed OOM witness preserves the empty ledger.

The source context assigns copied/widened references one origin and tracks grants separately from numeric values. Its executable
expression admission, consume check, binding and allocation-context rules have soundness proofs over the existing G syntax. The
source free witness executes G's allocator update and proves that the saved alias is rejected; reusing the same numeric index admits
only the new origin. `Ownership/Audit.lean` imports these results. The targeted build passes (580 jobs), with standard axioms only.
These source rules are still primitives: they do not yet constitute a complete function-body checker or remove the whole-program
integration obligations above. Quantified/range arena expressions currently have an explicit conservative refusal.


### 12.7 Source-certified calls and exact remaining integration (2026-10-24)

The ownership contracts now describe framed effects rather than one exact allocator invocation. A destructor removes precisely the
selected allocation, preserves every other cell and never decreases the grant clock. An owning identity/forwarder returns the same
allocation with a current grant and preserves every other cell; a borrow restores the original ledger. This admits nested transfers
without weakening the caller's frame or confusing allocation identity with the current grant.

`Source/Admission.lean` defines syntax-indexed `CheckedBody` certificates for source identity, destructor, fallible factory, consuming
forwarder and owning-result forwarder bodies. No constructor accepts a semantic preservation premise. `checked_bodies` derives the
former `Bodies` obligation from those source certificates; `checked_calls` consequently proves actual `rufAt` contract respect for
all recursion budgets. The destructor and factory witnesses now instantiate this source judgment. This is a **restricted source
judgment**, not an executable whole-language checker: other G body shapes have no certificate yet.

`Source/Calls.lean` derives the consuming caller-context update from the selected actual argument expression. `Source/Results.lean`
gives a returned owner a new source origin, retains old aliases as consumed, and preserves unrelated owning and borrowing grants.
Factory reasons preserve the complete caller context for arbitrary initial states, not only an empty-heap example. Source parameter
provenance, expression substitution and a shared owning-binder rule connect these judgments to actual argument/result values.
`ArgumentFlow` checks typed argument lists, rejecting repeated owners and either ordering of loan/owner overlap; its generic rejection
lemmas and concrete negative witnesses are proved. It is not yet a complete multi-argument runtime handoff theorem.

`Source/ForwardWitness.lean` instantiates all source-certificate and execution premises jointly: one real G function calls another,
returns its owning result, and the caller frees that returned object. Old grants are unusable, the old source name is refused, and the
new result name is admitted. A second actual G call borrows the object, cannot release it, and restores the exact original owner grant.

Validation: the ownership audit builds (590 jobs) and the complete library builds (2,218 jobs); audited declarations use only standard
axioms. Layout and whitespace checks pass. The primary `gabbro_ziel` statement and its user/hardware assumptions are unchanged.
**Still open, so the requested full gap is not closed:** general source-body admission (including joins, loops, compatible indirect
calls and full argument handoff), preservation at every real GA/GX prefix, integration in the actual `Akzeptiert`/`PrueferX` and reviewed
goal path, and the Lean front-end/exporter bridge. The new certificates are not that missing central admission check. No Rust or final
binary claim follows. Do not move any of these missing memory proofs into `NutzerPflichtA` or RAM/hardware assumptions.


## 13. Explicit unbounded storage component (2026-10-24, implementation in progress)

Simon authorized building an opt-in region without a declaration-time element ceiling, with fallible allocation and the existing
termination classes and proof obligations retained. This replaces the earlier “not authorized” note in the universality work.
The sampled no-`max` form in section 5.3 still has a `u32::MAX` counter ceiling in the production backend; it is not this new model.

### 13.1 Implemented semantics and proved properties

`grammatik/Grammatik/Bausteine/Arena/Unbounded/` contains `State`, `Safety`, `Lifetime`, `Runs`, `Execution`, `GForm`, `Realization`,
`Witnesses` and `Audit`. This is a Lean storage component with partial, explicit connections to G, not a newly admitted source feature.

* `Capacity.bounded maximum` and the explicit `Capacity.unbounded` use the same operations. Each state has an `extent` and finitely
  supported live payloads. There is no fixed maximum in the unbounded case. `no_static_memory_bound` proves that repeating one fixed
  allocation operation retains more payload cells than any proposed bound; `finite_payload_support` proves every individual valid
  state is finite. The beyond-`u32` witness specializes that theorem without trying to allocate billions of cells during a test.
* `Ref region` brands references by region and exposes no integer constructor. Payloads have one fixed Lean type per heap. The heap
  reuses `ArenaOwnership.State` for allocation incarnations, grants, exclusive owners and scoped loans. It does not invent a second
  ownership protocol. The payload map is the new component's storage; `PayloadRepresented` explicitly relates it to existing G memory.
* Every `allocate` consults an explicit provider answer, including free-list reuse. `allocateThen` requires both success and failure
  continuations; refusal invokes the latter on the unchanged heap. Positive availability still respects a bounded policy's ceiling.
  No OS behaviour or RAM availability is a new axiom. Availability remains an obligation of the program's own provider binding.
* Read/write require the current owning or borrowing grant. Release invalidates all aliases of that allocation; reuse issues a fresh
  incarnation/grant. A move issues a fresh grant and stays on the same thread. Loans suspend the lender's access and prevent release;
  ending the loan restores the exact original heap. Reset checks all live owners and loans by traversing a finite range; its checker
  is equivalent to `ArenaOwnership.State.canReset`, including rights held in suspended frames. Reset preserves the grant clock.
* `Step.preserves` and `Reachable.valid` cover arbitrary mixed executions of all storage operations. `Reachable.read_safe` establishes
  live, in-bounds storage for every successful read. Access exclusivity covers read/write operations between distinct frames. These
  are component theorems; they are not a proof of G's multicore scheduling or its whole-program contracts for a new heap construct.
* A finite list of allocation requests always completes or returns an explicit OOM prefix (`allocateList`), even for a provider that
  always refuses. No allocation inserts a retry. Arbitrarily many successful allocations are conditional on the explicitly successful
  provider answers in `Allocations`; the theorem does not promise unlimited physical RAM or decide arbitrary program termination.

### 13.2 Executed G connection and exact remaining boundary

`Block.allocationAttempt` uses G's existing checked branch with mandatory failure and success continuations. Its refusal/available
execution equations include the actual recorded reads, and `allocationAttempt_termination` preserves both branches in the existing
termination analysis. It assumes no provider success. A finite physical allocator retains its own full/failure branch on the success
side; the guard alone is not proof that an allocation can succeed.

`physicalIndex` lowers an actual live reference only after its grant and the finite realisation's extent have been established.
`read_execution` proves a G slot expression reads the represented payload. `fresh_payload_execution` executes the real G allocation
instructions and proves agreement of payload, live grants, ownership and free-list safety after the allocation. Its witness stores
byte 7 in an initially empty four-slot G arena. This is a **single-operation finite realisation**, not a universal program obtained by
increasing a static capacity, and not the missing unbounded whole-program simulation.

Still required before production acceptance: represent region references and allocation outcomes in the admitted language/declaration
and G execution; prove the generic whole-program ownership/heap simulation and extend the reviewed goal statement where necessary;
check all source alias uses and owning call results (section 12); model provider freshness/disjointness and costs as user logic;
update the Lean front end, exporter and GabbroV bridge; then implement the Rust checker, compiler and source documentation. Physical
address/counter exhaustion must go to the ordinary failure continuation rather than become an ideal-model ceiling or an inserted trap.
The new component has not yet been enabled in Rust. There is no full Turing-completeness claim.

Validation of this increment: the dedicated Lean audit builds successfully (810 jobs), and the complete `Grammatik` plus audit build
succeeds (2,188 jobs). The 64 audited declarations use only standard axioms,
and `gabbro_ziel` still has exactly `propext`, `Classical.choice`, `Quot.sound`. Joint witnesses exercise reuse/stale aliases, double free,
OOM on reuse, movement, exclusive loans, reset, the bounded policy, mixed executions and actual G payload/refusal execution.


### 13.3 Linked-stack machine backend and conditional bounds (2026-10-24)

`Unbounded/{Frame,Linked,Observe}.lean` adds cell-level framing and an actual linked stack on the same heap. Push allocates a node
containing one value and one region reference; pop reads and releases the head. The representation theorem preserves all remaining
nodes' grants/payloads. Distinct cells in a well-formed chain bound its length by the current heap extent; `readAll_extent` therefore
observes real linked cells with finite fuel computed from the heap itself. No list-valued stack oracle sits in finite control.

`Berechenbarkeit/Storage/{TM2Heap,TM2Execution,TM2Initialize,TM2Run,TM2Observe,TM2Cost,BrainfuckHeap,BrainfuckBounds,HeapWitnesses,HeapAudit}.lean`
implements Mathlib TM2's push/peek/pop/load/branch/goto/halt using region-branded linked cells. Each stack has its own region brand.
The finite control retains its original labels and local values, plus one optional reference per stack. Input loading really allocates
cells; OOM returns the already allocated prefix for the caller to handle. Normal halt, fuel exhaustion, OOM and invalid storage are
separate outcomes. Representation invariants exclude invalid storage; arbitrary provider refusals preserve safe intermediate storage.

`BrainfuckHeap.compiler_correct` proves that **every well-formed byte-Brainfuck program** has exactly the same normal halting/output
behaviour in this heap backend when allocations are available, starting from the actual allocated input. The exact finite-budget
correspondence includes one silent entry/halt transition for empty source code. `run_sound_any` proves provider refusal cannot fabricate
a normal guest halt; `divergence_preserved` rules out a spurious halt at every budget, including when allocation may fail. Computational
witnesses execute transfer (19 transitions), nested loops (40), byte wrapping, empty code, insufficient fuel, input/output OOM and
output before divergence. A separate push/load/peek/pop witness checks real head retention and release.

`TM2Cost.Counted` and `Driven` are faithful traces of the executable interpreter. Every finite statement tree has a computed operation
bound, including failure paths. Compiled Brainfuck uses at most four abstract heap/control operations per transition. A supplied finite
halting trace of `k` source transitions yields a target termination certificate with at most `4 * (k + emptyEntry)` such operations.
Input loading and output observation are separate finite procedures. These are **abstract operation counts**, not CPU-cycle, allocator,
provider-latency or hardware WCET bounds. No general halting decider or relaxed termination class is added.

Validation: full `Grammatik` plus `HeapAudit` build succeeds (2,213 jobs). The 68 new audit entries and the original storage audit's 64
entries use only standard axioms; the goal keeps exactly the standard three. The Rust checker/compiler are unchanged. The remaining
boundary in 13.2 is still binding: this is a proved executable heap backend, **not yet an admitted whole-program unbounded G construct**.
The next bridge must execute the stack protocol in G and prove source admission, initialization and final normal return, rather than
claim universality from a family of independently bounded programs.

### 13.4 Actual G stack execution and finite program witnesses (2026-10-24)

`Berechenbarkeit/Storage/GStack/` now proves value-sensitive stack operations over the existing G instructions. `Represents` reads
payloads along a live, acyclic linked chain; it is not an uninterpreted stack interface. `linkPush_values`, `linkPop_values`,
`fresh_allocated`, `reused_allocated`, `push_values` and `popAndRelease_values` execute the concrete link/counter/free-list stores,
preserve the old value sequence, save a popped payload before freeing its cell, and establish free-list safety. Prefix equations
quantify over every continuation, so composition does not replace the continuation with a test-only body. Fresh and recycled
allocation share one push implementation and theorem. `tryPush_refused` retains the explicit provider failure continuation.

Joint witnesses execute fresh and recycled push/pop/free cycles, including reuse in front of a nonempty old stack. A whole finite G
program binds its own input and sink, executes the cycle, saves byte 7 in the caller local, releases the cell and returns normally.
The existing core `Akzeptiert` computes true for this program, and its termination class computes to `endet`. Separate witnesses
exercise provider refusal despite available room and the empty-pop branch. This is an instantiation of the old core checker, not
integration of the proposed ownership/source checker or a proof that every arbitrary initial arena satisfies the representation.

The stack prefixes introduce no loops or recursive calls. The `*_termination` equations retain exactly the continuation's extracted
behaviour plus every supplied failure branch; they do not prove that an arbitrary surrounding controller halts. The finite program
witness is proved by composing the semantic prefix theorems, avoiding repeated normalization of the entire functional memory.

**Boundary unchanged:** actual G indices still have `D.count A.tab` as their bound. These are generic proofs of the concrete operations
needed by the bridge, not an unbounded G declaration, a whole TM2/G compiler or a new universality theorem. `popAndRelease` also exposes
the dead internal index to its continuation; full source admission must reject reference use after release. No ownership check is
silently inferred from the old `Akzeptiert` witness. Section 13.2's source, whole-program, goal, provider and Rust obligations remain.

History: `7fd5ea1d` includes concurrent ownership-source work as well as the heap backend; `32afd758` checkpoints the G stack prefix
files alongside independent ownership work. The successful combined library/heap/ownership build after `7fd5ea1d` measured 2,221 jobs.
The dedicated G stack audit checks its declarations and imports the earlier heap audits; this does not constitute independent review
of the separate ownership-source integration.

Validation: full `Grammatik` plus `GStack.Audit` build succeeds (2,230 jobs). The 36 new G-stack audit entries and the earlier 68/64
heap/storage entries use standard axioms only; `gabbro_ziel` retains exactly the standard three. The no-holes/axiom guardian stages,
the 1,063-file Lean layout check and whitespace check pass. No Rust or binary validation is claimed for this Lean-only increment.

### 13.5 Ownership grants across concrete G push/pop (2026-10-24)

`Allocated` now specifies the exact live-set change, replacing its weaker monotonicity/new-cell pair. Fresh allocation and free-list
reuse both prove that the selected slot is the only newly live slot. `popAndRelease_values` likewise states the exact removal.
`GStack/Grants.lean` derives `push_owned` and `pop_owned` by combining these executed prefixes with the existing ownership ledger.
Push issues one fresh incarnation/grant; link stores issue none. Pop saves the payload before release, invalidates every handle at
the released slot in every frame, and retains every other ledger entry. This is a semantic bridge, not a new source admission rule.

`GrantWitnesses.Cycle` observes the actual G code, stored byte, free-list invariant and ownership transitions jointly. Fresh and
recycled witnesses instantiate it, with the recycled fixture retaining a nonempty old stack and live allocations owned by another
frame, including a cell outside that stack. The complete ledger agreement premise checks those cells too. The old checker witness
still does not imply general ownership admission; the remaining obligations in 13.2 and 13.4 are unchanged.

Validation: full library plus G-stack audit succeeds (2,232 jobs); all 45 G-stack audit entries use standard axioms only. No-holes,
goal axioms, 1,065-file layout and whitespace checks pass. No production source admission or Rust implementation is changed.

### 13.6 Exact termination boundary for an actual G stack loop (2026-10-24)

`GStack/Drain.lean` composes the real pop/free code with the existing `runsUntil` abbreviation. Its logical guard reads the actual
stack head and tests the empty sentinel. `drain_trace` constructs an `ExitTrace` of the existing G loop evaluator from every
represented, free-list-safe input stack: each continuing pass removes exactly one cell, and the final pass observes the empty head.
`ExitTrace.length_unique` proves that deterministic execution cannot reach its first normal exit at two distinct pass counts.

`drain_iff_budget` gives the exact boundary, under those initial representation/safety premises:

```
normal completion at budget p  <->  initialStack.length < p
```

Thus a stack of length `n` needs exactly `n + 1` loop passes, including the last guard check. `drain_bound` also establishes the empty
output representation, unchanged caller environment and retained free-list safety. It assumes no provider success and no eventual
truth of an arbitrary condition; the proof derives the guard's eventual truth from the decreasing represented stack length.
This measures G loop fuel, not primitive instructions, CPU cycles, allocator latency or hardware WCET. It neither bounds an arbitrary
Brainfuck computation nor decides its halting. Section 13.3's abstract operation bound remains a separate theorem.

`DrainWitnesses` instantiates both directions with two cells, rules out normal completion at budget 2, supplies normal completion and
empty output for every budget at least 3, and checks the empty-stack boundary. A complete finite G function executes the loop and
returns normally. The existing core checker accepts it; its existing structural class stays `bedingt`. The semantic bound is a
separate Lean theorem about represented inputs, not a silent classifier change or a newly installed source-certificate interface.
All source/goal/unbounded-G boundaries from 13.2 remain open.

Validation: full library plus G-stack audit succeeds (2,234 jobs). All 58 G-stack, 68 heap-backend and 64 storage audit entries use
standard axioms only; the primary goal keeps exactly the standard three. No-holes, goal axioms, 1,067-file layout and whitespace checks
pass. The whole-function proof composes the loop execution equation instead of normalizing its entire functional memory.
