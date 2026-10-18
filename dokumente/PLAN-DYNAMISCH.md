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
   phases 1–3 cover; everything else stays refused by name. Run `cargo test --test zertifikate -- --nocapture`: the booked success
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
| the recognizer | PROVED FOR THE LIST (and the free list). `Erk a b a'` (`ArenaErkenner`): a body is accepted iff it is built from the proved moves (alloc from counter / free list, `free`, push, pop, unlink, head and successor reads, `grow`, guards with a store-free `else` (`Rein`), payload stores, branches) over an abstract state per bound variable (`frei` owned, `glied` member, `offen` unknown; the Lean model of the `N586` name table). **`erk_erhaelt`**: `Erk a b a'`, `StrukturOk σ`, `Passt a σ ρ` give `StrukturOk` at EVERY exit of the run of `b` and `Passt a'` when it falls off; **`erk_koerper`**: a body that knows nothing at entry. The proof applies the executed-form theorems; their hypotheses are exactly what the abstract state says. Witnesses: `nimmPush_konkret` and `kopfUnlinkFrei_konkret` RUN accepted bodies on the real arena; planted defects with NO derivation (rejected through the soundness theorem and a real run): `nimmPushPush_abgelehnt` (a slot linked twice), `nimmFreiFrei_abgelehnt` (double release), `nimmFreiPush_abgelehnt` (use after release), `pushFremd_abgelehnt` (a slot the body does not own). | `ArenaErkenner`, `ArenaErkennerLemmas`, `ArenaErkennerBeweis`, `ArenaErkennerZeuge`, `ArenaAuf` |
| sibling consistency (O6), abstract half | PROVED over the abstract binary tree. `SibF` (first child has parent `j`, next sibling has the parent of `j`); the slots after a leaf in/out (`einfuegen_mitglieder`, `blatt_aus_mitglieder`); `sib_einfuegen_links/rechts` (the new child gets parent `p`, the new sibling the parent of `p`), `sib_blatt_aus_*`; planted defect `sib_ohne_vater_bricht` and concrete witness/defect (`sib_einfuegen_zeuge`, `sib_defekt_bricht`). | `ArenaSibling` |
| hash chain, abstract half | PROVED over the abstract link function. `HashOkF` (every bucket a `ListOkF`, chains pairwise disjoint); `hash_push` (the slot is on NO bucket), `hash_pop`, `hash_unlink`; witness `hash_push_zeuge`, planted defect `hash_defekt_bricht` (a slot on two buckets). | `ArenaHash` |

**Still open inside phase 2 (not claimed):**
* the recognizer for the TREE bodies (the executed tree forms exist; their hypotheses "member of the tree", "empty child
  place", "leaf" are not yet tracked by an abstract state with guards), and for bodies that hold a list AND a tree on one
  arena;
* the recognizer is NOT yet a component of `Akzeptiert` and `Spec.lean`/`gabbro_ziel` do not mention it (8a.3 stays a
  proposal): there is no generic statement that every ACCEPTED unit's writers of a dynamic structure are `Erk`-derivable,
  and no `Block` that the Rust checker accepts is translated to an `Erk` derivation (the exporter does not exist for these forms);
* executed forms for the parent store of the capability tree (`par[i] = p`), for `revoke` (cutting a whole subtree: needs
  `blatt_aus` for subtrees and the release of each slot), and for a bucket head held in a TABLE field (the hash
  chain's `hd` is an abstract function today, not a field read through `Wert.umTyp`);
* a recognizer rule for loops (`traverse`, `retry`, `forever`) over structures: a body with a loop that moves a link is
  not derivable;
* the vocabulary is closed: any other store into a link field or head, a `bind` that copies an owned index (aliases),
  a call that may move a link, has no derivation and is refused; widening it means a new constructor with its theorem;
* a link field that holds an index of ANOTHER arena (decision (b) says: not in scope).

### 8a.2 Concurrency of arenas (O20): design note, phase 3, nothing built yet

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
* **Next steps:** (1) the section theorem `abschnitt_erhaelt`: a body built only from the proved moves preserves
  `S.inv L` from acquire to release; (2) `dynGrow_fremd` (DONE 2026-10-18 as `nachGrow_gleich`, `grow_liste`, `grow_baum` in `ArenaWachs`); (3) the slot-ownership predicate for the ABA point (the recognizer's `frei` status is the single-thread form of it).

### 8a.3 Proposal (NOT applied): the `Spec.lean` diff for step 4

Today an invariant is an `Expr ... .bool` over a table's carriers (`Programm.invariante`, `InvTraeger`, `InvRuheG`,
`InvSichtG`). A chain or a tree is not a bounded boolean expression (no quantifier over a growing index set), so the
dynamic structures need their own declaration form and their own `Holds`, beside `D.invs`, not inside it.

1. `Deklaration` (Kern, Syntax.lean) gets one field with a default, so every old declaration keeps its meaning:
   `dyn : List DynForm := []` where a `DynForm` names the arena table, counter, free head, free link and ONE structure
   `liste (kopf, lnk) | baum (wurzel, lft, rgt)` (the data of `LinkFeld`/`LinkKopf` in `ArenaListe.lean`; the types move
   down into Kern so that `Spec` can mention them, the lemmas stay in Bausteine).
2. `Spec.lean` gets two legs, shaped exactly like `invRuhe`/`invSicht`:
   * `DynRuhe P M0 M := ∀ s ∈ D.dyn, DynHaelt s (M0.speicher.welt []) → DynZu M s → DynHaelt s (M.speicher.welt [])`
   * `DynSicht P M0 M := ∀ s ∈ D.dyn, DynHaelt s (M0 ...) → ∀ t, (no frame in a writer of s) → (holds a guard of s's table)
     → DynHaelt s (M ...)`
   with `DynHaelt s σ := FreiOk ∧ ListOk (or BaumOk)` and `DynZu` = no unfinished thread has a frame of a function
   whose effects write one of the structure's fields or words. For a shared arena `S.inv L` additionally contains `DynHaelt`
   (`sperrWechsel` then carries the section theorem of 8a.2).
3. `Ziel` gets `dynRuhe`, `dynSicht` as new conjuncts; every old conjunct stays word for word. The NOT CLAIMED entry
   "dynamic unbounded data structures" shrinks to: heap without a ceiling, recursive types, links across arenas,
   hash chains until proved.
4. The premise side: (a) gets a rule that every function that writes a structure field or word is a `maintains`
   function whose body the Lean recognizer matches against the proved moves; (b) stays as is (user logic: `requires`,
   `ensures`); a DynForm in a unit is only exported when the recognizer accepts every writer.
5. Proof: `gabbro_ziel` gets the two legs from the section theorem (8a.2) and the preservation theorems of 8a.1 by the
   same induction over machine steps that proves `invRuhe`; the axioms stay `propext`, `Classical.choice`, `Quot.sound`.
   Review: two independent verdicts as for every extension of the goal (AGENTS.md section 1).
   Status 2026-10-18: the premise of item 4 (a recognizer whose acceptance yields the invariant) is PROVED for list bodies
   (`erk_erhaelt`, 8a.1); still missing before this diff may be applied: the tree recognizer, loops, the wiring of the recognizer
   into `Akzeptiert` (a Bool `dynB` over the writers of every declared structure), the per-structure `DynForm` declaration in
   `Kern/Syntax`, and the lock-section theorem of 8a.2. Until those exist the diff would claim more than is proved; it is a proposal.

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
