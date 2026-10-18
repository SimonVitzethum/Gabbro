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

**What is proved in step 3** (`grammatik/Grammatik/Bausteine/Arena/Struktur/Sperre/`, 12 modules, imported by `Grammatik.lean`; axioms `propext`/`Classical.choice`/`Quot.sound`
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
    (`Block.arenaAlloc`), not by `komSt` (`Block.dynAlloc` is not a recognized form); the executed forms' frames name the link words, not `zaehl`/`komm`; and `Erk.wachs` accepts
    `n < 0` (`wachs_negativ_schrumpft`: `komm 2 -> 1`; the surface demands `n >= 1`, `R-grow-const`). The theorems say: the commit never breaks anything the structures read
    (`grow_atomar`) and is a lock-guarded carrier (`komm_nur_halter`); "every live slot is committed storage" needs (a) `n >= 0` in `Erk.wachs`, (b) a `dynFrisch` constructor
    over `Block.dynAlloc`, (c) the frame of every form extended to `zaehl`/`komm`. Lean-only repairs, not done.
 5. **The machine bridge covers loop-free writers.** `EndR` has no guard inside a loop body (`narrow`/`check` need `Block D V false`), so a recognized body with a loop is a statement about
    `execEnd` (`erkE_koerper`) only; its machine correspondence needs the loop fragment extended to guards.
 6. **`Erk` and `EndR` are two separate derivations.** `erkE_maschine` takes both as premises; there is no theorem `ErkE (loop-free) → EndR`. For an accepted unit the checker's
    `programmImFragmentG` supplies the coverage and the exporter would supply `ErkE`; the embedding would remove the double certificate.

**Still open in 8a.2 (not claimed):** the ownership predicate for the ABA point across a release (a slot a thread holds is not on the free list unless that thread freed it; the cross-thread
form of `N586`); two sections commute up to slot names; per-thread arenas need nothing new (the legs above do not mention them); a lock-free free list (Treiber) is Phase B item 5;
the commit bound (finding 4); the footprint repair (finding 1).

### 8a.3 Proposal (NOT applied): the `Spec.lean` diff for step 4 (revised 2026-10-18, third pass)

**Design change against the first proposal.** The first proposal added two new legs `dynRuhe`/`dynSicht` beside `invRuhe`/`invSicht`. The
third pass shows a cheaper and more honest route: **a declared arena is one more INVARIANT NAME of `D.invs` whose meaning is `Dekl.Ok`
instead of the evaluation of an `Expr`**. Then `invRuhe` (every invariant that reads only its carriers and held at the start holds
whenever no thread is inside a writer) and `invSicht` (the same for a thread that holds a guard) become contentful for dynamic structures
WITHOUT a new leg, with the machinery that proves them today (`invRuheG_aus`, `InvZu`, `schuldet`). What changes is where the obligation
"every writer restores the invariant at its return" comes from: for an ordinary invariant it is user logic (b) (`InvGutSA`); for an arena
invariant it is the recognizer, a premise on the unit that Lean checks (`erkE_koerper`).

All of it is modelled in Lean already except the wiring; nothing below is applied, and `Spec.lean`, the Rust checker and the exporter are unchanged.

**D1. `Kern/Syntax` (the declarations move down; their lemmas stay in `Bausteine/Arena/`).** New file `Kern/Syntax/Arenen.lean`, imported by
`Syntax.lean` before `Programm`, holding only the STRUCTURES: `ArenaForm`, `DynForm`, `FreiForm`, `LinkFeld`, `LinkKopf`, `ListDekl`,
`BaumDekl`, `Dekl`. (They mention only `Deklaration`; `Wert.umTyp` is needed for the readers `wert`/`st`, so the readers move with them.)
`Programm` gets ONE field with a default, so every old program keeps its meaning:
```
structure Programm where
  invariante : ...                                   -- unchanged
  ...
  unterbricht : D.Fn → Bool := fun _ => false        -- unchanged
+ /-- `i` names the invariant of a declared ARENA (Phase A): its meaning is `Dekl.Ok`, not the evaluation of `invariante i`. -/
+ arena : D.Inv → Option (Σ A : FreiForm D, Dekl A) := fun _ => none
```
and `Deklaration` needs no new field: the carriers of an arena invariant are the arena's table and the words its `Dekl` reads, listed in
`D.traeger i` as for any invariant (`D.traeger`, `D.braucht` give the guards).

**D2. `Spec.lean` / `ZielOrt/Rahmen/ZielOrtInv.lean`: the meaning of an invariant.**
```
  def InvHaelt (P : Programm D) (i : D.Inv) (σ : World D) : Prop :=
-   wahr? (eval σ (P.invariante i) σ .nil) = true
+   match P.arena i with
+   | none => wahr? (eval σ (P.invariante i) σ .nil) = true
+   | some s => s.2.Ok σ
```
`InvTraeger P i` (the invariant reads only its declared carriers) is proved for an arena invariant by a lemma `dekl_ok_traeger` (the words
`Dekl.Ok` reads are the words `D.traeger i` lists) instead of the `.orte` computation; the premise "the arena declares its words in
`D.traeger`" is a field check of the exporter (a Prop in the unit, see D4). `InvRuheG`, `InvSichtG`, `InvAmRueck`, `schuldet` are used
unchanged; `Ziel`/`ZielF`/`ZielX`/`ZielFX` get NO new conjunct, every old conjunct stays word for word.

**D3. The writer obligation for an arena invariant (premise side).** For `i` with `P.arena i = some s`, `NutzerPflicht`'s `InvGutSA` is not
demanded (the user does not prove it); instead the unit carries, for every function that owes `i` (`schuldet f i = true`), a recognizer
derivation of its body:
```
+ structure DynZeuge (P : Programm D) : Prop where
+   schreiber : ∀ i ∈ D.invs, ∀ s, P.arena i = some s → ∀ f, schuldet f i = true → ErkE s.2 Abs.leer (P.rumpf f)
```
`ErkE` is a Prop; the derivation is a proof term the EXPORTER writes and Lean's kernel checks, so nothing about the Rust side is trusted.
Where it lives: as a field of `Einheit` (`dynZeuge : DynZeuge P`, a Prop-valued field with no default, so every unit carries it; for a
program without arenas it is `by intro i hi s hs; simp [Programm.arena] at hs`-trivial), not in the Bool of `AkzeptiertSpec`
(the Bool would need a decision procedure for `Erk`, which does not exist and would need `DecidableEq` on `Block`). The one generic theorem
that connects it to the proof of `invRuhe`:
```
+ theorem invGutS_arena : ErkE s.2 Abs.leer (P.rumpf f) → <the arena part of InvGutSA>   -- from `erkE_koerper`
```
`InvGutSA` runs `execEndH` (lock invariants and havoc); a recognized body has no `locks` statement, so `execEndH = execEnd` on it
(a generic lemma `execEndH_eq_execEnd`, to be proved: induction over `Endblock` with no `Stmt.locks`).

**D4. The statement.** `gabbro_ziel` gains no conjunct; the NOT CLAIMED entry "dynamic unbounded data structures" shrinks to: a heap without a
ceiling, recursive types, links across arenas, hash chains and the sibling demand until their recognizers exist, bodies that call a function, a
walk that releases every slot of a revoked subtree, `leave`/`next` in loop bodies. `Einheit` gains the one field of D3.

**D5. The proof of the new content.** `invRuheG_aus` needs, for every invariant, (i) the invariant at every function RETURN of a function that
owes it (`InvAmOrtG`, here from `invGutS_arena`), (ii) the invariant at the start memory (a hypothesis of the leg), (iii) that a step of a thread
outside every writer of `i` moves no carrier of `i` (the footprint of `schuldet`: `TraegerGleich`). All three are statements about carriers and
returns, not about the shape of the predicate, so the induction over machine steps is the existing one; the two places that read the predicate
(`InvTraeger`, the evaluation) are D2. Review: two independent verdicts, as for every extension of the goal (AGENTS.md section 1).

**Premises of the diff, status after step 3 (2026-10-18; each line says proved or open):**
 1. the section theorem for SHARED arenas: **PROVED** (`abschnitt_erk`, `abschnitt_rufe`, `abschnitt_start`, `arena_ziel`, `grow_atomar`; 8a.2). The ownership predicate of the ABA
    point across a release stays OPEN; for a per-thread arena the three points of D5 suffice.
 2. the bridge from the machine-G steps of a writer's frame to the big-step `execEnd` that `erkE_koerper` talks about: **PROVED for loop-free writers** as `erkE_maschine`
    (`rufG_adaequat_ruf` + `erkE_koerper`; premises: coverage `EndR`, certificate `ErkE`; witness `erkE_maschine_zeuge`). OPEN: writers with loops (the machine fragment has no guard inside a
    loop body), and the embedding `ErkE (loop-free) → EndR` that would remove the double certificate.
 3. `execEndH_eq_execEnd` for bodies without `Stmt.locks`: **PROVED** for the recognized fragment (`erk_ohneLocks`, `erkE_ohneLocks`, `erkE_execEndH`; the generic statement was
    `Endblock.execH_ohne` already); `dekl_ok_traeger`: **PROVED** as `Dekl.ok_gleich_wort` (the invariant reads only `Dekl.orte`, and not the trace).
    D3's `invGutS_arena`: **PROVED** as `invGutSD2_arena` against `InvHaeltD2` (the proposed meaning), with the entry premise `hein` (finding 2 of 8a.2).
 4. the exporter writing `ErkE` derivations (Rust `lean_g.rs`): OPEN (the vocabulary is closed; a form outside it stays refused by name).
 5. calls inside writers (the recognizer has no call constructor; the CALL form of the SECTION is proved, a writer that calls a helper is not), the hash and sibling recognizers, the release
    of a whole revoked subtree: OPEN.
 6. the migration D1: **NOT DONE; analysed.** The eight structures (`ArenaForm`, `DynForm`, `FreiForm`, `LinkFeld`, `LinkKopf`, `ListDekl`, `BaumDekl`, `Dekl`) mention only `Deklaration`
    (and `Ty`), so their declarations can move; their readers (`stand`, `komSt`, `wert`, `st`) need `World` and `Wert.umTyp` and stay in `Bausteine/Arena/`. But `Programm` lives at the END of
    `Kern/Syntax/Syntax.lean` (line 653) in the same file as `Deklaration` (line 111): a new `Kern/Syntax/Arenen.lean` that `Syntax.lean` imports cannot import `Deklaration`.
    The migration therefore needs `Syntax.lean` split at the `Deklaration` boundary (`Syntax/Deklaration.lean`, `Syntax/Arenen.lean`, then the rest) or the structures inserted into
    `Syntax.lean` before `Programm`; either changes the root of the Lean tree, so the whole of `grammatik/` rebuilds (~800 files, one lake run at a time), every positional `Programm`
    literal needs the new field appended (`none` / `fun _ => none`), and the namespace of `DynForm` (`ArenaDyn`) is renamed at its uses. Measured here: nothing built; this needs a
    sitting of its own and the build to be green before the diff is reviewed.
 7. NEW (finding 1 of 8a.2): the footprint. `schuldet`/`InvTraeger` count tables only; `pop` and `wurzelAus` write only a head word; D5 (iii) needs either `traeger : Inv → List (Tab ⊕ Glob)` or an
    arena case in `schuldet` (`K.orte.any (writes f)`). DECISION needed (Simon): it changes `Deklaration` or `schuldet`, both in the statement.
 8. NEW (finding 2): the arena at entry (`hein`): a pseudo-`requires` the exporter writes, or the premise that writers are called inside a section / a closed machine.
 9. NEW (finding 4): the commit bound `stand <= komSt` is not part of the lock invariant; Lean-only repairs (`n >= 0` in `Erk.wachs`, a `dynFrisch` constructor, frames over `zaehl`/`komm`).

**The exact Spec.lean diff, refreshed (D1-D5 as written above, with these changes; STILL NOT APPLIED -- it needs Simon's review and two independent verdicts):**
 * D1 stands as written, with the file split of item 6.
 * D2 stands; the proposed `InvHaelt` match is `InvHaeltD2` in `ArenaSperreInv.lean` (so the D2 text can be copied from a compiled definition). `InvTraeger` for an arena invariant is
   `Dekl.orte`-based (`ok_gleich_wort`), over `Tab ⊕ Glob` if item 7 is decided that way.
 * D3: the field of `Einheit` is `dynZeuge : DynZeuge P` as written; its consumer is `invGutSD2_arena` (proved), which takes the entry fact `hein` -- add the premise of item 8.
   `execEndH = execEnd` on a recognized body is proved (`erkE_execEndH`).
 * D4: the NOT CLAIMED list shrinks as written; add: the commit bound, an arena under a lock-free free list, loops in a writer's machine correspondence (item 2), the ABA ownership predicate.
 * D5: (i) is `invGutSD2_arena` + the existing return leg; (ii) is the leg's hypothesis; (iii) needs item 7. For a SHARED arena the three legs of `Ziel` already say what is needed
   (`arena_ziel`), with `S := K.sperr L` as the lock family of the unit: `sperrOrte` (the checker's `protects` fact) is the only premise, `SperrInvLokal` is a theorem (`sperr_lokal`).
Until items 4, 5, 7 and 8 are settled and item 6 is built the diff would claim more than is proved; it stays a proposal.

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
