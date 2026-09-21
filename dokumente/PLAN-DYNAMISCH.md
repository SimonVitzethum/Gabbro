# Dynamic tables: `max` cap, reservation vs commit, explicit `grow`, reset-only free

*Design for TODO wave D (lanes 240-244). Lane 239, 2026-09-17. Design only: no code,
no codes, no probes. Nothing here is built.*

## 0. What exists, and what is missing

Today an `arena A capacity lo .. hi of T` (`dokumente/SYNTAX.md` §9.1) is a static
object: the emitter writes `buf[hi]` beside `uint32_t used` (`crates/gabbro-check/src/emit.rs`,
`fn arena`), `alloc` bumps `used`, `reset` stores zero. The reservation `lo` emits
nothing; it is the checker's static count (`N212`). The Lean form is sugar over existing
constructors (`grammatik/Grammatik/ArenaZucker.lean`): a table of `count = hi` slots
beside a `used` global; `lo` travels nowhere, on purpose.

The missing piece: `hi` is two things at once — the storage the C touches AND the
ceiling the checker reasons about. A program whose footprint is bounded but not known
at translation time (a firewall connection table, a batch that scales with input)
must today declare `hi` for the worst case and touch all of it: `.bss` of the worst
case, zeroed at load, resident whether used or not. There is no way to say "reserve
address space for M, touch only what this run needs".

This plan decouples the two: a static, checkable ceiling `max M` (address reserved,
never touched implicitly) from a committed prefix (storage actually usable, grown
explicitly). Growth beyond `M` is a refusal, never a runtime surprise.

## 1. Binding constraints (Simon), and where each lands

1. **No OS hard-dependence.** Reservation and commit are RUNTIME (`laufzeit/`, A4-style
   named assumption), addressed by declaration data the program carries. No ABI constant,
   no syscall number, no `MAP_*` in `crates/` or `grammatik/` — not even in tests.
   Lands in §6 (emitter/runtime split) and lane 242 inputs (§10).
2. **Static, checkable ceiling.** `max M` with `M` a compile-time count; growth beyond
   it is a refusal. Cost proofs see every growth point — an invisible commit is a design
   bug. Lands in §2 (clause syntax), §4 (checker obligations), §7 (costs).
3. **Efficiency budget.** At most proved plumbing over the static-arena lowering:
   steady-state fast path at most **X = 10%** more emitted operations than today's
   checked `alloc` (§8 fixes X and the measurement), zero bytes of ghost or header
   material at runtime. Per-object headers are out. Lands in §8 and lane 242/243 inputs.

Scope reading of constraint 2 (explicit, for the reviewer): the `max M` clause of wave D
goes on the **arena declaration** (the monotone form of `PLAN-ERWEITUNG.md` §3 — the only
form with `alloc`/`reset`/`N210`-`N214` machinery). Tables keep their static `count`
(the pool form with per-element release already exists there); a `max` clause on tables
is reserved future syntax, not parsed, not refused, not built in wave D. The substance of
the constraint — compile-time ceiling, refusal beyond, visible growth — is honored in
full for arenas; §2 names the clause so the table form can share it later without rename.

## 2. Clause syntax (lane 240 builds exactly this)

```
arena Log capacity 2 .. 8 max 64 of u32;

impl fn nutzen() -> u32 effects { writes Log } costs <= 24 ops {
    let c = alloc Log (x) else { return 0; };
    grow Log by 8 else { return 0; };
    ...
    reset Log;
}
```

- `max M`: optional third bound. `M` is a translation-time constant (`N210` family:
  same constness rule as `lo`/`hi`). With `max` present: `0 <= lo <= hi <= M`, `M >= 1`,
  `M <= u32::MAX` (the `used`/`committed` counters stay namable). Without `max`:
  today's meaning, byte for byte (`M = hi`, no new checks, no new C).
- `hi` keeps its meaning (initially committed count = emitted initial storage shape)
  and gains a second reading: the commit floor. `lo` keeps its meaning (reservation:
  no `else` owed within). `M` is the ceiling: address reserved, storage not touched.
- `grow A by n else B;`: explicit commit request. `n` is a translation-time constant
  expression (`n >= 1`; non-constant or `n < 1` is a refusal in lane 241's rule set).
  The `else` runs when the runtime cannot commit (below `M` — the only runtime failure
  left; beyond `M` never reaches the C, see §4). The `else` does not fall through,
  exactly like the `alloc` `else` (`SYNTAX.md` §9.1).
- No per-element free, no `release`, no shrink: commit is monotone within a run (§5).

## 3. Reservation vs commit: where each lives

| | reservation (virtual) | commit (usable storage) |
|---|---|---|
| what | address range for `M` slots named, nothing touched | prefix of `c` slots, `hi <= c <= M`, readable/written |
| who | runtime at load (`laufzeit/`, §6) | runtime on `grow` (§6), counted by checker (§4) |
| program-carried data | descriptor with base, `M` (const), `used`, `committed` (§6) | `committed` word, bumped only by `grow` |
| checker fact | `M` from the declaration (const, like `hi`) | per-path pair `(count, committed)` (§4) |
| Lean sketch | `Fin M` virtual region (§9) | committed prefix `c <= M`, monotone |
| failure | load refuses (assumption text §9) | `else` branch (runtime) or refusal (checker, §4) |

The `lo` reservation travels nowhere — unchanged from today (`ArenaZucker.lean` §4:
`arenaAlloc_unter_schranke`). The ceiling `M` travels as a constant into the checker
(constness check), into the emitter (descriptor + `_Static_assert` pins, §6), and into
the Lean sketch (region index, §9). The committed count travels as checker state per
path (like the `N212` count) and as one runtime word (like `used`).

Monotone commit: within one run, `committed` never decreases. `reset A;` sets `used`
to zero and leaves `committed` unchanged (one store, as today — no runtime call, cost
1 op, unchanged). There is deliberately no decommit statement: a shrinking primitive
would need its own checker domain (which paths may assume what is committed) and its
own Lean model (prefix property lost), for a memory-pressure payoff no corpus program
measures. If a deployment needs its pages back, it restarts the generation's owner —
that is an architecture answer, not a statement.

## 4. Checker obligations (lane 241 builds exactly this)

> **Correction, fix lane F2 (review G08 F1, 2026-09-21).** The paragraph below holds the
> ceiling against a single `min`-joined committed value. That is the LOWER bound — right for
> "what is usable" (R-commit), wrong for "can this commit pass `M`", which needs the MOST any
> run can have committed. Since fix lane F2 the checker carries both: the lower bound as
> written below, and an UPPER bound per arena that joins with `max`, is left alone by
> `reset` (the runtime never decommits, §3), saturates after a loop whose body may commit
> without a constant pass bound (`forever`, `traverse`, a non-constant `retry`), multiplies
> by the pass bound of a `retry … bounded N`, and crosses function boundaries: every
> routine gets a per-invocation bound (its own `grow`s plus its callees' and started roots',
> `UNENDLICH` in a recursion or through a call through a place), the whole-program total is
> the sum over the ROOTS of the call graph (routines no other routine calls or starts, plus
> every cycle member), each entered once per load (a `concurrent` body once per naming, an
> `entry … dispatch` target without bound), and each body starts at the floor plus
> the total minus its own share. `N426` refuses every `grow` whose upper bound plus amount
> may pass `M`. The `else` of `grow` walks from the state BEFORE the request (nothing
> committed), as written below; until fix lane F2 the checker walked it from the bumped
> state. The run model (roots entered once per load) is the goal theorem's (declared starts;
> separately linked units NOT CLAIMED): a routine entered again by a caller the unit does not
> see can still reach the runtime's past-ceiling stop.

Per function body, per path, the pass tracks `(count, committed)` per arena, starting
at `(0, hi)`; `reset` sets `(0, hi)` (commit floor restored by construction, since
commit never shrinks); `grow A by n` sets `(count, min(committed + n, M))` on the main
path and leaves `(count, committed)` in the `else` branch (commit failed, nothing
gained). Joins take `max` of counts (as today) and `min` of committed (sound
direction: what both paths guarantee). Loops: counts saturate as today (`UNENDLICH`
in `arena.rs`); committed needs no saturation — it is capped by `M` by construction.

Rules (codes: REQUEST from the orchestrator, next free block after the §-1 assignments;
do not self-assign — see §10):

- **R-max (refusal): `alloc` whose static count may reach `M`.** Since
  `committed <= M` is invariant, this is subsumed in practice by R-commit below, but it
  is stated separately because it is the constraint-2 rule: no path may name a slot at
  or beyond `M`. Sentence pattern follows `N212` ("past X … the … is owed/refused").
  Poison probe: arena with `max 4`, four allocs since reset, fifth `alloc` — refused
  even with an `else` beside it (beyond the ceiling there is no branch to take).
- **R-commit (refusal): `alloc` whose static count may exceed the path's `committed`
  without a dominating `grow`.** This is the `N212` shape with the path's committed
  value in place of `hi`: the program touches storage nobody committed. Positive probe:
  `hi = 8`, `grow by 8`, then allocs 9..16 with `else` past `lo` — clean.
  Poison probe: alloc of slot 9 with committed 8 and no `grow` — refused.
- **R-grow-else (refusal): `grow` without `else`.** The runtime commit below `M` can
  fail (out of memory is real even under a reservation); the failure path is written
  down, not hoped away — same rationale as `N212`'s sentence. No exceptions for `n`
  small: smallness is not a proof. **What the `else` does and does not catch** (review
  G08 F3, fix lane F2): it runs when the platform REFUSES the commit. On hosted Linux the
  commit (`laufzeit/arena_dyn.c`) only changes page protection and is lazy since fix
  lane F2 (no scrub, no touch); under the default overcommit heuristic that practically
  never fails, and out of memory surfaces later, at first touch, as the OOM killer — not
  as the `else`. Only strict accounting (`vm.overcommit_memory = 2`) makes the refusal,
  and so the `else`, reachable. The branch is the program's answer to a refused commit,
  not a promise that every out-of-memory reaches the program; no test exercises it.
- **R-grow-const (refusal): non-constant or `< 1` grow amount.** The committed count is
  checker state; an uncountable step makes it uncountable. Same constness reader as
  `N210` (share it, do not re-implement it).
- **R-grow-form (refusal): `grow` naming no declared arena.** Same as `N213`.
- Unchanged: `N210` (plus the `hi <= M`, `M` range faces — extend the rule, do not add
  a code), `N211` (generations; `grow` does not touch generations), `N212` (reservation
  logic, now against the path's committed value where it exceeds `hi`), `N213`, `N214`.

Cross-function counting of the ALLOCATION count stays per function, like `costs` and
like today's arena count: a reservation shared across functions needs whole-program
discipline (future work, not a silent promise — `arena.rs` module head already says
this). The COMMIT ceiling is whole-program since fix lane F2 (the correction above).

## 5. DECISION 1 — growth trigger: explicit `grow` with costs (picked)

The trigger is the `grow A by n else B;` statement of §2: every commit is a program
step the checker counts, the cost pass prices, and the Lean sketch models.

Why, with measurement reasoning:

- **Cost visibility (constraint 2 is decisive).** An invisible commit is a design bug
  by Simon's fiat, and a page fault is the most invisible commit there is: no statement,
  no cost, no checker fact at the growth point. Explicit `grow` is a statement: it
  costs (1 op + the runtime's declared commit costs through the existing `K003`
  callee-costs machinery, §7), it feeds `K002` inside `locks` blocks (§7), and a
  missing one is a refusal (R-commit). The growth points of a program are then
  enumerable by grep — a reviewer checks them the way they check `held` today.
- **Latency concentration.** A fault puts handler latency (microseconds, TLB + handler
  + first-touch zeroing) on an arbitrary store at an arbitrary program point: every
  store's timing becomes assumption-dependent, and the §4 waiting-bound/WCET story
  ("waiting bounds that fit a data sheet") would need a per-access fault term. `grow`
  concentrates commit at named points with declared costs — the WCET certificate
  carries them like any call (§7). Programs that need smooth latency grow before the
  batch (amortized, one `grow` per N allocs); programs that do not, grow inline.
- **Fast path is equal, so latency/visibility decide.** Today's checked `alloc` emits
  `if (used < hi)`; the dynamic form emits `if (used < committed)` — one load of a
  runtime word instead of an immediate, same branch shape (§8 measures exactly this).
  Fault-driven also has a zero-instruction fast path, so there is no fast-path argument
  for faults; the decision rests on who pays the slow path and where it is named.
- **Smaller, OS-agnostic runtime (constraint 1).** Explicit commit needs two runtime
  functions (reserve at load, commit on `grow`) behind a two-function interface with
  OS code strictly inside `laufzeit/*.c`. Fault-driven needs a fault/exception path:
  a signal handler on hosted POSIX, vector-table entries on bare metal — the most
  OS-specific code in the system, threaded through every deployment, with its own
  reentrancy and latency proof load. Keeping that out of the trusted base is worth
  more than saving the `grow` statements.

REJECTED ALTERNATIVE — fault-driven commit with a latency assumption: first touch
within the reservation traps to the runtime, which commits and resumes; programs carry
no `grow`; the ONE list gains a fault-latency entry ("every fault in the reservation
resolves within F"). Revisit only if measured: a deployment where `grow` placement
costs (code size + planner effort) exceed the fault-handler TCB savings, counted in
reviewed lines of `laufzeit/` and in WCET certificate entries. That measurement does
not exist today; until it does, the fault path is not built, not prototyped, not
kept warm.

## 6. DECISION 2 — free discipline: arena-reset proof (picked)

Freeing is `reset A;` only — unchanged semantics (counter to zero, generation consumed,
`N211` refuses stale indices), unchanged cost (1 op), plus the monotone-commit fact of
§3 (commit survives reset). There is no per-slot free, no free list, no `release`.

Why:

- **The machinery exists and is proved.** Generations are a type index in Lean
  (`Arena k g`, `ArenaIdx g n` — a stale index does not typecheck) and a counter in the
  checker (`N211`, five probes' worth of refusal sentences). Reset-only freeing reuses
  both with zero new domains. In the Lean sugar use-after-free falls out grammatically,
  exactly as `PLAN-ERWEITUNG.md` §3 designed it ("a node is an `index into arena`; an
  index into a reset arena is not expressible"). **In the surface language it is a
  checker refusal, not grammar** (review G08 F2, corrected by fix lane F2 on
  2026-09-21): indices travel in parameters, globals, fields, slots and call results,
  and `N211` holds them as follows — a `reset` in the same body, or in any routine
  called or `start`ed since (transitively; a call through a place counts as resetting
  every arena the program resets), consumes the generation of every index held across
  it; a parameter typed `index into A` is live until the first such `reset`, and a stale
  index handed to one is refused at the call; an index that reaches a use through a
  global, a field, a slot, a call result or an untracked local is refused wherever the
  program resets that arena at all. **Not covered:** a `reset` in a routine running
  CONCURRENTLY with the index holder (another root of a `concurrent` set, a `child`
  path) — generations are tracked along one thread of control. Memory safety does not
  depend on it (a stale index stays below `committed`); the residue is a logical
  dangling reference.
- **A free list needs a per-slot liveness domain.** Returning slot `i` to a list and
  reissuing it later requires the checker to know, per slot, whether it is live — an
  abstract domain over up to `M` slots (bitset or interval set per path, joined at
  branches, saturated at loops), plus a reuse-order argument, plus an ABA-shaped
  reasoning about a slot's successive lifetimes. That is a new checker pass of the size
  of `arena.rs` itself, a new Lean index family, and per-object ghost liveness that must
  then be proved zero-size at runtime (constraint 3) — all to re-issue slots the next
  `reset` reclaims for one store.
- **No duplication of the pool form.** Per-element release already exists where it
  belongs: `table T count N` with generated `insert`/`remove` (`PLAN-ERWEITUNG.md` §3,
  second row). A free list on arenas would give the monotone form a second, worse pool.
  Programs with per-object lifetimes use tables; programs with phase lifetimes use
  dynamic arenas; the two forms stay two forms.

REJECTED ALTERNATIVE — linear free-list: `free A[i]` consumes the index (linear, like
a mark) and links the slot into a free list; `alloc` reuses the head or commits a new
slot; a use-after-free is a linearity refusal. Revisit only if measured: a corpus
program (not a sketch) whose peak-live set fits `M` but whose total allocations do not
fit any reset placement — i.e. interleaved lifetimes that no phase boundary separates.
No such program is in the corpus today (`beispiele/98`, `99` are single-phase); until
one is, the list is not built.

## 7. Emitter / runtime interface (lane 242 builds exactly this)

Emitted shape per dynamic arena (names provisional; lane 242 fixes them and pins them
in the C-form census the way `A_arena_speicher` is pinned today):

```c
/* Declaration data the program carries (emitter-owned, OS-free). */
static uint32_t Log_used;        /* as today */
static uint32_t Log_committed;   /* committed prefix; init: hi */
static uint8_t *Log_base;        /* reserved region base, set at load */
/* M and hi are compile-time constants at every use site; additionally: */
_Static_assert(8 <= 64, "commit floor within ceiling");
_Static_assert(64 <= UINT32_MAX, "ceiling namable");
```

- The descriptor (`base`, `used`, `committed`, const `M`/`hi`) is what §3 means by
  "declaration data the program carries": the runtime never names an arena any other
  way. The emitter passes a pointer to the descriptor (or its link-time name) — never
  sizes, never addresses, never flags.
- Runtime interface (exact signatures fixed by lane 242; the SHAPE is fixed here —
  two functions, both in `laufzeit/`, both OS-free at the interface):
  `void gabbro_arena_reserve(descriptor *)` at load (establishes the virtual range for
  `M`; failure refuses the load — assumption text §9 and
  `bool gabbro_arena_grow(descriptor *, uint32_t n)` on `grow` (commits `n` more slots
  below `M`, bumps `committed`, returns success; `false` runs the `else`).
- All OS specifics (`mmap`/`MAP_*`, `VirtualAlloc`, page-table/MPU setup, first-touch
  policy) live strictly inside `laufzeit/reserve.c` and `laufzeit/grow.c` (new files,
  hosted-POSIX first like `laufzeit/start.c`, bare-metal second). A mechanical guardian
  (lane 242 adds it beside `pruefe-emission.sh`, same pattern as the A4 precedent):
  `MAP_|mmap|munmap|mprotect|sbrk|VirtualAlloc` outside `laufzeit/` fails the build —
  including tests and comments (a constant smuggled as documentation is still smuggled).
- `alloc` lowering: today's checked form with `committed` in place of the `hi`
  immediate (§8). `grow` lowering: `if (gabbro_arena_grow(&desc, n)) { } else { <else> }`
  in the same brace shape as the checked `alloc`. `reset` lowering: unchanged
  (`used = 0`), plus a comment-level pointer to this plan for why `committed` does not
  move. Bare `alloc` without `else` (the `OFFEN.md` O14 shape (1)): unchanged policy —
  closing it needs a decision about the emitted C, and that decision is still open;
  dynamic arenas inherit it, they do not fix it.
- Ghost material: the Lean-only fields of §9 (`committed` proofs, generation indices)
  are erased at emission — the emitter reads the descriptor, never the proofs. Zero
  bytes is checked by construction (no new emitted word except `committed` + `base`,
  both functional) and re-measured in §8.

## 8. Costs and the efficiency budget (lane 243 builds exactly this)

- `grow A by n else B` costs `1 + <declared commit costs of the runtime grow for n> +
  <else-branch costs>`, counted exactly like `StmtArt::Alloc` today (`kosten.rs`: store
  is one primitive plus the value plus the `else` as any `else`). The commit work is
  priced through the callee-costs machinery (`K003`: a call counts the callee's declared
  `costs`): the runtime grow carries a declared cost bound per slot committed, and the
  checker multiplies by the constant `n`. No new cost theory — one new arm reusing two
  existing readers.
- `K002` sees every `grow`: a `grow` inside a `locks` block counts against the lock's
  `held` promise like any other statement cost. This is the constraint-2 payoff stated
  as a rule: growth inside a critical section is priced where the latency promise lives.
  Poison probe (lane 243): a `grow` that overflows `held` falls at `K002` with the lock
  named — the growth point is visible exactly where it costs.
- **X = 10%.** Steady-state `alloc`/`read`/`reset` lowerings carry at most 10% more
  emitted operations than today's static-arena lowerings, counted as: dynamic checked
  `alloc` = today's checked `alloc` with one immediate replaced by one word load
  (same branch shape) — expected measured delta is one load, i.e. ~1 op on a ~10-op
  sequence, hence 10% with headroom. Ghost/runtime-bookkeeping material at runtime is
  exactly two words per arena (`base`, `committed`); proof material is zero bytes (§6).
  Method (lane 243 measures, lane 242 provides the C): op tally via `gabbro kosten`
  plus emitted-C instruction tally on the arena corpus (`beispiele/98`, `99`, and the
  new dynamic examples of §10) before/after. Note: `messung/SPEICHER-CENSUS.md` (lane
  238) was not in the tree when this was written; the 10% is fixed against the
  static-arena lowerings above, and lanes 242/243 reconcile against the census if it
  lands first — reconciliation is a report row, not a redesign (the budget direction
  is: dynamic costs no more than static + one load per checked access).

## 9. Lean model sketch (lane 244 builds exactly this)

New file `grammatik/Grammatik/ArenaDyn.lean` (name fixed; contents sketched, lane 244
proves). It extends `ArenaZucker.lean`, it does not modify it:

- `DynForm`: an `ArenaForm D` (table `count = M` — note: the Lean table spans the
  CEILING, the virtual region) plus `hi : Nat` (commit floor, `D.count`-style bound
  `hi <= M`) plus the committed prefix as a runtime word read through `stand`-style
  accessors. The virtual region is `Fin M`; the committed subset is the prefix
  `Fin c` with `c <= M`; the prefix property (no fragmentation, no holes) holds by
  construction — commit only extends the prefix (§3 monotone).
- Theorems (mirror shapes of `ArenaZucker.lean` §4, lane 244 states and proves):
  `dynGrow_commit` (grow bumps the committed word by `n`, capped `M`, memory
  otherwise untouched — the frame lemma `exec_rahmen` carries it, like any store);
  `dynAlloc_unter_commit` (below the committed count, `alloc` runs its body — same
  statement shape as `arenaAlloc_unter_schranke` with `committed` for `count`);
  `dynAlloc_ueber_commit` (at/above committed, `alloc` takes its `else` — the
  R-commit rule's model half); `dynCommit_monoton` (no step decreases committed).
- Refinement shape (statement fixed here, proof is lane 244's): every dynamic run
  whose allocs stay under their path's committed count simulates the static-max
  program (the same sugar with `hi := M`) step for step — growth is then an
  observable no-op, and every static-arena theorem (`arenaAlloc_unter_schranke`,
  the `Arena.lean` arithmetic) transfers. The witness is the reference fixture
  (`ReferenzB.lean`) extended with one dynamic arena — lane 244's `_zeuge` theorems
  build on `refD`-style concrete values, non-degenerate (a table some function
  writes, a reached run with a memory-changing step), per the inhabitation rule.
- Assumption texts for the ONE list (`Spec.lean` header style, English, lane 244
  inserts — exact wording fixed here so the header diff is reviewable without
  asking):
  - (d) `Laufzeit.reserve` — "the loader reserves the virtual range for every
    dynamic arena's `M` before any start runs; a failed reservation refuses the
    load, it never starts a program with a smaller range." Falsifier probe: a
    `max`-carrying unit started under a reservation smaller than `M` must not
    reach any start (lane 242's executed probe covers the hosted half).
  - (d) `Laufzeit.commit` — "every `grow` the checker admits either commits its
    slots before the next statement runs or takes the `else` branch; a commit
    that reports success names readable/writable storage; commit latency is
    bounded by the runtime's declared per-slot cost (the `K003` number §7
    counts)." This is the commit-service entry — the explicit-grow counterpart
    of a fault-latency entry, and the only timing assumption wave D adds.
  - Recorded but NOT inserted (rejected alternative §5): fault-latency text —
    "every first touch within the reservation resolves within F (fault handler
    + TLB + zeroing)". Kept in this plan so a future revisit does not re-derive
    the wording; it goes nowhere while `grow` is the trigger.

## 10. Builder lanes 240–244: exact inputs

Common to all five: read this plan, `dokumente/SYNTAX.md` §9.1, `dokumente/OFFEN.md`
O14, `crates/gabbro-check/src/arena.rs` (module head + `N210`–`N214`), `grammatik/Grammatik/ArenaZucker.lean`
(header + §4), `crates/gabbro-check/src/emit.rs` `fn arena` + the `Alloc`/`ResetArena`
lowering arms, and `crates/gabbro-check/src/kosten.rs` (the `Alloc`/`ResetArena` arms).
Do not touch MARKE_EMIT. English only. Report as `MUSE-REPORT-NN.md`. Number
discipline: diagnostic codes, gift numbers and example numbers are REQUESTED from the
orchestrator before first use (next free blocks past the §-1 assignments); provisional
mnemonics in code (`DYN-…`) until assigned — a self-assigned code that collides fails
review. No ABI constant, no syscall number, no `MAP_*` in `crates/` or `grammatik/`,
not even in tests (§1.1).

| lane | exclusive scope | reads first | deliverable | needs from |
|---|---|---|---|---|
| 240 | clause syntax + parser + `SYNTAX.md` §9.1 delta | `SYNTAX.md` §§9.1/12, `pruefe-wortschatz.py` + grammar-table guardian (patterns bilingual BEFORE the document moves), `lex.rs`/`parse.rs`/`ast.rs` arena arms | `arena … max M` + `grow … else` parsed into `StmtArt`-level AST; EBNF + vocabulary guardians green; poison probes: non-constant `M`, `hi > M`, `M = 0`, `grow` with `n < 1`; examples: dynamic 98/99 twins (one `max`-carrying, one static-unchanged) | — |
| 241 | checker obligations R-max/R-commit/R-grow-else/R-grow-const/R-grow-form (§4) | `arena.rs` full, `saetze.rs` sentence pattern of `N212`, `umgebung.rs` arena sigs | `(count, committed)` flow + the five rules with sentences in `saetze.rs` in the same commit; poison probe per rule + one positive probe (grow-covered allocs clean); corpus diff measured, zero unintended diffs | 240 (AST shape) |
| 242 | emitter + runtime interface (§6) | `emit.rs` arena arms, `laufzeit/start.c` (A4 precedent), `pruefe-emission.sh` counters | descriptor + `grow`/`alloc`/`reset` lowerings; `laufzeit/reserve.c` + `laufzeit/grow.c` (hosted first); OS-token guardian (fails on `MAP_\|mmap\|mprotect\|sbrk\|VirtualAlloc` outside `laufzeit/`); one executed probe (grow, fill past old `hi`, read back); §8 fast-path tally input for 243 | 240 (AST), 241 (rule names for refusal arms) |
| 243 | costs + budget proof (§§7–8) | `kosten.rs` full (`Alloc` arm, `sperrbloecke`/K002, callee-costs/K003), `gabbro kosten` output on 98/99 | `grow` cost arm (1 op + declared per-slot commit × const `n` + else); `K002`-falls probe for `grow` inside `locks`; §8 measurement table (static vs dynamic op tally, ghost-bytes row = 2 words + 0 proof bytes); reconcile-or-report row against `messung/SPEICHER-CENSUS.md` if present | 242 (lowered C to tally) |
| 244 | Lean sketch + assumption texts (§9) | `ArenaZucker.lean` full, `Arena.lean` (`alloc_innerhalb_reserve`, `keine_fragmentierung`), `Zielsatz/Spec.lean` ONE-list header, `ReferenzB.lean` fixture | `grammatik/Grammatik/ArenaDyn.lean` with `DynForm`, the four theorems, the refinement statement + proofs; `_zeuge` companions on the reference fixture (non-degenerate, per the inhabitation rule); the two (d) assumption texts inserted in the `Spec.lean` header as a reviewed diff; `#print axioms` standard, `./lean-bau` green | 241 (rule names the lemmas mirror) |

Order: 240 first; 241 after 240; 242 after 240 (+241 rule names); 243 after 242;
244 after 241. 240 and the 244 proof sketch can start in parallel (244 works against
§9 statements, which are fixed here). No lane changes an existing file's theorems or
refusals except by extension (new arms, new rules); `N210`–`N214`, `K001`–`K007` and
the `A_arena_speicher` shape stay green throughout — a lane that breaks them owns the
repair, never the deletion.

*Rejected-shape log (so no builder relitigates): fault-driven commit (§5), linear
free-list (§6), per-element `max` on tables in wave D (§1 scope reading), decommit/
`release` statement (§3), `max`-dependent fast-path branch beyond one word load
(§8 — anything fancier pays for itself in a measured corpus program first).*

