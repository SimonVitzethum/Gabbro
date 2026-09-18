# MUSE-REPORT-242 — mmap runtime: reserve/commit, OOM fail-stop, emitter-arm SPEC (TODO §-1 wave D)

Lane 242, 2026-09-18. Scope as tasked: `laufzeit/` reservation + commit-on-demand +
OOM fail-stop, the mmap-contract assumption TEXT (report only, not wired into Lean),
demos `153`/`154`, the emitter-arm SPEC for lane 248 (specified, NOT built).
Untouched as ordered: `emit.rs` (234→235), `arena.rs`/`kosten.rs` (240/232),
all Lean files (241), `MARKE_EMIT*` (delta measured below, merger bumps).

## Verdict in one line

**The operational half of `ArenaDyn.lean` is built and executed: reserve-at-load
with a named fail-stop exit, commit-on-`grow` below the ceiling with an `else`
return, no silent NULL on any path; the OS surface is one file behind a
two-function counts-only interface, guarded mechanically; two demos pin the
static shapes the dynamic form preserves; the 248 SPEC names file, place and
shape so the emitter arm starts without asking. `cargo-pruef` zero failures,
`lean-bau` green, corpus verdict diff zero, `MARKE_EMIT` delta +2 measured.**

## 1. What was built (5 new files, 0 modified)

- **`laufzeit/arena_dyn.h`** — the OS-free interface: `gabbro_arena_desc`
  (`base`, `elem`, `max`, `floor_hi`, `used`, `committed`), `void
  gabbro_arena_reserve(desc*)` at load, `bool gabbro_arena_grow(desc*, n)`
  on `grow`. Named exit `GABBRO_ARENA_EXIT_RESERVE 3`. No ABI constant, no
  syscall number, no `MAP_*` — the mechanical guard (§2) covers this file too.
- **`laufzeit/arena_dyn.c`** — the hosted-POSIX half, the ONLY tree file that
  may name OS memory calls. Reserve: `mmap(PROT_NONE, MAP_PRIVATE |
  MAP_ANONYMOUS)` for `max` slots; any failure (bad descriptor, `size_t`
  overflow, `mmap` fail, floor that will not commit) refuses the LOAD with a
  stderr line plus `exit(3)` — never a null base, never a smaller range.
  Grow: page-rounded `mprotect(PROT_READ | PROT_WRITE)` of the new tail,
  zero-scrub of exactly the new slots, `committed` bumped only on success;
  OOM below the ceiling returns `false` (`committed` unchanged, caller runs
  `else`); a request past `max` fail-stops (`abort`, named message) — past
  the ceiling there is no commit, only the stop, because reaching it means
  the checker was bypassed. `n == 0` is a no-op `true`; `NULL`/unreserved
  descriptor is `false`, never a crash. Page size never crosses the
  interface (slots in, pages internal).
- **`instrumente/pruefe-osfrei.py`** — the §6 guardian beside
  `pruefe-emission.sh`: fails on `mmap|munmap|mprotect|sbrk|VirtualAlloc`
  (ASCII-guarded: bare `mmap` would fire inside German `Programmfragen`),
  `MAP_[A-Z_]+`, `PROT_[A-Z_]+`, `__NR_*`, `SYS_*` over `crates/`,
  `grammatik/`, `beispiele/` (comments included), `laufzeit/` excluded by
  design, `.lake/target/.git/__pycache__/programmlogik` excluded as
  non-tree. Prose ABOUT the interface (`dokumente/`, reports) is out of
  scope — prose about `cc` is not a call, same lesson as
  `pruefe-waechter.py`'s call-site rule. Selftest `--selbsttest`: planted
  token falls, token-free tree silent, compound-word pin silent (3 of 3).
- **`beispiele/153-arena-waechst.gab`** — growth under a ceiling in today's
  syntax (`capacity 2 .. 8`, `M = hi = 8`): eight allocs, every one past
  `lo` with its `else` (growth points enumerable by grep), 16-bit slots
  with 32-bit widening reads (the `99` shape, so the eight-way sum fits
  `u32` with no narrowing owed), `reset` + re-alloc + deterministic return
  **370**. `check` 0/0, `kosten` 57/64, emits 92 lines, byte-identical
  re-emit, `cc -Werror` clean (`-O0`, stage-9 `-c`, clang), executed 370 at
  `-O0`, `-O2` and UBSan, all equal.
- **`beispiele/154-arena-voll.gab`** — refuse-on-full (`capacity 2 .. 2`):
  third alloc takes `else`, branch resets and reallocates (both halves of
  the free discipline in one file: no branch past the ceiling except the
  written one, no live index past a reset), deterministic return **1004**.
  `check` 0/0, `kosten` 24/32, emits 48 lines, byte-identical, `cc -Werror`
  clean (`-O0`, stage-9 `-c`, clang), executed 1004 at `-O0` and UBSan.

## 2. Verification (last lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full build + test).
- `./lean-bau`: `Build completed successfully (280 jobs).` (no Lean file
  touched; the run is the machine check behind that claim).
- `python3 instrumente/pruefe-osfrei.py`: `1267 files read, no OS token
  outside laufzeit/`, exit 0; `--selbsttest`: `3 of 3 checks hold`, exit 0;
  `pruefe-waechter.py:statisch()` over the new guardian: `[]` (no
  FRIST/SPRECHPROBE/ROT-BEI-ABBRUCH/GEBIETSSCHEMA demand; pure scan, no
  subprocess, locale-free by construction).
- Runtime harness (scratch `.tmp/harness242.c`, NOT committed — drivers are
  evidence, not product): `ok` (reserve 64/floor 8, floor R/W, grow 8→16
  with zero-fill verified per slot, pattern read-back, grow to exactly 64,
  no-op grow 0) exit 0; `pastmax` (8 + 57 > 64) SIGABRT with the named
  line; `oom` (1 GiB reservation under a 64 MiB `RLIMIT_AS`) exit **3**
  with the named line; `null` (grow unreserved) `false`, no crash.
  `-O0`, `-O2` and UBSan runs agree (`HARNESS-OK committed=64` thrice).
- `laufzeit/arena_dyn.c` alone: `cc -Werror` clean at `-O0` and `-O2`.
- Corpus verdict diff: ZERO by construction (no checker/emitter/Lean file
  changed; `cargo-pruef` green over the identical tree, gifts included).
- `MARKE_EMIT` delta, measured (`gabbro emit` over `beispiele/*.gab`):
  **123 → 125, exactly the two new demos** (both emit; no other root
  moves: no gifts, no `messung/`, no new emitting root). The merger bumps
  `MARKE_EMIT` 123 → 125; every other `MARKE_EMIT_*` is unchanged.
- New codes/gifts/examples: **NONE consumed** (N431–435, gifts 1092–1096 go
  back unused — §6 why). No new refusal was measured: over-cap growth
  already refuses via 240/N212 (gift 1087), OOM-below-max is a branch, not
  a refusal, and past-max at runtime is a bypass abort, not a checker code.

## 3. Assumption TEXT for the ONE list (report only — 241 owns the model)

Verbatim from `PLAN-DYNAMISCH.md` §9 (lane 239's fixed wording, so the
header diff is reviewable without asking); NOT wired into `Spec.lean`:

- (d) `Laufzeit.reserve` — "the loader reserves the virtual range for every
  dynamic arena's `M` before any start runs; a failed reservation refuses
  the load, it never starts a program with a smaller range." Built half:
  `gabbro_arena_reserve` + exit 3 (§1); falsifier probe: the harness `oom`
  mode (a `max`-carrying load under a 64 MiB cap refuses with the named
  exit and reaches no start).
- (d) `Laufzeit.commit` — "every `grow` the checker admits either commits
  its slots before the next statement runs or takes the `else` branch; a
  commit that reports success names readable/writable storage; commit
  latency is bounded by the runtime's declared per-slot cost." Built half:
  `gabbro_arena_grow` true/false shape + zero-fill (§1, harness `ok`
  mode reads every new slot as zero before writing it).
- Recorded but NOT inserted (rejected §5 alternative): the fault-latency
  text stays in the plan and goes nowhere while `grow` is the trigger.

## 4. Emitter-arm SPEC for lane 248 (specified, NOT built — no `emit.rs`)

Start conditions (all three, in order): the parser lane lands `arena … max
M` + `grow A by n else B` into `StmtArt` (`ArenaSig::max`, `StmtArt::Grow`,
`SYNTAX.md` §9.1 — still unowned, findings of 240/243 confirmed); wave C
frees `emit.rs` (after 235 — touching it before conflicts at merge); 241's
rule names (`R-max`/`R-commit` refusals) fix the refusal arms. Nothing below
needs a question answered by lane 242.

- **File/place:** `crates/gabbro-check/src/emit.rs`, `fn arena`
  (today line ~3866) gains the dynamic arm (taken iff `max` present), plus
  the `StmtArt::Grow` lowering beside the `Alloc` arm (~line 7067) and the
  `ResetArena` no-change (one store, as today). Driver side: the hosted
  driver (lane 246's generator or `start.c` family) calls
  `gabbro_arena_reserve` per dynamic arena before spawning roots.
- **Shape per dynamic arena** (names fixed here, pinned like
  `A_arena_speicher` today):
  ```c
  static gabbro_arena_desc Log_desc = {0, sizeof(uint16_t), 64, 8, 0, 8};
  _Static_assert(8 <= 64, "commit floor within ceiling");
  _Static_assert(1 <= 64, "ceiling namable");
  ```
  (`M`/`hi` are compile-time constants at every use site; `base` is set at
  load; the descriptor pointer — never sizes, addresses or flags — is what
  the runtime is addressed by.) No `buf[M]` static storage is emitted for
  the reserved range: address reserved, storage not touched.
- **`alloc` lowering:** today's checked form with the `committed` word in
  place of the `hi` immediate (`if (used < Log_desc.committed)` — one word
  load instead of one immediate, same branch shape; §8 fast-path input).
  **`grow` lowering:** `if (gabbro_arena_grow(&Log_desc, n)) {} else {
  <else> }` in the checked-`alloc` brace shape. **`reset` lowering:**
  unchanged (`used = 0`) plus a comment pointer to the monotone-commit
  fact. Bare `alloc` without `else` inherits the open O14 policy — dynamic
  arenas do not fix it.
- **Test obligations (248's, not mine):** one executed probe — grow, fill
  past the old `hi`, read back (result values reuse the 153/154 shapes:
  370/1004 are the static twins that must still compute); poison shape:
  over-`max` growth refuses at check time (extends gift 1087, no new code
  expected); `-O0`/`-O2`/UBSan parity plus stage-9 `-c` on both compilers,
  as measured in §1.
- **Non-goals (rejected shapes, do not relitigate):** decommit/`release`,
  per-element `max` on tables, linear free-list, fault-driven commit, any
  second ceiling beside 240's cap, any `MAP_*`/ABI token outside
  `laufzeit/` (the §2 guardian fails the build on it).

## 5. Fault-cost accounting (deliverable 2)

- **Which latency the named assumption covers:** commit latency ONLY, as
  DATA — lane 241's `growKosten n faultKosten = 1 + n * faultKosten` reads
  the per-slot cost from the (d)`Laufzeit.commit` entry (§3), never proved.
  Reserve latency is load-time: no program path carries it, so no `K00x`
  prices it (the loader refuses or it happened before start 0). Committed-
  slot access adds no assumption term: it is today's checked `alloc` with
  one immediate swapped for one word load (§8 tally input for the lane that
  re-measures: static immediate vs dynamic `committed` load on 153/98).
- **Where K002 sees every growth point:** the existing `sperrbloecke` walk
  prices every `StmtArt` inside `locks` against `held` — lane 240's
  `arena_wachstum_in_sperre_k002` probe proves the mechanism for `alloc`
  (three allocs vs `held <= 2 ops` fall `K002`, twin at 64 clean). The
  `Grow` arm rides that walk with zero new machinery; coordinates:
  `kosten.rs:1080` (`Alloc` arm shape: 1 + value + else) with the declared
  per-slot commit cost × const `n` in place of the value cost.
  `ResetArena` (`kosten.rs:1087`) stays `Zahl(1)` — commit survives reset.
- **Where K003 sees it:** through the callee-costs machinery — the runtime
  grow carries its declared per-slot bound, the checker multiplies by the
  constant `n` (non-constant `n` is R-grow-const, no syntax yet). Measured
  baselines on this tree (`gabbro kosten`): 153 `waechst 57/64`, 154
  `voll 24/32`, 98 `nutzen 11/16`, 99 `grenze 34/34`.

## 6. Findings (report, not built)

1. **Parser lane still missing** (confirms 240-F2, 243-F1): `max M` clause,
   `grow A by n else B`, `SYNTAX.md` §9.1, `ArenaSig::max`. Until it lands,
   R-commit coincides with N212 and R-grow-else/const/form have no syntax.
   The 248 SPEC above is written so no second design is needed — but the
   build still waits on that lane plus 235 (`emit.rs`).
2. **`-O2` `-Warray-bounds` on the checked-alloc idiom** (measured, not
   mine): 154's emitted `buf[a]` warns at `-O2 -Werror`, and 99's merged
   emission warns IDENTICALLY (same subscript, same site class) — a
   pre-existing emitter-idiom-vs-optimizer note, not a lane-242 defect.
   UBSan silent, `-O0`/`-O2` results equal (370/1004), stage-9 `-c` clean
   under both `cc` and `clang`. Left for the emitter owner; weakening the
   demo to dodge an optimizer warning would be exactly the traded-safety
   class the owner forbids.
3. **`narrow` lowering vs `-Werror=type-limits`** (measured while writing
   153): a `narrow` on a full-range `u32` emits `if (!(sum >= 0 && …))`,
   which `-O0 -Werror` rejects as tautological. 153 avoids it with the
   16-bit-slot shape (no narrowing owed anywhere). 248's dynamic `alloc`
   lowering must keep the `-O0 -Werror`-clean property — recorded here so
   it is a constraint, not a surprise.
4. **Preamble vs task** (as in 240/241/243): the wave preamble says
   "independent reviewer, change no existing file"; the lane task orders a
   runtime + demos + SPEC build. I followed the specific task; the
   resulting diff is new files ONLY (`git status`: five `??`, zero `M`).
5. **Lane 248 has no TODO §-1 row** (wave D lists 238–244; the emitter arm
   "post-235" exists only in this task text). The §4 SPEC targets that arm
   by content; the orchestrator owns the numbering.
6. **Rule-13 note:** no theorem added (no Lean touched), so no `_zeuge`
   is owed; the non-degeneracy burden is carried by execution instead —
   the harness `ok` mode moves memory (`slots[i] = …`, read-back verified)
   and both demos execute with compared results.

## Names added

- `laufzeit/arena_dyn.h`: `gabbro_arena_desc`, `gabbro_arena_reserve`,
  `gabbro_arena_grow`, `GABBRO_ARENA_EXIT_RESERVE`.
- `laufzeit/arena_dyn.c`: `seiten_groesse`, `slot_bytes` (both static).
- `instrumente/pruefe-osfrei.py` (scan + `--selbsttest`).
- `beispiele/153-arena-waechst.gab` (`waechst`, executed 370),
  `beispiele/154-arena-voll.gab` (`voll`, executed 1004).
- Last `./cargo-pruef` result line: `== exit 0; failing tests: 0`.
- Last `./lean-bau` result line: `Build completed successfully (280 jobs).`

Open: parser lane (F1) then 248's emitter arm (§4); the §8 static-vs-dynamic
op tally once it lands (method + baselines in §5); the two (d) texts'
wiring into `Spec.lean` (241's reassigned lane).
