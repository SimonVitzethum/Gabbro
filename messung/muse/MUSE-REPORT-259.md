# MUSE-REPORT-259 — lower `grow` to C (the emitter arm lane 248 could not build)

Lane 259, 2026-09-26. Scope as tasked: the `grow` emitter arm over lane 257's
closed parser gap, `R-commit`/`R-max` wiring, executed runs including the
`else` branch, honest OOM note, O20 entry. Untouched as ordered: `child`,
`start`, strings, `MARKE_EMIT*` (delta measured below, merger bumps),
`lean_g.rs` (still `LG005` — the model builds the static `ArenaForm`),
no Lean file at all.

## Verdict in one line

**BUILT — `grow A by n else { … }` on a `max`-carrying arena lowers to the
runtime's commit call, `alloc`/`index`/`reset` run against the committed
prefix, `R-commit` refuses at `N466`, example 158 executes on both branches
(118 / 1), and every gate is green except the one expected stage-9 FUND
below.** `./cargo-pruef` zero failures, `./lean-bau` green, corpus verdict
diff zero, `MARKE_EMIT` delta +1 measured (158 only).

## 1. What was built (4 commits on `muse/259`)

**Piece A — emitter arm (`emit.rs`, `erzeugernamen.rs`, `zeugnis.rs`).**

- `Namen::arenen_max` (bare name → `max` expr; presence IS the dynamic form).
- Runtime prelude `ARENA_DYN_PRELUDE` once per `max`-carrying unit (descriptor
  layout + the two declarations behind `#ifndef GABBRO_ARENA_DYN_H`, so a
  driver can include `laufzeit/arena_dyn.c` after the emitted file and the
  header's identical layout wins): the unit still compiles alone (`cc -c`).
- `fn arena` dynamic arm iff `max` present: `static gabbro_arena_desc
  Log_desc = {0, sizeof(T), M, hi, 0, hi}` + two `_Static_assert` pins, NO
  `buf[M]` storage. Static arenas byte-identical (same format strings).
- `alloc`: `used < committed` (one word load for one immediate, same branch
  shape) and stores through `((T *)D_desc.base)[used++]`. Branchless `alloc`
  inherits the O14 policy unchanged.
- `reset`: `D_desc.used = 0`, `committed` untouched (one store + the
  monotone-commit comment).
- `grow` on a dynamic arena: `if (gabbro_arena_grow(&D_desc, (uint32_t)(n)))
  {} else { <else> }` in the checked-`alloc` brace shape. `grow` on a STATIC
  arena keeps `C001` by name (no committed prefix to grow).
- Index reads through `((T *)D_desc.base)[i]`; name set, saturation scan,
  C-name pool (`{A}_desc`) and certificate (`EINORDNUNG` rows `grow` +
  `dynamic arena`, both `Direkt`) follow the lowering — `grow` was
  `UNCLASSIFIED` before.

**Piece B — `R-commit` as `N466` (`arena.rs`, `saetze.rs`, tests, gifts).**

- `Laeufer::dynamisch` (clause present AND usable) threads through
  `pass`/`alle_laeufe`/`laufe`; an `alloc` whose static count since the last
  reset may stand at or past the path's committed LOWER bound falls at
  `N466`, with or without the `else` (the `else` runs when the arena is
  full; here the slot was never committed).
- `R-max` takes NO second code: the committed prefix never exceeds `M`, so a
  count that may reach `M` is already past the prefix on every path and falls
  at `N466` first (gift 1172 pins it). A refusal that can never fire beside
  `N466` would be decoration, not coverage. Static arenas keep `M = hi` with
  `N212` against `lo` (`99` stays clean — the lane-184 class).
- Sentence `arena.alloc_unter_commit` (same commit as the code), poison gifts
  `1171` (past-commit with `else`, exactly `N466`) and `1172` (past-`M`,
  exactly `N466`), `paesse.rs::arena_alloc_braucht_commit_n466` (two poisons
  `faellt_genau`, one grow-covered twin `faellt_nicht`).

**Piece C — example 158 + executed runs.**

- `beispiele/158-arena-commit.gab` (`capacity 2 .. 4 max 8`): `grow by 4`,
  eight allocs past the old `hi` with read-back, `reset`, re-alloc. Clean,
  emits (byte-identical re-emit), cost 58/96.
- `pruefe-emission.sh`: `beispiel158` via the hosted runtime (reserve at
  load, `118`), `beispiel158-else` via a refusing stub (every commit refused
  below the ceiling — the strict-overcommit shape — `1`), `beispiel153`
  static twin (`370`). Each with a biting gift-sed (119 / 9 / 371).
- `154` gets NO durchgestochen entry: its static `buf[a]` warns at `-O2
  -Werror` (`-Warray-bounds`, inlined), and `99` warns identically — the
  pre-existing emitter-idiom finding (lane 242 §6.2), not a lane-259 defect.
  It emits and compiles (stage 9); the refusal path it pins is executed by
  `beispiel158-else` on the dynamic form instead.

**Piece D — ledger and census.**

- `OFFEN.md` O20 gains the third row: the emitted counters are plain words —
  concurrent `alloc`/`grow` on one arena races in C (no atomics, no rule
  demanding them); residue logical only (indices stay below `committed`),
  no concurrency safety claimed or built.
- `pruefe-cformen.py`: the dynamic base store joins `stmt:store-array`
  (same uncovered bucket as its static twin, no new claim); the commit call
  gets its own uncovered row `stmt:grow-call` (it sat under the `stmt:if`
  lemma before — a branch lemma covers the jump, not the callee's effect).
  Result: 0 new uncovered, unclassified back to the 1 pre-existing
  (`140-atomic-array`), RED in the same kind as before.

## 2. Verification (last lines, this tree)

- `./cargo-pruef`: `== exit 0; failing tests: 0`, `1327 passed, 0 failed,
  1 ignored` (baseline 1326; +1 `paesse` test).
- `./lean-bau`: `Build completed successfully (285 jobs).` (no Lean file
  touched; the run is the machine check behind that claim).
- `./emission-pruef`, first run (158 untracked): `== exit 0`,
  `ALL PASS -- 40 durchgestochen, 289 von 289 uebersetzen` (both compilers,
  UBSan silent, ASan not available on this machine — 39 NICHT GEFAHREN).
- `./emission-pruef`, second run (everything committed): the expected FUND
  `127 statt 126 emittierende Dateien in beispiele/` — caused ONLY by 158
  (gift/18, messung/143, messungen/2, programmlogik/1, laufzeit/1, sonst/0
  all unchanged; 1171/1172 are checker-refused and never emit). Mark
  untouched for the merger, who bumps 126 → 127 and re-runs to stage 10
  (green on the identical tree in run one).
- Corpus verdict diff: ZERO — `cargo-pruef` green over the tree (every
  `beispiele/*.gab` still clean, every `gift/*.gab` still falls with its
  booked code; the only new verdicts are 158 clean and 1171/1172 `N466`).
- Guardians: `pruefe-saetze.py` rc=0 (443 codes, 185 sentences, 0 invented);
  `pruefe-kennungen.py` ALL PASS; `pruefe-osfrei.py` clean (1358 files);
  `pruefe-englisch.py` red as on base, German comment count 7965 before
  and after (0 added); `pruefe-vergabe.py` red as on base — `N466` is absent
  from its candidate list, the drift (35→37, 93→109) is other lanes' stale
  marks (the same story as lane 257 §5).

## 3. Names added (exact)

- `emit.rs`: `Namen::arenen_max`, `ARENA_DYN_PRELUDE`,
  `braucht_arena_dynamisch`; dynamic arms in `arena`, `Alloc`, `ResetArena`,
  `Grow`, `benutzte_namen`, index read, saturation scan.
- `erzeugernamen.rs`: `{Arena}_desc` pool entry for `max`-carrying arenas.
- `zeugnis.rs`: `EINORDNUNG` rows `grow`, `dynamic arena`.
- `arena.rs`: `Laeufer::dynamisch`, code `N466`.
- `saetze.rs`: `arena.alloc_unter_commit` (`kennungen: &["N466"]`).
- `paesse.rs`: `arena_alloc_braucht_commit_n466`.
- Gifts `1171-arena-alloc-ohne-commit`, `1172-arena-alloc-ueber-decke`
  (`-- erwartet: N466`); example `158-arena-commit` (executed 118 / 1).
- No Lean definitions, no theorems — no rule-13 `_zeuge` owed on the Lean
  side; inhabitation is carried by execution (158 runs both branches on
  non-degenerate programs) and by the poison/positive probe pairs.
- Consumed from the block: code `N466`, gifts `1171`–`1172`, example `158`.
  Returned unused: `N467`–`N470`, gifts `1173`–`1180`.

## 4. What I believe is wrong in the task (two items, one deviation)

1. **The `else`-via-ceiling run as specified is unbuildable — and the design
   says why.** A `grow` the checker sees reaching past `M` is refused at
   `N426` (never reaches the C); a request reaching past `M` at run time is
   the fail-stop (`abort`), never the branch; a commit below `M` fails only
   when the platform refuses it (strict overcommit — not this machine).
   So no checker-clean program takes the `else` through the ceiling on any
   hosted test machine (fix lane F2 §4 already records: no test exercises
   the hosted refusal branch). The deviation: `beispiel158-else` drives the
   SAME source through a refusing stub — it executes the emitted branch
   exactly where the runtime refuses, without claiming the hosted commit can
   refuse here. Turning the past-`max` stop into a branch instead would have
   made the test pass by weakening safety — refused.
2. **`R-max` as a second refusal would be a dead code.** See §1: subsumed by
   `N466` on dynamic arenas, fatal on static ones (`99`). One code, not two.
3. **Deviation disclosed:** no `154` durchgestochen run (§1, pre-existing
   `-O2` finding). `153` runs; both still emit and compile.

## 5. Open (not mine)

- The merger bumps `MARKE_EMIT` 126 → 127 and re-runs `pruefe-emission.sh`
  to stage 10.
- `pruefe-cformen.py` stays RED on the pre-existing `140-atomic-array`
  unclassified line (another lane's); `pruefe-vergabe.py` and
  `pruefe-englisch.py` stay red on their stale marks/counts.
- The static `-O2 -Warray-bounds` idiom (`154`, `99`) belongs to the emitter
  owner. `grow A by 0` still accepted (G08 F7). Lean `ArenaDyn` refinement,
  the two `Spec.lean` (d) texts, and `LG005` lifting are other lanes'.
- Last `./lean-bau` result line: `Build completed successfully (285 jobs).`
- Last `./cargo-pruef` result line: `== exit 0; failing tests: 0`
  (`1327 passed, 0 failed, 1 ignored`).
