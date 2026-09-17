# MUSE-REPORT-239 — Dynamic-table design (`PLAN-DYNAMISCH.md`)

## What was done

Wrote `dokumente/PLAN-DYNAMISCH.md` (new file, ~360 lines, design only — no code,
no codes, no probes, MARKE_EMIT untouched) for TODO wave D (lanes 240–244).

Design summary:

- **Ceiling:** `arena A capacity lo .. hi max M of T` — `M` a translation-time
  constant, `0 <= lo <= hi <= M`. Without `max`, today's meaning byte for byte
  (`M = hi`). Scope reading stated explicitly: wave-D `max` goes on arena
  declarations; tables keep static `count` (pool form already covers per-element
  release); the constraint's substance (static ceiling, refusal beyond, visible
  growth) is honored for arenas.
- **Reservation vs commit:** virtual range for `M` reserved by the runtime at load;
  committed prefix `hi <= c <= M` grown explicitly; commit monotone within a run;
  `reset` keeps commit (one store, as today); no decommit statement.
- **DECISION 1 — growth trigger: explicit `grow A by n else B;` with costs.**
  Rejected: fault-driven commit with latency assumption (invisible commit violates
  the binding constraint; per-access fault latency breaks the waiting-bound story;
  fault-handler TCB is the most OS-specific code in the system). Revisit condition
  stated as a measurement that does not exist today.
- **DECISION 2 — free discipline: arena-reset proof.** Rejected: linear free-list
  (needs a per-slot liveness domain ≈ a second `arena.rs`, plus per-object ghost;
  duplicates the table pool form). Revisit condition: a corpus program with
  interleaved lifetimes no reset placement separates (none exists today).
- **Checker (§4):** per-path `(count, committed)` flow; five rules (R-max, R-commit,
  R-grow-else, R-grow-const, R-grow-form) with `N212`-style sentences; joins take
  `max` counts / `min` committed; `N210`–`N214` extended, never weakened.
- **Emitter/runtime (§6):** program-carried descriptor (`base`, `used`,
  `committed`, const `M`/`hi`) + two runtime functions
  (`gabbro_arena_reserve`, `gabbro_arena_grow`) with all OS tokens strictly inside
  `laufzeit/*.c`, guarded mechanically. `alloc` lowering = today's checked form
  with `committed` for the `hi` immediate.
- **Costs (§§7–8):** `grow` priced through existing `K003` callee-costs machinery;
  `K002` sees every `grow` inside `locks`. **X = 10%** fast-path budget fixed
  (one word load vs one immediate on a ~10-op sequence), ghost 0 bytes, runtime
  bookkeeping exactly 2 words/arena, with the measurement method.
- **Lean sketch (§9):** `ArenaDyn.lean` with `DynForm` (table spans `M`, committed
  prefix, prefix property by construction), four theorem shapes mirroring
  `ArenaZucker.lean` §4, a refinement statement (dynamic run simulates static-max
  program), `_zeuge` on the reference fixture, and exact English wordings for the
  two new (d) ONE-list entries (`Laufzeit.reserve`, `Laufzeit.commit`) plus the
  recorded-but-not-inserted fault-latency text.
- **Builder lanes (§10):** 240 (syntax/parser), 241 (checker), 242 (emitter/runtime),
  243 (costs/budget), 244 (Lean/assumptions), each with reads-first list, exact
  deliverable, dependencies, and number discipline (codes/gifts/examples REQUESTED
  from the orchestrator past the §-1 blocks — no self-assignment), plus a
  rejected-shape log so nothing is relitigated.

## Verification

Design-only lane: no Lean changes, no Rust changes. `./lean-bau` not affected
(no `grammatik/` change — verified by `git status`: only the two new files).
No guardians read new patterns (no document moved except the new plan itself).

## What remains open / findings

1. **TODO.md has no §-1 wave D and `messung/SPEICHER-CENSUS.md` (lane 238) is not
   in the tree.** The plan defines wave D's lanes 240–244 standalone and fixes X
   against the static-arena lowerings instead of the census, with a
   reconcile-or-report row for lanes 242/243 if the census lands first. If the
   orchestrator numbers wave D differently, §10's table needs a rename pass only —
   no design content changes.
2. **`OFFEN.md` O14 shape (1) (bare `alloc` without `else`) stays open by decision:**
   dynamic arenas inherit it. A builder lane that "fixes" it inside wave D is out
   of scope — the plan says so (§6).
3. **Table-side `max` is reserved, not built.** If the owner meant `table … max M`
   literally for tables in wave D, §1's scope reading needs an owner override and
   lanes 240/241/244 each gain a table arm. I recommend against it (duplicates the
   pool form), but the call is the owner's.
4. Anything in the task I believe is wrong: nothing — the two DECISIONS were
   decidable from the constraints plus the tree, and both rejected alternatives
   are recorded with revisit measurements.

## Files

- `dokumente/PLAN-DYNAMISCH.md` (new, design)
- `MUSE-REPORT-239.md` (this file)
