# MUSE-REPORT-240 — checker: `max` cap, growth points, cap refusal (TODO §-1 wave D)

Lane 240, 2026-09-17. Scope as tasked: `arena.rs`, `saetze.rs`, tests/probes.
`kosten.rs` read-only, no `emit.rs`, no Lean, no `MARKE_EMIT*`, no OS constants.

## What was built

The `(count, committed)` growth accounting of `PLAN-DYNAMISCH.md` §4, with the
ceiling tied to `hi` — no `max` syntax exists, so floor and ceiling coincide by
construction (`M = hi`, committed `= hi` on every path). No verdict moves.

**`crates/gabbro-check/src/arena.rs`** (only checker file touched):

- `Stand` gains `verpflichtet: HashMap<String, u64>` (committed prefix per
  arena per path; absent means the floor).
- `Laeufer` gains `boden: HashMap<String, u64>` (floor = `hi` per arena, built
  once per pass); `bodenwert()` admits exactly the `N210` shape
  (`0 <= lo <= hi`, `hi >= 1`, `hi` namable).
- Joins run the §4 directions: `Stand::vereinige` takes `max` of counts (as
  before) and `min` of committed (new, with floor fallback for untouched
  sides); `reset` restores `(0, floor)` (monotone commit); all three
  `schleife` arms merge the committed axis via `verbinde_verpflichtung`
  (minimum of entry and exit — capped by `M` by construction, so no
  `UNENDLICH` saturation on this axis).
- `alloc()` is verdict-identical: the `N212` check still holds the `else`
  against `lo` (sharper than committed while committed `== hi`, documented
  inline), plus a `debug_assert!` pinning the ceiling invariant
  (committed `<= M`) with the `R-max` wiring point named beside it.
- Module head documents the accounting, the cost-visibility contract, and the
  `R-max` finding below.

**`crates/gabbro-check/src/saetze.rs`**: new sentence `arena.wachstum_sichtbar`
with `kennungen: &[]` (precedent: `namen.asm_never_angenommen`). It pins the
accounting — every growth point (`alloc`/`reset`) carries its cost into
`K001`/`K002`/`K003`, over-cap growth without a branch is `N212`, growth with
the branch declared is accepted — and records that `R-max`/`R-grow-*` need the
parser lane. No code in the sentence means `pruefe-saetze.py` is untouched in
both directions (exit 0; 416 codes, 173 sentences, 55 without sentence,
0 invented — the booked MARKE=55 holds).

**Probes, both directions** (no new codes, so no new gift numbers consumed
beyond one):

- `beispiele/gift/1087-arena-ueber-kappe.gab` (`-- erwartet: N212`): over-cap
  growth (third `alloc` on `capacity 1 .. 2`, count 2 `== hi`) without a
  branch. Verified `N212` alone (sauber by the `zaehle-gifttreffer.py`
  definition: exactly one hit) — gift marks safe by construction
  (sauber 271 → 272 against floor 271, verdeckt unchanged at 24).
- `paesse.rs::arena_kappe_ohne_else_n212`: same poison with `faellt_genau`
  (`["N212"]`) plus the clean twin (branch declared — the `beispiele/99`
  shape — `faellt_nicht`).
- `paesse.rs::arena_wachstum_in_sperre_k002`: three `alloc`s under
  `locks L` against `held <= 2 ops` fall with exactly `["K002"]`; the twin
  under `held <= 64 ops` is clean. This is the constraint-2 payoff as a
  probe: growth inside a critical section is priced where the latency
  promise lives (via the existing `sperrbloecke` walk — `kosten.rs`
  untouched).
- Six unit tests in `arena.rs::wachstumstests`: join directions
  (`verbindung_max_zaehlung_min_verpflichtung`), untouched side at floor,
  grown side capped at the minimum, reset restores floor (and leaves unknown
  state unknown), `bodenwert` faces, and `kappe_erreicht_feuert_auf_neunundneunzig`
  (the unwired `R-max` predicate firing on the `99` shape — see below).

## Measurements

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full `cargo build` +
  `cargo test --no-fail-fast`). All six `wachstumstests` pass; both new
  `paesse` tests pass; `beispiele.rs` (98/99 clean, all gifts fall with
  their code), `korpus.rs` (named codes only), and
  `keine_zwei_korpusdateien_teilen_eine_nummer` pass.
- Corpus verdict diff: zero intended or unintended moves — the diff adds no
  `melde` call and changes no refusal condition (verified by reading the
  diff; the suite above is the machine check).
- `pruefe-saetze.py` exit 0, `pruefe-kennungen.py` exit 0 (ALL PASS).
- `zaehle-gifttreffer.py` could not run in this environment (its staleness
  latch trips on test-file mtimes and falls back to `cargo`, which is not on
  `PATH` for direct guardian runs — pre-existing, reproduces on master; the
  marks argument above stands in its place).
- `./lean-bau` not run: the diff touches no file under `grammatik/` (git
  status shows only the four files above plus this report), so the Lean build
  is unaffected by construction; the merge gate rebuilds it anyway.
- No `MARKE_EMIT*` strings added or moved (grepped); `emission-pruef` not
  affected (the emission script enumerates fixed file lists; a refused gift
  is not emitted).

## Findings (report, not built)

1. **`R-max` is unbuildable on current syntax — measured tightening.**
   `PLAN-DYNAMISCH.md` §4 `R-max` (refuse the `alloc` whose static count may
   reach `M` even with an `else`) wired with `M = hi` fires on
   `beispiele/99-arena-grenze.gab`'s third `alloc` (`Klein capacity 2 .. 2`,
   count 2 `== M`, `else` present). That demo is load-bearing (boundary
   behavior, emission included, named in `arena.erklaerung`'s positive
   direction and in `OFFEN.md` O14's unblock list). Wiring it would be a
   tightening of the lane-184 class (rejected for breaking a frozen
   excerpt). Pinned as the `kappe_erreicht_feuert_auf_neunundneunzig` unit
   test (predicate fires on `(2, 2)`, silent on `(0/1, 2)`) instead of a
   rule. Reserves `N426`–`N430`, gifts `1088`–`1091`, and examples go back
   unused.
2. **Design gap: the parser lane is missing.** `PLAN-DYNAMISCH.md` §10 gives
   the `max`/`grow` syntax to a lane owning `lex.rs`/`parse.rs`/`ast.rs` +
   `SYNTAX.md` §9.1; TODO §-1 wave D (the binding table for this lane) gives
   no lane that ownership — lane 240 (this one) is checker-only and
   explicitly forbidden from touching the parser. Do not invent a second
   design: the `max M` clause shape, `grow A by n else B` statement shape,
   and `SYNTAX.md` deltas are lane 239's §2 text verbatim, still unowned.
   Until it lands, `R-commit` coincides with `N212`, and `R-grow-else` /
   `R-grow-const` / `R-grow-form` have no syntax to fire on.

## Handoff

- **Lane 241 (checker rules):** wire `R-max` in `Laeufer::alloc` beside the
  `debug_assert!` (the `obergrenze`/`verpflichtung` accessors already exist;
  scope `M` above `hi` from the new `ArenaSig::max` field — needs the parser
  lane first); re-point the `N212` comparison at the committed value where
  it exceeds `hi` (comment marks the spot); add the `StmtArt::Grow` arm in
  `anweisung()` (bump committed, cap `M`; `else` joins like `alloc`'s);
  mint from `N426`–`N430` with sentences in the same commit. The
  `vereinige`/`verbinde_verpflichtung`/`reset` merges need no changes — only
  the bump site and the two refusal sites.
- **Lane 242 (emitter/runtime):** the descriptor fields to emit are
  `committed` (init `hi`) beside `used`; `reset` lowering unchanged
  (`used = 0`, committed untouched — the monotone fact is now checker state
  too). Cost side: `grow` prices through the existing `Alloc`-shaped arm in
  `kosten.rs` (`Alloc` arm line ~1080, `ResetArena` ~1087, `sperrbloecke`
  walk) — lane 243 owns that file with 232.
- **Parser lane (unowned):** `arena … max M` (`M` same constness as `lo`/`hi`,
  `0 <= lo <= hi <= M`, `M >= 1`, `M <= u32::MAX`), `grow A by n else B;`
  into `StmtArt`, `ArenaSig::max`, `SYNTAX.md` §9.1 + vocabulary guardians
  (patterns bilingual before the document moves).

## What I believe is wrong in the task

TwoLow-severity frictions, neither blocking: (a) the wave-6 preamble
("independent reviewer … do not change any existing file") contradicts the
lane-240 task (checker code + probes + report, all committed) — I followed
the specific task, which also matches TODO §-1; (b) the reservation text
promises "positive: capped growth with declared points" as a gift probe,
but positive probes live in `paesse.rs`/`beispiele/`, not in `gift/`
(gifts are red by construction) — delivered there instead.

## Names added

- `arena.rs`: `Stand::verpflichtet`, `Laeufer::boden`, `bodenwert()`,
  `Laeufer::obergrenze()`, `Laeufer::verpflichtung()`,
  `Laeufer::verbinde_verpflichtung()`, `wachstumstests::{boden,
  verbindung_max_zaehlung_min_verpflichtung,
  unberuehrte_seite_steht_am_boden,
  seite_ueber_boden_wird_am_minimum_gekappt, reset_stellt_boden_wieder_her,
  bodenwert_nur_brauchbare_schranken,
  kappe_erreicht_feuert_auf_neunundneunzig}`.
- `saetze.rs`: `arena.wachstum_sichtbar` (no codes).
- `paesse.rs`: `arena_kappe_ohne_else_n212`,
  `arena_wachstum_in_sperre_k002`.
- `beispiele/gift/1087-arena-ueber-kappe.gab` (`N212`).
- Last `./cargo-pruef` result line: `== exit 0; failing tests: 0`.

Open: the parser lane (finding 2); lanes 241/242 consumption (handoff);
re-running `zaehle-gifttreffer.py` where `cargo` is on `PATH`.
