# MUSE-REPORT-198 (lane 198, TRANSFER 1: exporter produces an `Einheit`)

Session role: finish-and-commit session. The earlier session left three
modified source files uncommitted; this session inventoried them
(`git status`/`git diff`), repaired the two failing suites, extended the
tests, measured everything below, and commits.

## What was already in the tree (inherited, not started over)

`crates/gabbro-check/src/lean_g.rs`, `obligations_g.rs`,
`gegenbeispiel.rs` (+374/-151 lines): the exporter emits the real
`requires` (Held-only clauses stay in the signature, value clauses travel
as `gReq_<fn>`), the member lists `gLs`/`gCs`, the zero-memory `gSp0`, and
`def gE : Zielsatz.Einheit gD` (starts from `concurrent` members plus
`entry`/`boot` dispatch roots, `.nil` arguments each); `obligations --g`
states `nutzerPflicht : NutzerPflicht gE` with decided `gFs/gLs/gCs_voll`,
decided `gCheck`, and `gP_gabbro` derived from `gabbro_ziel`.

## What this session changed (on top)

1. `obligations_g.rs`: `gCs_voll` now proves the `inl` arm by
   `simp [gCs]` (and `inr` by `cases g <;> simp [gCs]`), with a comment
   recording why. Measured cause: `decide` fails with
   `failed to synthesize Decidable (Sum.inl … ∈ gCs)` on 104 AND 108 --
   instance search does not unfold the `gD` declaration to reach the
   derived `DecidableEq` instances; `simp` rewrites membership over the
   literal list to constructor equalities and needs no instance.
2. `crates/gabbro-check/tests/obligations_g.rs`: rewritten to the new
   output (old pins `pflicht`/`KoerperGutS`/`gP_ziel` failed against the
   new export by construction). Now pins `nutzerPflicht`, the three
   `_voll` theorems, `gCheck`, `gP_gabbro` via `gabbro_ziel`, plus a new
   `obligations_108_starts_travel` test.
3. `crates/gabbro-check/tests/lean_g.rs`: 11 new tests (names in the next
   section). One repair during the session: `requires_value_travels`
   first read a protected table without holding its lock and correctly
   got `LG004` at the *body*; the positive probe now uses an unprotected
   table.
4. No Lean file touched, added, or removed; no corpus file touched;
   `MARKE_EMIT` untouched. Scratch probe files live under `$TMPDIR/l198`
   (not committed): the four generated files and the two hand-augmented
   obligations files.

## New definitions / theorems / tests (exact names)

Rust (`lean_g.rs`): `CheckedFn.requires`, `Model.wurzeln`,
`held_aus_klausel`, `requires_ctx`, `Ctx.in_requires`, `Ctx.quelle`,
`tr_contract_requires`, `check_starts`, `check_sp0`, `emit(…, startet)`;
emitted Lean decls: `gReq_<fn>`, `gLs`, `gCs`, `gSp0`, `gE`.
Rust (`obligations_g.rs`): `abschnitt` now emits `nutzerPflicht`,
`gFs_voll`, `gLs_voll`, `gCs_voll`, `gCheck`, `gP_gabbro`.
Tests (`tests/lean_g.rs`): `export_104_carries_the_unit`,
`export_104_requires_stays_true`, `requires_value_travels`,
`requires_held_and_value_travel`, `refuses_call_in_requires`,
`refuses_result_in_requires`, `concurrent_members_travel_to_starts`,
`export_108_starts_travel`, `refuses_start_with_params`,
`refuses_sp0_outside_zero`, `entry_root_travels_to_starts`.
Tests (`tests/obligations_g.rs`): `obligations_104_states_the_user_duty`
(rewritten), `obligations_108_starts_travel` (new),
`obligations_104_keeps_the_export` (rewritten),
`obligations_single_function` (rewritten); three refusal-travel tests
unchanged.
Hand-proved (scratch, `./lean-probe` green, not committed):
`hand104_start`, `hand104_lokal`, `hand108_start`, `hand108_lokal`.

## Measured numbers (before -> after)

- `./cargo-pruef`: `exit 101; failing tests: 2`
  (`obligations_104_states_both_duties`, `obligations_single_function`)
  -> `== exit 0; failing tests: 0` (full workspace, `--no-fail-fast`).
- `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s)`,
  `Build completed successfully (230 jobs).`
- `./emission-pruef`: `== exit 0` (553-line log; the only warning lines
  are a pre-existing `DeclInfo` visibility notice in `certstmt.rs`).
- `./lean-probe` on generated files (rebuilt binary):
  `lean-g 104` 0 errors; `obligations --g 104` 0 errors (was 1:
  `gCs_voll`); `lean-g 108` 0 errors; `obligations --g 108` 0 errors
  (was 1). The 108 obligations file decides `gCheck` true WITH two
  declared starts, and `gP_gabbro` typechecks against `gabbro_ziel`.
- Scratch hand proofs, both 0 errors: 104 `StartPflicht gE` (starts
  vacuous, invariant `fun _ => true` at `gSp0`) and `SperrInvLokal gS /\
  AxEnsLokal gE.Q` (no-op invariant, `Ax := Empty`); 108 the same with
  two real starts (`ReqAmEintritt` at `.wahr` requires, closed by
  `simp only [ReqAmEintritt, gE, gP, g_read_a, g_read_c, eval, wahr?]`).
- New refusals and their probes: `LG001` start-with-parameters
  (poison `refuses_start_with_params`; positive
  `concurrent_members_travel_to_starts`, `entry_root_travels_to_starts`);
  `LG005` start naming nothing exported (poison
  `refuses_concurrent_unknown`, pre-existing; positive same as above);
  `LG003` requires-without-`Expr`-form incl. `result`
  (poisons `refuses_call_in_requires`, `refuses_result_in_requires`;
  positives `requires_value_travels`,
  `requires_held_and_value_travel`); `LG003` integer range holding no
  zero (poison `refuses_sp0_outside_zero`; positive: 104/108 pin `gSp0`).
- `git diff --stat`: 5 files, +594/-194 (3 src + 2 tests). No `sorry`,
  `axiom`, `native_decide` in the diff (only the words "axioms" and
  "sorry-free" inside comments); `MARKE_EMIT` untouched.

## Still open (explicitly NOT measured / NOT done)

1. The `LogikPflicht` body triples (`∀ passes f, KoerperGutS ∧ InvGutS ∧
   InvGutGrund`) are not hand-proved for the new export on 104 or 108.
   Only the budget-free conjuncts (`StartPflicht`, `SperrInvLokal`,
   `AxEnsLokal`) are proved (scratch). The per-function execution proofs
   need a Pflicht104-style port to the new export namespace.
2. `GenOblig104.lean` / `Pflicht104.lean` still pin the OLD obligation
   form and were deliberately NOT touched (reviewer rule + green build);
   regenerating `GenOblig104` with the new exporter would break
   `Pflicht104` (it opens `pflicht`/`gP_ziel`, which no longer exist).
   That migration is the natural follow-up lane.
3. `beispiele/124` does NOT export: `LG004 … RufPasst.hb` (a floored
   caller into a floorless callee) from `lean-g` itself, unrelated to
   this lane. The concurrent end-to-end runs on 108 instead.
4. The `LG005` ambiguous-start arm (two functions, one short name) has no
   probe; it is defensive (surface syntax gives unique short names) and
   shares its code with the probed unknown-name arm.
5. `gegenbeispiel.rs`: comment-only updates (requires now travels, hits
   kernel-check it); no fresh counterexample search was measured.
6. Text guardians and `abnahme.py` were not run (no document changed).

## What I believe is wrong in the task

- "`reuse Pflicht104.lean`" reads as theorem reuse; it can only be
  technique reuse. `Pflicht104` proves duties over the checked-in OLD
  export namespace; the new `NutzerPflicht gE` lives over a freshly
  generated namespace with different declaration types, so nothing ports
  by import -- the body proofs must be re-done, and `GenOblig104` must
  be regenerated first (which breaks `Pflicht104` as it stands).
- "124 or 108" as the concurrent program: 124 is not exportable
  (`LG004`/floor rule), so 108 is the only candidate of the two; the
  task should name 108 directly.
