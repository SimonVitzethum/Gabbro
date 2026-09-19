# MUSE-REPORT-255 — concurrent exporter: masked locks + deadline drop (TODO §1 residue)

Lane 255 (Rust, exporter widening). Branch `muse/255`. Exclusive scope kept:
only `crates/gabbro-check/src/lean_g.rs`, `crates/gabbro-check/tests/lean_g.rs`,
`crates/gabbro-check/tests/obligations_g.rs`. No checker passes, no `emit.rs`,
no Lean files (read-only), no `MARKE_EMIT*`, no new N codes, no gifts, no examples.

## Census BEFORE (measured with the unmodified tree, 127 files)

- **Exports: 15** (104, 108, 109, 118, 119, 120, 121, 124, 130, 15, 16, 34, 62, 69, 73).
- First refusals: LG001 x74, LG002 x21, LG003 x1 (131), LG004 x10, LG005 x6.
- The six of this lane: **108 export, 109 export, 124 export**;
  07 refuses LG001 (`type BootPhase` linear ghost);
  59 refuses LG001 (`lock TAKT carries a form` = `masks irqs`);
  125 refuses LG004 (`function lese_schreibe falls off with a result`).

## What was done (two widenings, one class at a time, lane-254 rhyme)

**Widen A — `masks irqs` travels as `D.maskiert`** (`lean_g.rs`):
`LockModel` gains `maskiert: bool`; `read_lock` stops refusing `maskiert`
(the shared-hold branch `shared held <= …` still refuses LG001, now by name);
`emit` prints per-lock arms (`maskiert := fun | .TAKT => true | .RING => false`)
where some lock is masked and keeps the old `fun _ => false` spelling otherwise,
so every existing export stays byte-identical. The field is in the specification
(`Korpus59.lean` carries `kMaskiert` the same way: TAKT true, RING false);
G has no interrupt model, so the word names no behaviour — but it travels
instead of refusing, exactly like rank already did.

**Widen B — `deadline <= n ops arch X falsifier p` drops as NO-FORM**
(`check_fn` no longer refuses `d.deadline`; ledger lines in the module docs and
in the printed header, the latter only where a deadline was actually dropped so
existing exports stay byte-identical): the DATE, not the budget
(`FnDecl::deadline`) — owed to the machine `arch` names, discharged by the
probe, a statement about the environment and not about the program. `Korpus59.lean`
models `beispiele/59` exactly this way (bodies, Held sets, locks, starts travel;
all four deadlines do not). 59 needs both widenings in sequence (masks first,
then deadline — each step measured through the CLI).

**59 now exports and proves out.** `gabbro lean-g beispiele/59…` prints the unit
(two tables, two locks, four functions, two entry dispatch roots as
`starts := [⟨g_takt_verteiler, .nil⟩, ⟨g_ruf_verteiler, .nil⟩]`,
`programmImFragmentG` + `fussOrtGB` checks). The export elaborates with
`./lean-probe`: exit 0, 0 errors. `gabbro obligations --g` on 59 elaborates
with exit 0, 0 errors, including `gCheck … = true := by decide` (the concrete
checker accepts the EXPORTED program) and the `gP_gabbro` closing theorem.

## Census AFTER (same 127 files)

- **Exports: 16** (the 15 + 59). **Gained: +1 (59).**
- First refusals: LG001 x72, LG002 x21, LG003 x2, LG004 x10, LG005 x6.
- Moves, each with its justification:
  - 59: LG001 → EXPORT (this lane, both widenings, proved correct as above).
  - 57 (`faedenhalt`): LG001 → LG003. Its `masks irqs` wall is gone; the next
    wall is `ensures-clause in alle_anhalten has no G form` — a contract
    expression with no `Expr` form (thread-set shape), i.e. model-side
    contract work, outside this lane's lock/held/starts scope. Moved refusal,
    zero gain, honestly reported.
  - 07: still LG001 (linear ghost `BootPhase` first; behind it stand `walk`,
    `format`, entry/boot steps, axioms, `prim`/`extern` — each a different
    model class; `Korpus07.lean` proves the blockage `offen07_kein_zeuge`:
    no non-degenerate witness exists). Finding, not failure.
  - 125: still LG004. `Korpus125.lean` PROVES no faithful body term exists
    (`offen125_ret_unter_locks`: `return z` inside `locks WACHE` would need
    `[held WACHE].Perm []` against `ende = []`, uninhabited). The exporter
    refusal is the G-side face of that proved fact. Finding, not failure.
  - 108, 109, 124: still export, outputs byte-identical (verified: no
    `deadline`/`maskiert` arms in any of the 15 pre-existing exports; the two
    conditional print sites fire only on 59).

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (incl. 6 new tests; negative
  control run: breaking one assert gives `exit 101, failing tests: 1` naming
  the test, then reverted to green). No build warnings.
- `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s)` (no Lean files touched).
- `./emission-pruef`: `== EMISSION: ALL PASS` (MARKE_EMIT untouched — `git status`
  shows only the three allowed files).
- `pruefe-genlean.py`: 0 of 2 byte-identical, 2 BEFUNDE — pre-existing red since
  lane 204 (the diff hunks are exactly the O12 RELEASE-OBLIGATIONS trailer;
  nothing from this lane). Not worse by one byte.

## Honest count

Gained exports per class: **masks +1 (59), deadline +0 alone (enabler for 59),
shared-hold 0, return-under-locks 0 (proved blockage), linear/walk/format 0
(multi-class), starts-with-arguments 0 (correctly refused — see below).**
Moved between refusals: one LG001→LG003 (57). What stays refused, and where:
LG001 x72 / LG002 x21 / LG003 x2 / LG004 x10 / LG005 x6 (full table in census
files under `$TMPDIR`, not committed).

## What remains open / believed-wrong in the task

- "Only 108 exports today" is stale: 108, 109 AND 124 all exported before this
  lane (TODO §1's 15-set; my BEFORE census re-confirms). "124 needed hand model
  `Korpus124.lean`" conflates two jobs: 124's *export* was never the gap — the
  hand model proves the *premise groups* (`NutzerPflicht` etc.) over it, which
  no exporter does. 59 is the file whose export was actually missing.
- "Locks (`S` family export)" as new work is stale: the family travels since
  lane 156. The residue inside the lock class was `masks` (landed here) and the
  shared-hold branch (still refused: no G counterpart — G has one lock list per
  signature and no reader/writer split).
- "Held sections": the `held <= N ops` budgets were already dropped+ledgered;
  signature-held sets already travel (`haelt`). Nothing in the six needed more.
- "Multiple starts (declared starts with arguments, `sp0` per start)": starts
  already travel (lane 198: `concurrent` + entry/boot dispatch; 59 proves two
  entry roots). Starts WITH arguments still refuse LG001 — by design, not by
  backlog: the declaration carries no `Env` argument form, so inventing one
  would put arguments into the term that neither source nor model has. `sp0`
  per start is not a G notion (`sp0` is per-unit memory). Both surveyed, neither
  widened, deliberately.
- No rule-13 witnesses owed (Rust lane, no Lean theorems added; `#print axioms`
  N/A). No N codes, no gifts, no examples, per task.

## Names added

Rust (`crates/gabbro-check/src/lean_g.rs`): `LockModel::maskiert`; widened
`read_lock`, `check_fn` (deadline arm removed), `emit` (two conditional sites).
Tests (`tests/lean_g.rs`): `masks_irqs_travels_as_maskiert`,
`refuses_shared_hold_by_name`, `deadline_drops_as_environment_promise`,
`export_59_succeeds`, `return_under_locks_stays_refused`.
Tests (`tests/obligations_g.rs`): `obligations_59_states_masked_starts`.
