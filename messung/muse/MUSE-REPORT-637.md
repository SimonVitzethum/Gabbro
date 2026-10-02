# MUSE-REPORT-637: Independent exact review of candidate 636

CANDIDATE: 636 c17193125b0e3b10fc9fc94d13cdba147f6735c6

VERDICT: ACCEPT

## Scope

Lane 637 reviews the exact pinned candidate 636
(`c17193125b0e3b10fc9fc94d13cdba147f6735c6`, base `97cd0e9c`) from
`.tmp/review/SNAPSHOT.json`. Owned file only: `MUSE-REPORT-637.md`.
No source, Lean, checker, emitter, provider or live-control contact; all
probes used fixture scratch and fake binaries. No real provider or live
control files were touched.

## Candidate contents (verified exact)

`git diff` of the pinned HEAD against its base shows exactly the four owned
paths: `MUSE-REPORT-636.md`, `dokumente/x86/COORDINATOR-FAILOVER.md`,
`instrumente/coordinator-failover.py`,
`instrumente/tests/test_coordinator_failover.py`.
No Lean/Rust/emitter contact, ASCII only, no credentials.

## Re-review: repair of the previous REPAIR findings

The previous review (candidate `8a549340`, verdict: repair) found one defect
with three measured consequences: `is_paused` treated `pool-paused.json`
(explicit USER pause) and `coordinator-pause.json` (INTERNAL transient
marker) identically. The new candidate repairs exactly this, confined to the
owned paths (319 insertions, 13 deletions across the four files):

- `is_paused` now reports only the user pause (`pool-paused.json`); the
  internal marker never blocks takeover, never stops the role, never exits
  the supervisor.
- New `cleanup_stale_internal_pause` (with `INTERNAL_PAUSE_MAX_AGE_SECS`,
  `internal_pause_doc/pid/age_secs`), called at startup and every poll:
  removes only a supervisor-owned marker (`owner: failover-<pid>`) whose pid
  is dead or whose age exceeds 600 s. Foreign registration markers are never
  touched and never pause coverage.
- Pause exit and budget exit now call `remove_own_pause`; SIGKILL leftovers
  are covered by the stale cleanup.
- Doc Pause section rewritten to the user/internal distinction.
- Six new kernel-lock `PauseDistinctionTest` tests (live supervise threads,
  real flock/processes, fixture scratch), each substantive: internal marker
  never stops a live role; never blocks takeover; stale own-pause cleaned
  and never blocks; foreign marker byte-identical afterwards but never
  blocks; internal marker during busy watch then removed by registration;
  user pause still stops a live role safely.

## Verification performed on the NEW head

- Candidate suite from the extracted tree
  (`$TMPDIR/cand636b`, byte-identical to the pinned files):
  `python3 instrumente/tests/test_coordinator_failover.py`:
  **27 tests, 0 failures, 0 errors** (16 inherited + 5 ClosureTest + 6 new
  PauseDistinctionTest). Green.
- Own reviewer probes re-run against the new tree (private scratch,
  ignored, not committed) with live processes and kernel flock:
  - Probe A (foreign internal marker + stale foreground + no child):
    previously exited `paused_no_takeover` with 0 turns; now takes over
    (`status=budget_done note=muse_coordinates turns=1 owner=muse`).
    Fixed.
  - Probe D (foreign internal marker + live child): previously
    `stopped_at_boundary_paused_by_coordinator-pause.json` with the child
    killed; now `owner=muse child_alive=True note=muse_coordinates`.
    Fixed.
  - Probe E (leftover own-pause from dead pid + stale foreground): previously
    blocked every future supervisor; now stale marker cleaned and takeover
    happens (`turns=1`). Fixed.
  - Control C (real user pause `pool-paused.json`): still exits
    `paused_no_takeover` with 0 turns. User-pause behavior preserved.
  - Probe B (busy watch, no other stop reason): role survives, no spurious
    handback, no leftover pause file. Unchanged.
- No `./lean-bau` run: the candidate touches no `grammatik/` file, so no Lean
  build claim is needed and none is made.

## Standing evidence (unchallenged by the repair)

Slot/role survival across supervisor crash via `pass_fds` inheritance plus a
session-separated guardian, group-drain-gated release (`group_members`,
`wait_group_gone`, fail-closed), boundary locks held (not probed) across
termination with nonblocking acquire under the lease lock (no deadlock
against the foreground action-then-lease order), crash adoption without a
duplicate or a different slot, and dispatcher stopped once and kept stopped
while awaiting a slot. The `guard_mutation_role` order (action EX, then
lease SH) is respected by the supervisor's nonblocking boundary acquire, and
`test_busy_action_blocks_kill_until_released` proves no kill across a busy
integration. The repair diff does not touch any of these paths except to add
the pause-exit/budget-exit `remove_own_pause` calls and the additive stale
cleanup; all 21 prior tests still pass unmodified.

## Final assessment

All three consequences from the previous REPAIR are fixed on the new HEAD and
re-verified independently with live processes; the six new tests cover the
required distinction (internal marker during busy watch then removed, user
pause still preventing takeover and stopping the role safely); scope stays
inside the four owned paths with no guarantee weakened. Deployment may
proceed on candidate `c17193125b0e3b10fc9fc94d13cdba147f6735c6`.
