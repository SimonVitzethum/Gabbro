# MUSE-REPORT-637: Independent exact review of candidate 636

## Scope

Lane 637 reviews the exact pinned candidate 636 (`8a54934026ebc5781f7395178726f127841de5a6`,
base `97cd0e9c`) from `.tmp/review/SNAPSHOT.json` with TASK/PATCH under
`.tmp/review/author-636/`. Owned file only: `MUSE-REPORT-637.md`.
No source, Lean, checker, emitter, provider or live-control contact; all
probes used fixture scratch and fake binaries. No real provider or live
control files were touched.

## Candidate contents (verified exact)

`git diff --name-only` of the pinned HEAD shows exactly the four owned paths:
`MUSE-REPORT-636.md`, `dokumente/x86/COORDINATOR-FAILOVER.md`,
`instrumente/coordinator-failover.py` (1210 lines),
`instrumente/tests/test_coordinator_failover.py` (751 lines).
The extracted candidate tree matches `.tmp/review/author-636/` byte for byte
(`diff -q` clean on both Python files). No Lean/Rust/emitter contact, ASCII
only, no credentials.

## Verification performed

- Candidate suite from the extracted tree:
  `python3 instrumente/tests/test_coordinator_failover.py`:
  **21 tests, 0 failures, 0 errors** (16 inherited + 5 new `ClosureTest`),
  real flock/processes, fixture scratch. Green.
- Own reviewer probes (private scratch `$TMPDIR/probe637.py`,
  `$TMPDIR/probe637b.py`, ignored, not committed) with live processes and
  kernel flock:
  - Control C (user pause): `pool-paused.json` + stale foreground + no child
    exits `paused_no_takeover` with 0 turns. Correct per contract.
  - Slot survival / 16th refusal, busy-action block, busy-watch owned pause,
    full-pool single `dispatch_stop` without churn: covered green by the
    candidate's own `ClosureTest` (re-ran, passing).
- No `./lean-bau` run: the candidate touches no `grammatik/` file, so no Lean
  build claim is needed and none is made.

## What the candidate gets right

Slot/role survival across supervisor crash via `pass_fds` inheritance plus a
session-separated guardian, group-drain-gated release (`group_members`,
`wait_group_gone`, fail-closed), boundary locks held (not probed) across
termination with nonblocking acquire under the lease lock (no deadlock
against the foreground action-then-lease order), crash adoption without a
duplicate or a different slot, and dispatcher stopped once and kept stopped
while awaiting a slot. The `guard_mutation_role` order (action EX, then
lease SH) is respected by the supervisor's nonblocking boundary acquire, and
`test_busy_action_blocks_kill_until_released` proves no kill across a busy
integration.

## Findings (all reproduced with live processes, not mocks)

The supervisor does not distinguish the two pause files. `is_paused`
(`coordinator-failover.py:139`) returns True for `pool-paused.json` (explicit
USER pause) and `coordinator-pause.json` (INTERNAL transient safe-boundary
marker) identically, and the document (`COORDINATOR-FAILOVER.md`, Pause
section) records the conflation as intended behavior. Three consequences,
each measured:

1. **Internal marker kills the live role (probe D).** Live fallback, foreign
   `coordinator-pause.json` (`owner: register_tasks-999`, no return request,
   no user pause): within 2 s the supervisor reported
   `stopped_at_boundary_paused_by_coordinator-pause.json`, lease back to
   `codex`, child dead. The supervisor kills its own coordinator for a busy
   registration marker.
2. **Internal marker permanently ends coverage with no child (probe A).**
   Stale foreground + foreign internal marker + no live child: supervisor
   exits `rc=0 paused_no_takeover`, 0 turns. A transient registration marker
   is treated as user shutdown; nothing restarts the supervisor, so takeover
   coverage is lost.
3. **Leftover own-pause file blocks all future supervisors (probe E).**
   `ensure_own_pause` writes `owner: failover-<pid>`; the budget-exit path
   never calls `remove_own_pause`, and `remove_own_pause` refuses foreign
   owners while `ensure_own_pause` will not overwrite them. A leftover file
   from a dead pid (SIGKILL/crash between ensure and remove) makes every
   future supervisor exit `paused_no_takeover` with 0 turns. Nothing in the
   protocol cleans it.

## VERDICT: REPAIR

The pause distinction is a deployment requirement of the lane-637 task, and
probe-only safety for it is explicitly a repair trigger. Required repair,
kept small and inside the candidate's owned paths:

- Track which pause file is present; only `pool-paused.json` (user pause)
  may block takeover, stop the role, or exit the supervisor.
- `coordinator-pause.json` (internal, including the supervisor's own file)
  must never be a stop reason, a takeover block, or an exit reason; exclude
  the supervisor's own `failover-<pid>` file from the pause check.
- Give the internal marker ownership/expiry handling (own pid liveness or
  timestamp) so a leftover from a dead supervisor cannot permanently block
  coverage, and add kernel-level tests for: internal marker present during a
  busy watch action then removed by registration (role survives, coverage
  continues), own-pause lifecycle across budget exit, and user pause still
  preventing takeover and stopping the role safely.

No source-guarantee weakening is involved; no finding contradicts the
candidate's slot/guardian/boundary/dispatcher evidence, which stands.
