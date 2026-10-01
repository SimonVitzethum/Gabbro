# MUSE-REPORT-636: Operational failover closure

## Scope

Lane 636 closes the four operational gaps the coordinator rejected for
deployment after accepting candidate 620 narrowly (reports 620/621 read).
Owned paths only: `instrumente/coordinator-failover.py`,
`instrumente/tests/test_coordinator_failover.py`,
`dokumente/x86/COORDINATOR-FAILOVER.md`, `MUSE-REPORT-636.md`.
No Lean, Rust, checker, emitter, live-root or provider contact; fixtures and
fake binaries only, scratch under the clone `.tmp/`.

## What was done

1. Slot/role survival across supervisor crash/budget exit. The SAME locked
   slot and role descriptions are inherited into the model via
   `Popen(pass_fds=...)` and into a dedicated slot-guardian child in its own
   session (never in the fallback group). Any survivor keeps the kernel
   flock until the whole group drains. Restart adoption recognises a
   still-held slot as externally held (no best-effort release, no different
   slot); only a free recorded slot (pre-inheritance leases) is re-held with
   a fresh guardian. Lease carries `guardian_pid`.
2. Boundary locks held across termination. Stop needs a clean tree AND
   `foreground-action.lock` EX AND `watch.lock` EX HELD through signal,
   group drain and lease update -- never probe-and-release. Nonblocking
   acquire per poll while holding the lease lock (no deadlock; holders
   progress, supervisor retries next poll). Watch-busy writes a
   supervisor-owned `coordinator-pause.json` and removes only its own file.
   Only the fallback's own process group is ever signalled; foreign
   watcher/user groups are never touched.
3. Release only after descendants gone. `group_members(pgid)` (kernel
   `/proc` scan, zombies excluded) gates every release: direct-gone with
   strays keeps slot/role and lease (`descendants_remain_<n>_slot_held`);
   stop drains with `wait_group_gone` (30 s) while holding boundary, lease
   and slot/role, else fails closed (`descendants_remain_fail_closed`).
4. Dispatcher once, kept stopped. `dispatch_stop` once to reserve the next
   completion, kept stopped while awaiting a slot with 30 s backoff and no
   stop/start churn; restored on fresh heartbeat, explicit pause, failed
   launch or successful handoff. `role_held_by_other` backs off instead of
   churning. Budget/pause exit restores a held dispatcher.

## Names

`GUARDIAN_MARKER`, `proc_pgrp`, `group_members`, `wait_group_gone`,
`guardian_code`, `spawn_guardian`, `guardian_alive`, `acquire_boundary`,
`close_fhs`, `own_pause_path`, `ensure_own_pause`, `remove_own_pause`;
extended `run_supervise` (dispatcher_held, guardian adoption, held-boundary
stop, group-drain release, pass_fds launch); lease key `guardian_pid`;
status key `dispatcher_held`; notes `adopted_live_fallback_slot_held`,
`descendants_remain_<n>_slot_held`, `descendants_remain_fail_closed`,
`slot_exhausted_dispatcher_held`.

## Verification

- `python3 -m py_compile` on both Python files: OK.
- `python3 instrumente/tests/test_coordinator_failover.py`: **21 tests,
  0 failures, 0 errors** (16 inherited + 5 new ClosureTest). Last full run
  green; `git status` shows only the three owned paths plus this report.
- New kernel-lock tests (real flock/processes, fixture scratch): slot
  survives supervisor exit with 14 remaining reservable and 16th refused;
  orphaned same-group strays keep the slot until all gone; busy action and
  busy watch block the kill (owned pause requested, decoy survives) until
  released; full pool keeps one dispatch_stop with zero starts until a slot
  frees, then hands off and restores.
- Existing `slot_exhausted` note updated to
  `slot_exhausted_dispatcher_held`; all other inherited tests unmodified
  and passing.
- Tools-only lane: no `grammatik/` contact, no `./lean-bau` claim needed;
  no `cargo` runs (no Rust contact); `git diff --check` clean except
  pre-existing ResourceWarnings from un-reaped fixture Popen handles.

## Findings

- `python -c` argv indexing: `sys.argv[1]` is the marker, not the pgid;
  the first guardian draft read `[1]/[2]` and crashed instantly. Fixed to
  `[2]/[3]/[4]/[5]`; the crash-adoption test caught it.
- Holding the lease EX while blocking on boundary locks would deadlock
  against the foreground mutation gate (action EX then lease SH), so the
  stop path acquires boundary nonblocking per poll and holds only on
  success -- closing the TOCTOU without deadlock.
- Go-family runtimes close extra fds on exec, so pass_fds to the direct
  model alone cannot cover grandchildren; the Python guardian (no exec,
  own session) is what holds the shared description until the group
  drains.

## What remains open

- A descendant that leaves its process group (`setsid`/new session) is not
  a group member the guardian waits for; documented, ordinary tool children
  keep the pgid.
- Watcher cooperation on `coordinator-pause.json` is assumed (request +
  owned restore implemented); a watcher that never yields fails closed by
  design (never killed).
- I disagree with nothing in the task; no weak-limit footnote remains --
  the old best-effort slot paragraph is replaced by the inherited-hold
  guarantee above with its stated `setsid` boundary.
