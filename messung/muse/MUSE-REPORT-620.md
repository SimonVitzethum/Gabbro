# MUSE-REPORT-620: coordinator failover supervisor

## What was done

Implemented the explicitly authorised automatic OpenCode coordinator
takeover as a portable standard-library Python supervisor, with
fixture/mock tests and a CLI document. All work is in the owned paths;
no Lean, Rust or other tree files were touched.

- `instrumente/coordinator-failover.py` (new, ~740 lines): `supervise` and
  `heartbeat` actions with `--project-root --control-dir --pool-dir
  --coordinator --opencode --model --budget` (43200 default)
  `--timeout-seconds` (300 default) `--turn-seconds` (max 7200),
  plus `--proc-root --prompt-file --poll-seconds`. Foreground heartbeat
  lease written atomically under flock; the background supervisor never
  renews it. Stale lease (>= timeout) starts exactly one identified
  fallback in a shared `go-contributor-01..15` slot, with owner lease,
  role lock, unique role epoch (`GABBRO_COORDINATOR_ROLE=muse`),
  pid-plus-starttime identity, pause/handback handling, cooperative safe
  boundary (clean tree AND free watch/action locks), exponential backoff
  capped at 300 s, bounded turns, crash-restart adoption and exclusive
  supervisor lock. Coordinator contacted only via subprocess argv
  (`dispatch_stop`/`dispatch_start`); only the fallback's own process
  group is ever signalled.
- `instrumente/tests/test_coordinator_failover.py` (new, 16 tests):
  takeover starts once with slot held, freshness, pause blocks takeover,
  pause stops the role at a safe boundary, all-slots-occupied, handback
  on heartbeat while Muse owns, duplicate supervisor, pid reuse / zombie
  / wrong-cmdline / starttime mismatch, launch-failure backoff without
  storm, turn expiry killing only the own child (decoy survives),
  dirty-root delaying the stop until clean, crash-restart adoption
  without duplicate.
- `dokumente/x86/COORDINATOR-FAILOVER.md` (new): usage, protocol, root
  wrapper contract, authorisation scope and limits.

## Verification

- `python3 instrumente/tests/test_coordinator_failover.py`: **16 tests,
  0 failures, 0 errors** (last full run).
- `py_compile` on both Python files: OK.
- `git diff --check`: clean (new files only).
- Tools-only lane: no Lean edits, no `./lean-bau` claim, no `cargo` runs.
- No network, no real agents, no live control/config reads; fakes only.

## Findings during the work (kept, not worked around)

- An orphaned grandchild keeps its old process-group id alive after the
  group leader dies, so group existence never proves the fallback is
  alive. The stop path waits for the direct child (handle or
  identity-checked pid) and then SIGKILLs strays of the same group.
- The fixture `/proc/<pid>/stat` layout needs exactly 18 numeric fields
  between state and starttime for `after[19]` to be the start time; the
  first fixture draft had 17 and every identity check missed.
- The pause-exit belonged at loop level, not inside the
  child-management branch, or a paused watcher with no child loops to
  budget end.

## What remains open / limitations

- The `failover_start` root wrapper itself is not part of this lane; the
  deliverable is usable by it as specified in the document.
- Slot accounting across a supervisor-process exit is best-effort (the
  flock releases with the process while the fallback may outlive it);
  restart re-holds the recorded slot only if still free.
- A lost heartbeat during a long foreground tool run cannot be told
  apart from a dead foreground; mitigation is explicit foreground
  heartbeats plus the safe mutation boundary. No usage-API detection is
  claimed.
- I disagree with nothing in the task; the turn bound (>7200 rejected)
  and the cooperative return (clean tree alone is not safe) are
  implemented as specified.

## Names

`run_heartbeat`, `run_supervise`, `should_takeover`, `identify_model`,
`leader_alive`, `stop_own_child`, `safe_boundary`, `reserve_slot`,
`lock_slot`, `coordinator_action`, `model_env`, `model_argv`,
`update_lease_locked`, `write_status`, `SLOT_COUNT=15`,
`MAX_BACKOFF_SECS=300`.
