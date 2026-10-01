# Coordinator control-plane takeover and cleanup integration audit (lane 640)

Independent adversarial audit of the supplied private coordinator snapshot as an
integration-control program. This is an audit, not a deployment approval. Full
source-to-final-byte validation remains OPEN.

## Scope and method

- Snapshot: `.tmp/COORDINATOR.py`, 2786 lines,
  sha256 `0ab771798da779638f90ea12db073fdac783fce01da086c68c7c0e89271496f1`.
- Contracts used (committed, reviewed): `dokumente/x86/COORDINATOR-FAILOVER.md`
  (lane 620 scope), `dokumente/x86/LANE-CLEANUP.md` (lane 622 scope),
  `dokumente/x86/AGENT-MONITOR.md` (lane 595 scope).
- Method: clone-local standard-library fixtures only. The snapshot is imported
  without `__main__` side effects (top level is imports plus constants, lines
  1-21; `__main__` guard at line 2699); `ROOT`/`HERE`/`POOL` are repointed to
  scratch and `/proc` reads are stubbed. No live control directory, other
  clone, provider binary, config, key or real agent was read, run or signalled.
- Result: **31/31 fixture checks passed**
  (`.tmp/scratch640/test_snapshot.py`, kept in private ignored scratch, not
  committed). Failing-tool-green is not acceptance: every finding below cites
  a reproducible code trace, not a test exit code.

## What the snapshot gets right (verified, with traces)

1. **Deployment is refused until the strong scope lands.** `failover_start`
   (lines 2301-2321) requires `merged` for 620/621 (narrow baseline) AND for
   636/637 (strong scope), plus a `lifecycle-scope-approved.json` whose
   `module_blob` equals `HEAD:instrumente/coordinator-failover.py` and whose
   `review_candidate` equals reviewer 637's pinned candidate for 636. A
   best-effort supervisor therefore cannot be armed by accident.
2. **Whole-action locks are really held.** `guard_mutation_role` (lines 49-66)
   takes `foreground-action.lock` EX|NB and `orchestrator-lease.lock` SH; the
   pair is stored in `role_guard` (line 2707) and stays referenced until the
   one-shot process exits, so both locks cover the whole CLI mutation.
   Fixture proof: with the gate held, a second EX on the action lock and an EX
   on the lease lock both fail with `BlockingIOError`. Epoch matching
   (`GABBRO_COORDINATOR_EPOCH` against the lease `epoch`) refuses stale
   writers; a `muse` role with a dead lease is refused outright.
   No foreground-mutation path `exec`s, so PEP-446 close-on-exec cannot drop
   these locks mid-action (the only `os.execv`, in `failover_watch`, carries
   no guard by construction).
3. **The 15-slot cap has a kernel backstop for lane models.** `run` (lines
   167-251) acquires one of fifteen `go-contributor-01..15` flock files with
   EX|NB, spawns the model only after acquisition (line 228), and releases in
   `finally` (line 251). Every bulk spawn path funnels through it:
   `launch`, `resume`, `peer` (via `launch`/`resume`), `dispatch`,
   `restore_ready_pool`, `recover_unfinished_pool`. Cross-process fixture
   proof: a held slot file refuses a second EX|NB from another process while a
   sibling slot file acquires cleanly. Overshoot degrades to
   `waiting_for_slot` runners, never to a 16th lane model.
4. **Merge and publication gates are exact.** `merge_lane` requires
   `report_ready`, a committed report, `enforce_peer` (exact-commit ACCEPT,
   lines 676-683), a green `./lean-bau`, and the `gabbro_ziel` triple-axiom
   check. `watch` merges only on ACCEPT with fresh candidate hashes
   (lines 838-856) and publishes only after a clean HEAD change (line 881).
   `publish` (lines 1055-1092) re-checks provenance with summary-marker
   regexes, refuses source drift since the checked head, re-checks axioms,
   refuses an ahead origin, scans outgoing added lines for secret patterns,
   never passes `--force`, and verifies the pushed ref.
5. **Task preambles are VORSPANN-built; deletions are gated.** All twelve
   registration composers read `lanes/VORSPANN.md`, and `prepare` asserts the
   `HARD RULES` prefix. Reviewers receive exact task copies (`OWNER-TASK.md`)
   before any deletion. Tracked-task removal goes through `lane-cleanup.py`
   `--apply` with per-file revalidation, and the coordinator commits only
   `.md` changes (line 2278 rejects anything else). Reports, logs, session
   databases, `VORSPANN.md` and whole folders are never deletion candidates.

## Findings

### B1 — Deployment-blocking (already gated, do not arm): slot cap does not survive supervisor death
The snapshot holds no fallback slot file descriptor itself and performs no
`pass_fds` inheritance or persistent lock-holder handoff; the fallback model
is spawned by the separate supervisor script, which is not part of this
snapshot. `COORDINATOR-FAILOVER.md` "Limits" documents exactly this:
slot accounting across supervisor restarts is best-effort. That footnote is
precisely what required scope item (1) of the 636/637 task (snapshot line
2100) refuses to accept as completion. Status: correctly refused by
`failover_start`; remains the primary deployment blocker. Documented
operational limit AND deployment blocker — not a silent defect.

### B2 — Deployment-blocking (in 636/637 scope): lease enforcement is one-directional
Only `__main__` foreground mutations (line 2706 set) pass through
`guard_mutation_role`. The long-lived loop workers — `dispatch`, `watch`,
`run`, `stop` — never check owner or epoch (verified by AST: no
lease/guard reference in any of them). So a stale fallback-owned dispatcher
keeps launching lanes after Codex reclaims the lease until the supervisor
kills its tree; mutual exclusion in that direction is delegated to the
(unreviewed here) supervisor, not established by this snapshot. Matches
required scope items (2)/(3). Correctly gated, but it must stay explicit:
this snapshot alone does not prove no kill across a busy integration and no
concurrent writers after handback.

### M1 — Non-blocking hardening: `dispatch` honors no pause marker
`dispatch` (lines 746-815) checks neither `pool-paused.json` nor
`coordinator-pause.json`. `AGENT-MONITOR.md` claims `coordinator-pause.json`
is "checked by the dispatch/watch loops": true for `watch` (lines 828, 883),
false for `dispatch`. Consequence: after a failed `register_tasks` /
`register_lifecycle_wave` (pause marker preserved, dispatcher restarted),
dispatch keeps launching while the watcher stays yielded — a split-brain
"no automatic integration" window. Enforcement today is by killing the
dispatcher (`pause_muse_pool` → `dispatch_stop`) or refusing start, never by
a live loop observing a marker. Minimal fix: check both markers at the top of
each dispatch iteration and exit to `budget_ended`.

### M2 — Non-blocking robustness: pause marker leaks on registration/cleanup failure
`register_tasks` (line 2127) and `cleanup_lane_tasks` (line 2288) write
`coordinator-pause.json` with no `finally`: on any failure the marker
persists, and for cleanup the watcher is never restarted. `cleanup_lane_tasks`
additionally never stops the dispatcher first (unlike
`register_lifecycle_wave`, line 2022). Copy the `finally` restart pattern
from `register_lifecycle_wave` (lines 2049-2055). Fail-closed, but a stall
until manual repair.

### M3 — Minor: `probe` spawns a model outside slot accounting
`probe` (lines 1122-1148) runs `OPENCODE run --agent plan` with no flock
acquisition and no capacity consultation (AST-verified: no `flock`/`locks`
in its body). Mitigating facts: it is operator-invoked only (no in-loop
callers), single-shot, 180 s timeout. Minimal fix: attempt a nonblocking slot
or refuse while 15 are held.

### M4 — Minor: inconsistent fallback headroom
`dispatch` capacity (line 756) counts `bool(fallback_identity())`;
`restore_ready_pool.room` (line 2539) does not. The kernel lock backstops
this into waiting runners, not a 16th model — align the two formulas anyway.

### M5 — Minor measurement only: zombie counting differs by action
`inventory` uses `os.kill(pid, 0)` (zombies count as alive);
`session_count`, `fallback_identity` and the overnight `identified` check
exclude `Z`/`X` states. `actual_active_models` can therefore disagree between
actions. No control impact: all launch/restore decisions use state files plus
the stronger identity checks.

### M6 — Minor: `stop` identity is weaker than `pause_muse_pool`
`stop` (lines 1151-1166) checks only `comm` in `python3`/`opencode`, then
`killpg` on a pid that may not be a group leader — a PID-reuse window at
group granularity. `pause_muse_pool` (lines 1186-1187) requires full cmdline
markers plus `getpgid(pid) == pid`. Promote `stop` to the same check.

### M7 — Minor TOCTOU in `cleanup_merged_work`
The branch-deletion path re-verifies ancestry and SHA (lines 1664-1666); the
worktree/clone removal path (lines 1634-1653) does not re-check
merged/idle/clean between inventory and `worktree remove`/`rmtree`. Narrow
single-process window; re-verify before removal.

### M8 — Minor: `failover_start` spawns even on handback signal
`root_heartbeat` returning 2 ("Muse still owns the role", line 2003) does not
stop the supervisor spawn at line 2319. The status-file liveness pre-check
(lines 2310-2316) covers the normal case; re-read the lease after the
heartbeat and refuse on rc==2 for the status-file-lost case.

### M9 — Note: observer JSON is written non-atomically
`dispatch.json`, `watch.json` and `overnight-monitor.json` use plain
`write_text`; only state/lease/manifest use tmp+rename. Torn reads affect
observers (monitor JSON errors), never control. Atomic writes are cheap;
apply for uniformity.

## CUTS (not audited)

- The supervisor `instrumente/coordinator-failover.py` itself was not supplied
  and therefore not audited; B1/B2 close only with its reviewed 636/637
  integration. Live control state was deliberately not inspected.
- No Lean, Rust, checker, emitter or proof semantics were touched or
  re-verified; merge/publication gates were audited as control logic, not
  re-executed. No credentials, networks, or live processes were involved.
- No deployment approval is given: takeover stays disarmed until 636/637 plus
  the blob/candidate approval gate pass, and full compiler/bridge validation
  remains OPEN regardless.
