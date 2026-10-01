# Agent completion and workforce monitor (lane 595)

Read-only observer over the existing Python control plane. It reports lane
completion, live workforce counts and blockers. It never launches, resumes,
merges, publishes, kills, messages, reads credentials/configs/environments,
scans private keys, prints full cmdlines, or infers acceptance from a green
build. Restoration and backfill stay with the existing coordinator, which
applies bounded recovery; an explicit pause marker stops auto-actions in the
integration design.

## Files

- `instrumente/agent-monitor.py` — the monitor (standard library only).
- `instrumente/tests/test_agent_monitor.py` — fixture tests (standard library
  only, fixtures inside the clone). Run: `python3 instrumente/tests/test_agent_monitor.py`
- This document — usage and registry assumptions.

## Shell commands

Single scan (exits after one pass):

```sh
python3 instrumente/agent-monitor.py \
  --state-dir /path/to/x86/state \
  --manifest /path/to/x86/manifest.json \
  --once \
  --status-out /path/to/monitor-status.json \
  --events-out /path/to/monitor-events.jsonl
```

Continuous loop (sleeps `--interval` seconds between scans):

```sh
python3 instrumente/agent-monitor.py \
  --state-dir /path/to/x86/state \
  --manifest /path/to/x86/manifest.json \
  --interval 60 \
  --status-out /path/to/monitor-status.json \
  --events-out /path/to/monitor-events.jsonl
```

Against the live tree (paths are examples; only run where the coordinator
lives and never from inside a lane clone):

```sh
python3 instrumente/agent-monitor.py \
  --state-dir .claude/muse-arbeit/x86/state \
  --manifest .claude/muse-arbeit/x86/manifest.json \
  --log-dir gabbro-muse/logs \
  --report-dir messung/muse \
  --once \
  --status-out .claude/muse-arbeit/x86/monitor-status.json \
  --events-out .claude/muse-arbeit/x86/monitor-events.jsonl
```

Useful overrides:

```sh
# fixture proc root and fast heartbeat for tests/smoke runs
python3 instrumente/agent-monitor.py --state-dir S --manifest M.json \
  --proc-root /path/to/fixture-proc --stale-secs 300 --once \
  --status-out status.json --events-out events.jsonl \
  --seen-file seen.json --pause-file /path/to/pool-paused.json
```

## Inputs

| Flag | Meaning |
|---|---|
| `--state-dir` | Directory with `<lane>.json` state files. Only registered lanes are observed; stray files are ignored. |
| `--manifest` | Manifest JSON: `model`, `max_active`, `lanes[]`, `peer_reviews[]`, `delegated_peer_reviews[]`. |
| `--proc-root` | Process root, real `/proc` by default, fixture root in tests. Provides `<pid>/cmdline` and `meminfo`. |
| `--log-dir` | Optional directory with `<lane>.log` heartbeat files. Without it the monitor falls back to the `log` field of each state plus a sibling `logs/` directory. Only mtimes are read, never content. |
| `--report-dir` | Optional directory with `MUSE-REPORT-<n>.md`. Only exact `VERDICT:` / `CANDIDATE:` lines are read; a missing or ambiguous verdict stays `null` and is never inferred from build state. |
| `--pause-file` | Explicit pause marker. Siblings `<state-dir>/../pool-paused.json` and `<state-dir>/../coordinator-pause.json` are auto-detected. |
| `--model-substr` | Expected model marker (default: manifest `model`). The default match is the `opencode` binary plus the lane id. |
| `--max-active` | Override for manifest `max_active`. |
| `--stale-secs` | Heartbeat staleness threshold (default 1800). |
| `--mem-reserve-kib` | Free-memory reserve (default 8 GiB, same as the coordinator gate). |
| `--seen-file` | Restart-dedup store (default: status path with `.seen.json` suffix). |
| `--status-out` | JSON status destination, written atomically (tmp file + rename in the same directory). |
| `--events-out` | Append-only JSONL event destination (append + flush + fsync per batch). |

## What is observed

Per registered lane, from its state file only:

- `status`, `kind`, `model_pid`, `runner_pid`, `candidate_refs`, `updated`.
- Liveness: `<proc-root>/<pid>/cmdline` must exist and contain the expected
  markers (`coordinat` + lane for runners, `opencode` + lane for models).
  A live PID with the wrong cmdline is a reused/foreign PID: it is NOT counted
  as managed. An unreadable cmdline (permissions) fails closed as alive with
  identity `unknown`. Full cmdlines are never printed or stored.
- Completion: a transition into `report_ready` emits a `completion` event with
  the state's `candidate_refs` head where present (`null` otherwise) and the
  report verdict where a `--report-dir` file carries exactly one `VERDICT:`
  line. No verdict is ever derived from a build passing.
- Dead: an `ACTIVE_STATES` status (`running`, `starting`,
  `starting_feedback`, `waiting_for_slot`) with no live managed PID.
- Stalled: no state/log heartbeat within `--stale-secs`.
- Blockers: `resource` (MemAvailable below reserve), `paused`, `dependency`
  (reviewer registered while an author is not `report_ready`), `build`
  (terminal `runner_error` / `incomplete` / `needs_coordinator_fallback` /
  `stopped_for_directory_audit`, operator decision, never auto-requeued),
  `dead`, `reused_pid`, `stalled`.
- Workforce: `model_alive` vs `runner_alive` are counted separately; starting
  runners are not models. `under_utilised` is true when fewer than
  `max_active` lanes are active while pending (`ready` / `prepared` /
  `queued_isolated_restart`) lanes exist.

## Outputs

Status JSON: `generated`, `max_active`, `paused` + `pause_file`, `counts`
(registered / observed / active_or_starting / model_alive / runner_alive /
report_ready / merged / pending), lane lists, `needs_attention`,
`under_utilised`, `low_memory` + `mem_available_kib`, per-lane rows and
`blockers`. Event JSONL rows: `ts`, `kind` (`completion` / `transition` /
`dead` / `stalled`), `lane`, `from`, `to`, `head`, `verdict`, `updated`.
Completion rows deduplicate across restarts through the seen file keyed by
lane + status + updated + head.

## Pause and integration contract

When `paused` is true the integration must stop auto-actions: no launches,
resumes, merges or publications until the operator removes the marker. The
monitor itself takes no action either way; it only surfaces the flag. It does
not import or execute the coordinator, holds no locks, and creates no second
scheduler.

## Current registry assumptions (2026-10-01 snapshot)

- Manifest keys: `model` = `opencode-go/muse-spark-1.3-contributor`,
  `max_active` = 15 (permanent cap across authors, reviewers, organisers,
  integration owners and repair continuations), `lanes[]` entries with
  `lane` / `title` / `status` / `kind` (`lean`, `rust`, `docs`, `review`) /
  `priority`, `peer_reviews[]` with `reviewer` + `authors[]`, plus
  `delegated_peer_reviews[]`, `superseded_temporary_agent_limit`,
  `continuous_agent_policy`.
- State files: a JSON list of `{lane, status, model_pid, runner_pid,
  candidate_refs, updated, kind}`. Reviewer states pin
  `candidate_refs: {author: head}`; author states carry no hash, so author
  completion events record `head: null` and the exact hash stays with the
  review snapshot. `updated` is an ISO-8601 timestamp.
- Runner cmdline shape: `python …/coordinate.py run <lane> …`; model cmdline
  shape: `…/opencode run … --title muse-x86-<lane> …`. Pause markers:
  `pool-paused.json` (checked by start paths) and `coordinator-pause.json`
  (checked by the dispatch/watch loops). Memory gate: 8 GiB MemAvailable.
- If the registry changes shape (new state fields, renamed pause files, new
  terminal states), this monitor needs an owned follow-up; it must not guess.

## Limits

- The monitor cannot see work that never reaches a state file, nor distinguish
  a slow lane from a stuck one below the heartbeat threshold.
- Verdicts need `--report-dir`; without it completions carry `verdict: null`
  by design.
- Heads for author lanes are `null` by design (states carry no hash); exact
  candidate identity is established by the independent review snapshot, not
  by this monitor.
