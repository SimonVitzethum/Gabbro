# Coordinator failover supervisor (lane 620)

Automatic, explicitly authorised OpenCode coordinator takeover. The
foreground coordinator owns the role and renews its heartbeat lease; this
background supervisor never renews it. After the lease expires it starts
exactly one identified managed Muse fallback coordinator in a shared model
slot. It is a portable standard-library Python tool and a complement to the
existing coordinator, not a replacement scheduler: the independent
watcher/dispatcher keep running and are only paused/resumed around the role
change.

## Files

- `instrumente/coordinator-failover.py` — the supervisor (stdlib only).
- `instrumente/tests/test_coordinator_failover.py` — fixture/mock tests
  (stdlib only, fixtures inside the clone). Run:
  `python3 instrumente/tests/test_coordinator_failover.py`
- This document — usage, protocol and limits.

## CLI

Two actions, all paths explicit, no hardcoded machine paths:

```sh
python3 instrumente/coordinator-failover.py heartbeat \
  --project-root /path/to/Gabbro \
  --control-dir /path/to/x86 \
  --pool-dir /path/to/gabbro-muse \
  --coordinator /path/to/x86/coordinate.py \
  --opencode /path/to/opencode \
  --model opencode-go/muse-spark-1.3-contributor

python3 instrumente/coordinator-failover.py supervise \
  --project-root /path/to/Gabbro \
  --control-dir /path/to/x86 \
  --pool-dir /path/to/gabbro-muse \
  --coordinator /path/to/x86/coordinate.py \
  --opencode /path/to/opencode \
  --model opencode-go/muse-spark-1.3-contributor \
  --budget 43200 --timeout-seconds 300 --turn-seconds 3600 \
  --prompt-file /path/to/fallback-coordinator.md
```

| Flag | Meaning |
|---|---|
| `supervise` / `heartbeat` | Watch the lease and take over once, or renew the foreground lease. |
| `--project-root` | Git checkout the fallback coordinates (also the child cwd). |
| `--control-dir` | Private control plane dir (lease, locks, status, session db). |
| `--pool-dir` | Pool dir holding the shared `locks/go-contributor-01..15` files. |
| `--coordinator` | Existing Python coordinator; `dispatch_stop` / `dispatch_start` are sent as subprocess argv, never through a shell. |
| `--opencode` | Model runner binary (fake script in tests; no provider is contacted by this tool itself). |
| `--model` | Expected model marker used for pid identity. |
| `--budget` | Total supervise time in seconds (default 43200; `0` watches until paused). Exiting on budget never stops a live fallback; a restarted supervisor adopts it. |
| `--timeout-seconds` | Missing-foreground threshold (default 300). |
| `--turn-seconds` | Bound per fallback turn, at most 7200. Expiry waits for a safe boundary, then stops only the fallback tree. |
| `--proc-root` | Process root (`/proc`; fixture root in tests). |
| `--prompt-file` | Initial role prompt passed to the model as `--file` (the private control plane owns the text). |
| `--poll-seconds` | Lease poll interval (default 5). |

`heartbeat` is foreground-only: while an identified Muse fallback owns the
role it writes `return-to-codex.json` and exits 2 instead of overwriting the
live lease. Exit 3 rejects `--turn-seconds` above 7200; exit 4 means a second
supervisor found the supervisor lock held.

## Protocol

- **Lease.** `<control>/orchestrator-lease.json`, always written atomically
  (tmp + rename) under `<control>/orchestrator-lease.lock`. Only foreground
  `heartbeat` calls renew it (`owner: codex`). The supervisor never renews
  it; on a cooperative handback it records `owner: codex` with
  `returned_from_muse: true` so the next foreground heartbeat re-arms cleanly.
- **Takeover predicate.** Not paused, no live identified fallback,
  `owner == codex`, heartbeat age at or past `--timeout-seconds`.
- **One role.** `<control>/fallback-owner.lock` is held for the whole turn;
  the lease carries a unique `epoch`, and the child runs with
  `GABBRO_COORDINATOR_ROLE=muse` plus `GABBRO_COORDINATOR_EPOCH=<epoch>` so
  the coordinator mutation gate can refuse stale writers.
- **Shared slots.** The fallback reserves one of the same 15
  `<pool>/locks/go-contributor-01..15` flock files every managed model uses
  and holds it until its own tree is gone; at most 15 models exist. Only the
  supervisor's own dispatcher is stopped to free capacity
  (`dispatch_stop`, resumed with `dispatch_start` after launch, on pause, on
  fresh-heartbeat races and on launch failure). Contributors, watchers and the
  user's own processes are never signalled.
- **Pid identity.** A pid counts as the fallback only if its cmdline carries
  both the opencode and model markers, its state is not zombie/dead, and its
  process start time matches the lease. Reused, zombie and unrelated pids are
  ignored and never signalled; full cmdlines are never printed or stored.
- **Safe boundary.** Stopping the role needs more than a clean tree: the
  tree must be clean (no `status --porcelain` output, no `MERGE_HEAD`) AND
  the watch lock AND the foreground-action lock must be free (nonblocking
  probes, released at once). Otherwise the supervisor reports
  `waiting_for_safe_boundary_<reason>` and retries; on timeout it fails
  closed with status and preserves dirty states instead of killing anything
  outside its own tree.
- **Pause.** `<control>/pool-paused.json` or `coordinator-pause.json`
  prevents any takeover and stops a live role at the next safe boundary.
- **Retry bounds.** Launch failures and turns that die within 60 s back off
  exponentially (5 s doubling, capped at 300 s) while staying responsive to
  pause/handback. No restart storm.
- **Child scope.** The fallback starts as its own process group with a
  private session db (`<control>/sessions/fallback-coordinator.db`,
  inherited OpenCode config is never read) and SSD scratch
  (`<pool>/fallback-scratch`, never `/tmp`). Only that group is ever
  signalled. Group *existence* is not the stop criterion: orphaned
  grandchildren keep the group id alive, so the supervisor waits for its
  direct child and then SIGKILLs strays of the same group.
- **Recovery.** A restarted supervisor adopts an identified live fallback
  (re-holding its recorded slot where free) and never starts a duplicate.
  The supervisor itself is exclusive via `failover-supervisor.lock`.
- **Status.** `<control>/failover-status.json` (atomic) reports supervisor
  pid, owner, heartbeat age, model pid, slot, started turns, failures, last
  exit, pause and a short note. Logs carry no credentials.

## Root wrapper contract

The root coordinator arms this with a `failover_start`-style wrapper: refuse
until the supervisor and its tests are independently reviewed, refuse while a
supervisor lives, record one foreground heartbeat, then spawn
`supervise --budget 43200` detached with output to `failover.log`. The
supervisor performs no lane edits, no reviews and no publication by itself;
guarded publication stays behind the existing checked gates.

## Authorisation scope

The user authorises the coordinator role only, with guarded publication;
contributor no-push remains. Source edits stay delegated, reviews stay exact
and independent, and no proof or test gate is weakened to make a run green.

## Limits

- A lost heartbeat during a long foreground tool run is indistinguishable
  from a dead foreground here. Mitigation is explicit foreground heartbeats
  and the safe mutation boundary, documented above; this tool claims no
  usage-API detection.
- After the supervising process exits, its slot lock releases while the
  fallback may still run; a restart re-holds the recorded slot only if it is
  still free, so slot accounting across supervisor restarts is best-effort.
- The tool cannot see work that never reaches the lease, nor distinguish a
  slow integration from a stuck one below the poll granularity.
- Registry changes (new pause files, renamed locks, new coordinator
  actions) need an owned follow-up; the supervisor must not guess.
