# Coordinator failover supervisor (lanes 620, closed 636)

Automatic, explicitly authorised OpenCode coordinator takeover. The
foreground coordinator owns the role and renews its heartbeat lease; this
background supervisor never renews it. After the lease expires it starts
exactly one identified managed Muse fallback coordinator in a shared model
slot. It is a portable standard-library Python tool and a complement to the
existing coordinator, not a replacement scheduler: the independent
watcher/dispatcher keep running and are only paused/resumed around the role
change.

Lane 636 closes the four operational gaps the independent review accepted
as documented limits: inherited slot/role survival across supervisor
crash, boundary locks held across termination, release only after the
whole group drains, and churn-free dispatcher reservation.

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
  `<pool>/locks/go-contributor-01..15` flock files every managed model uses.
  The SAME locked slot and role descriptions are inherited into the model
  (`Popen(pass_fds=...)`) and into a dedicated slot-guardian child that runs
  in its own session (never in the fallback group, so `killpg` on the
  fallback never signals it) and exits only after the fallback process
  group has no live member left. Any survivor holding the inherited
  description keeps the kernel lock, so a supervisor crash or budget exit
  cannot free the 15-slot accounting while fallback tools still run, and
  orphaned grandchildren (same pgid, reparented) keep the slot held: the
  supervisor releases its copies only after the group drains, and a
  restarted supervisor recognises a still-held slot as held (no
  best-effort release, no different slot taken). Only the supervisor's
  own dispatcher is stopped to free capacity (`dispatch_stop`, kept
  stopped while awaiting a slot, resumed with `dispatch_start` on fresh
  heartbeat, explicit pause, failed launch or successful handoff; backed
  off without stop/start churn). Contributors, watchers and the user's
  own processes are never signalled.
- **Pid identity.** A pid counts as the fallback only if its cmdline carries
  both the opencode and model markers, its state is not zombie/dead, and its
  process start time matches the lease. Reused, zombie and unrelated pids are
  ignored and never signalled; full cmdlines are never printed or stored.
- **Safe boundary.** Stopping the role needs more than a clean tree: the
  tree must be clean (no `status --porcelain` output, no `MERGE_HEAD`) AND
  the `foreground-action.lock` AND the `watch.lock` must be HELD (EX) across
  the signal, the group drain and the lease update -- never probed and
  released. Acquisition is nonblocking per poll while the lease lock is
  held (no deadlock: holders keep progressing and the supervisor retries
  next poll); on success both locks stay held through termination, so no
  new action or integration can start mid-kill. Otherwise the supervisor
  reports `waiting_for_safe_boundary_<reason>` (or
  `descendants_remain_<n>_slot_held` / `descendants_remain_fail_closed`)
  and retries. A watch-busy wait writes a supervisor-owned
  `coordinator-pause.json` to request a watcher safe boundary and removes
  only its own file afterwards; foreign pause files are never touched.
  Only the fallback's own process group is ever signalled, and the
  slot/role release happens only after `group_members(pgid)` is empty
  (zombies excluded, kernel `/proc` scan); an undrained group fails
  closed with the lease and locks kept instead of killing anything
  outside its own tree.
- **Pause (user only).** `<control>/pool-paused.json` is the explicit USER
  pause: it prevents any takeover, stops a live role at the next safe
  boundary, and exits an idle supervisor (`paused_no_takeover`).
  `<control>/coordinator-pause.json` is INTERNAL and transient (watcher
  registration or the supervisor's own safe-boundary request): it never
  blocks takeover, never stops the role, and never exits the supervisor.
  The supervisor's own request carries `owner: failover-<pid>` plus a
  `requested` timestamp; startup, every poll, pause exit and budget exit
  clean a leftover supervisor-owned marker whose pid is dead or whose age
  exceeds 600 s. Foreign registration markers are never touched and never
  pause coverage.
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
  (recognising a still-held slot/role as externally held, re-holding only
  a free recorded slot from a pre-inheritance lease with a fresh guardian)
  and never starts a duplicate or a different slot while the old group
  lives. The supervisor itself is exclusive via `failover-supervisor.lock`.
  The lease carries `guardian_pid` alongside `model_pid`/`model_start_time`/
  `slot`/`epoch`; status carries `dispatcher_held`.
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
  and the held-lock mutation boundary, documented above; this tool claims no
  usage-API detection.
- The tool cannot see work that never reaches the lease, nor distinguish a
  slow integration from a stuck one below the poll granularity.
- A descendant that leaves its process group (`setsid`/new session) is no
  longer a group member the guardian waits for; ordinary tool children keep
  the group id. Slots are kernel flock files: a holder killed with SIGKILL
  releases only its own copies, and the surviving inherited copies keep the
  lock, which is exactly the tested property.
- Registry changes (new pause files, renamed locks, new coordinator
  actions) need an owned follow-up; the supervisor must not guess.
