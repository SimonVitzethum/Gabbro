# MUSE-REPORT-621: independent review of candidate 620 (coordinator failover)

## Scope and method

Review-only lane. I own only this report; no source, doc or control file was
touched. The exact candidate is the SNAPSHOT pinned commit
`7d7c5e4d755e91b86dacf16721e83e2a0762367f` (author 620, 4 new files, no other
tree paths). Its commit object is not fetchable from this clone, so I verified
content identity instead of the hash: `PATCH.diff` applies cleanly to the pinned
base `435604ad` (`git apply --check`: clean) and the four applied files are
byte-identical (`cmp`) to `.tmp/review/author-620/` snapshot copies. Content
reviewed is therefore exactly the candidate content; only the commit-hash
binding itself is taken from `SNAPSHOT.json`.

Files reviewed (all new, ~1340 lines total):

- `instrumente/coordinator-failover.py` (739 lines)
- `instrumente/tests/test_coordinator_failover.py` (468 lines, 16 tests)
- `dokumente/x86/COORDINATOR-FAILOVER.md`
- `MUSE-REPORT-620.md`

## Verification (independently reproduced)

- `python3 -m py_compile` on both Python files: OK.
- Full suite from a scratch copy (fixtures inside scratch, no live controls,
  no network, no provider): **16 tests, 0 failures, 0 errors in 16.6 s**.
  `git status` clean afterwards; scratch removed.
- `grep` over both files: no `socket`/`urllib`/`requests`, no `shell=True` /
  `os.system`, no `push`, no `pass_fds`, no password/token/key reads, no
  cmdline printing or storage. Git use is read-only `status --porcelain` plus
  a `MERGE_HEAD` existence check. Coordinator contact is subprocess argv only
  (`dispatch_stop` / `dispatch_start`), asserted literally in the fake log.
- The `/proc` stat index was checked against `proc(5)` by hand: after
  `rsplit(")",1)[1].split()`, index 19 is `starttime` (state at 0, 18 numeric
  fields between). The fixture layout matches, AND the real-`/proc` paths are
  exercised too (heartbeat-handback test and all supervise tests use live pids
  via `get_start_time`/`identify_model` on `/proc`), so the fixtures do not
  merely mirror an implementation assumption.

## Review answers (task questions plus coordinator notes)

- Freshness check to spawn: PASS. The whole takeover sequence
  (`dispatch_stop`, role-lock, `reserve_slot`, fresh lease re-read and
  `should_takeover` re-evaluation, `Popen`, `update_lease_locked`,
  `dispatch_start`) runs inside one held `orchestrator-lease.lock`
  (`run_supervise`, guard acquired before the loop-body work, released only
  after the post-launch lease re-read). Foreground `heartbeat` takes the same
  lock blocking, so a returning heartbeat cannot slip between recheck and the
  owner write; after release it sees `owner: muse` with a live pid and takes
  the handback path (exit 2, writes `return-to-codex.json`) instead of
  overwriting. Tested for the steady states; the exact interleave is argued
  from the lock scope, which I read line by line.
- Heartbeat never overwrites a live Muse owner: PASS, tested.
- One supervisor / one role: PASS (`failover-supervisor.lock` + unit test),
  role epoch carried in lease and child env for the mutation gate. At most 15
  models: PASS, same `locks/go-contributor-01..15` flock names, `SLOT_COUNT=15`
  asserted by test, fallback slot probe-conflict asserted with a real lock.
- PID identity: PASS. pid + starttime + both cmdline markers; zombies (`Z`),
  dead (`X`), unknown states, reused pids and unrelated binaries all rejected
  and never signalled; full cmdlines never logged or stored. No wall-clock-only
  assertion anywhere.
- Pause and user-process preservation: PASS and tested (pause blocks takeover,
  pause stops the role at a safe boundary, decoy `sleep` survives turn expiry).
  Private session DB under control dir, SSD scratch under pool dir, no `/tmp`,
  no config/credential reads: PASS.
- Bounded turns / no restart storm: PASS and tested (`--turn-seconds` > 7200
  rejected with exit 3 in both actions; exponential backoff 5 s doubling capped
  at 300 s; launch-storm test bounds `dispatch_stop` count and elapsed time).
- Safe handback: PASS and tested (dirty tree delays the stop with
  `waiting_for_safe_boundary_*`; clean tree alone is correctly NOT enough).
- Crash/restart adoption without duplicate: PASS and tested.

## CUTS (precise, accepted as documented limitations, none a merge blocker)

1. Slot lock is NOT inherited by the fallback (no `pass_fds` on the `Popen`).
   If the supervisor process exits, its flock releases while the fallback may
   still run; a restart re-holds the recorded slot only if still free. The
   author discloses this as best-effort in report and doc; I confirm the code
   matches the disclosure. A `pass_fds`-style fix would still depend on the
   model runner preserving the fd across exec, so it is not an obviously safe
   three-line repair; follow-up owns the design.
2. Watch/action locks are probed nonblocking and released at once, NOT held
   through termination, so a new action can in principle begin between the
   probe and the signal. This is exactly what the owner task prescribed
   ("watch.lock nonblocking"), the kill scope is limited to the fallback's own
   process group, and the window is small; residual TOCTOU stays a CUT.
3. `slot_exhausted` and `role_held_by_other` set no backoff, so with all 15
   slots full the loop repeats `dispatch_stop`/`dispatch_start` every poll
   interval. Dispatcher restoration is present on every path (verified), but
   the churn has no backoff. Minor; recommended follow-up, not a blocker.
4. Strays of the fallback's group get SIGKILL but the slot/role locks release
   without confirming the strays are gone; "children gone before slot release"
   holds for the direct child only. Minor CUT.
5. Pause with no live fallback exits the supervisor (`paused_no_takeover`,
   exit 0), so failover coverage ends until the root wrapper re-arms it. The
   doc does not state the exit explicitly. Behaviour is safe (fail closed, no
   takeover while paused); doc follow-up at most.
6. The lease lock is held across coordinator subprocess calls (up to 120 s
   timeout each) and the model spawn; a foreground heartbeat during that window
   blocks rather than failing, and is handled correctly on release. Availability
   note only.
7. No test forces the `fresh_heartbeat_before_launch` interleave or a
   mid-`Popen` heartbeat; those paths are covered by lock-scope argument, not
   by a test. Acceptable given real-lock integration tests elsewhere.

## Hard-reject criteria (all clear)

No unbounded spawning, no direct or unguarded `git push`, no optimistic kill of
busy git/test children (guarded by the safe boundary; residual is CUT 2), no
wall-clock-only PID assertions, no faked model counts, no mocked tests
bypassing kernel-lock properties (flock, Popen groups, `/proc` identity are all
real in the tests).

## Disagreements with the task

None. The turn bound, the cooperative return, and the explicit non-detection of
usage-API state are implemented as specified and disclosed where limited.

## Verdict

- Exact CANDIDATE: 620 `7d7c5e4d755e91b86dacf16721e83e2a0762367f`
  (content verified byte-identical via base + `PATCH.diff`; hash binding from
  `SNAPSHOT.json`)
- VERDICT: ACCEPT

Report-only commit; no root controls touched, no provider called, no lane
edits. Tools-only review: no Lean build claimed or needed (no `grammatik/`
contact), no `cargo` runs (no Rust contact).
