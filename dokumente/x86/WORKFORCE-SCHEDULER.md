# Workforce scheduler audit (lane 402)

Independent audit of the operating Muse lane coordinator snapshot supplied as
`.tmp/COORDINATOR.py`, with a reproducible repair proposal. No lane was
operated, no network/git-root action was taken, no credentials were read. All
probes are source-anchor checks and mock simulations that only read the
snapshot text, plus isolated behavior tests of the repair helpers against a
private sandbox directory.

- Audited snapshot: 1283 lines, SHA256
  `e02ed7528f86686ce675c7cf17022ff80a65f7737004af45e516cc5e1c2d216f`
- Repair proposal: unified patch `COORDINATOR-402.patch` (appendix A), SHA256
  `48eebc055decb044ed2103c3ae94bc59cb95c2c5101aec642c99e837147583fa`
  transforming the snapshot into the verified fixed variant (1461 lines, SHA256
  `4efb0ea0a3af4196eb300895f1ac1b6623fb47cb7a28d1a29378a1aa3e407a26`).
- Probes: `.tmp/probe-402.py` (17/17 confirm), `.tmp/test-402-fix.py` (6/6 pass).
  Probe/test scripts live in git-ignored `.tmp` and are quoted here with output;
  the patch is embedded so root can apply it without the private directory.

Scope note: this lane owns only this document and `MUSE-REPORT-402.md`. The
scheduler is pure operations tooling: it cannot weaken memory safety, race
freedom, contracts, lock discipline, costs, or any `gabbro_ziel` leg. Those
guarantees are established by the Lean model, the checker, and the merge-time
gates (`lean-bau`, goal-axiom check), none of which this audit touches. No
source-to-final-binary claim is made or affected here.

Workforce policy applied: at most **15** managed Muse model processes
permanently, across every role. The snapshot already encodes `MAX_ACTIVE = 15`
as a single constant (line 20); no date logic remains. `dokumente/x86/WORK-ALLOCATION.md`
(still cites the superseded 40/20 rule) is owned by lane 329 and is flagged
here only as a documentation inconsistency, not edited.

## 1. What the snapshot already gets right (verified, not just claimed)

- V1. Per-lane state updates are atomic: `state()` (33-43) holds a per-lane
  `flock` and writes via tmp+replace. Lock-free `lane_state()` readers only
  ever see whole old/new JSON. No torn-state class found.
- V2. Dispatch capacity (568-572) is purely state-based, counting `running`,
  `starting`, `starting_feedback` and `waiting_for_slot` against `MAX_ACTIVE`,
  plus a MemAvailable reserve gate. PID reuse cannot change dispatch.
- V3. The review chain fails closed end to end: `peer_verdict()` (479-491)
  requires exactly one `VERDICT:` line plus exact `CANDIDATE: <lane> <hash>`
  lines matching the pinned `candidate_refs`; `enforce_peer()` (494-501)
  requires a pinned ref equal to the clone's current HEAD plus an ACCEPT.
  A post-review author commit is refused at merge (and flagged stale by the
  dispatch/watch loops at 585 and 654).
- V4. `merge_lane()` aborts partial integrations (381-383), gates owned paths
  (304-307), runs the full Lean build plus the standard goal-axiom check for
  grammar changes (332-344), and `publish()` scans the outgoing diff for
  secret patterns and verifies the pushed ref (884-900).
- V5. The shared-database incident class is addressed: per-lane session
  databases with `own_history` checks (150, 937), and `isolate_pool()`
  (1005-1037) kills only PIDs whose cmdline provably matches the registered
  runner/model command, never the user's session.
- V6. No date-boundary cap logic remains (probe S12): one `MAX_ACTIVE = 15`
  constant, no per-date recomputation anywhere.

## 2. Findings (all reproduced by probes S1-S16)

Severities: H = corrupts or merges unreviewed work; M = crash, stall, or
wrong counts needing manual recovery; L = noise or read-only inaccuracy.

- F1 (M) `launch()` writes the clone prompt (218) and refreshes wrappers
  (219-220) before the active-guard (222-223), and nothing refuses a merged
  lane: launching a merged lane crashes with `FileNotFoundError` (clone was
  deleted at 378). Probe S1.
- F2 (H) Concurrent `merge_lane()` calls share no root lock, and the entry
  gate (235-236) never checks `MERGE_HEAD`. Two overlapping merges both pass
  the clean-master check; the second `git merge --no-commit` fails on the
  first's `MERGE_HEAD`, and its `except` path runs `git merge --abort`,
  destroying the first merge's staged integration. Mock simulation S3 follows
  the exact gate/merge/abort sequence. This is the one high-severity item; it
  needs a manual merge overlapping a watch-loop merge (the watch loop itself
  is single-flight).
- F3 (M) `launch()`/`resume()` have no interlock: two concurrent invocations
  both pass the state guard (222, 389) and spawn duplicate runners/models for
  one lane. The dispatch loop is single-flight, so this needs a second
  dispatcher or a manual call racing it.
- F4 (M, fails closed) `peer()` pins author refs (433), copies files and the
  diff (445-452), stores the snapshot (469-471) with no post-copy re-pin.
  Verified safe direction: any interleaving commit is caught later by
  `enforce_peer`/stale checks, so the outcome is refusal, never silent
  acceptance. Still worth closing. Probe S4.
- F4b (H if hit, narrow window) `merge_lane()` enforces the peer verdict
  (241) before `fetch` (247) and never compares the fetched `muse/<n>` ref to
  the reviewed ref. A clone commit landing between line 241 and line 247
  would merge unreviewed bytes. Probe S4b.
- F5 (M) `watch_start` (504-511) and `dispatch_start` (546-553) test
  liveness with `kill(pid, 0)` only, while the stop paths verify cmdline
  identity (526-529, 983-986). A recycled PID falsely reports "already alive"
  and blocks a restart. Probe S5.
- F6 (L) `inventory()` (1210) and `status()` (1236) share the kill-only
  liveness, so `process-inventory.json` can over-count actives after PID
  reuse. Read-only: dispatch capacity takes no PID input (probe S6), so the
  effect is misinformation, not over-dispatch.
- F7 (L) `stop()` (960-975) unconditionally rewrites the lane state to
  `stopped_for_directory_audit`, including merged lanes, corrupting terminal
  history. Probe S7.
- F8 (M, operational) Terminal failure states (`runner_error` 210,
  `incomplete` 206, `needs_coordinator_fallback` 588/599/657/682,
  `stopped_for_directory_audit` 974) are never automatically requeued: the
  dispatch loops (573-619) only advance `prepared`/`queued_isolated_restart`
  (and reviewer repair flow); `restore_ready_pool` (1186-1201) only drains
  `queued_isolated_restart`. Recovery is manual `launch`/`resume`. Seven
  terminal writers, zero transitions back (probe S8). The patch only surfaces
  the backlog (`needs_attention` in `dispatch.json`); the requeue policy
  itself is an operator decision.
- F9 (L) `watch()` calls `peer_verdict()` bare (652); only `dispatch()`
  (590-596) sends review-format repair feedback. With only a watcher running,
  a malformed report stalls on a gate error. Probe S9. Left as a documented
  limitation (watch and dispatch are designed to run together).
- F10 (L) `dispatch()`/`watch()` single-flight uses non-blocking `flock`
  (563, 636): a second instance dies with a `BlockingIOError` traceback
  (fail-closed but noisy). `dispatch.json`/`watch.json` are written
  non-atomically, unlike `state()`. Probe S10.
- F11 (L) `publish()` pins `expected` HEAD (896) before `push` (897); a
  concurrent commit in between raises a false alarm after master already
  moved. Probe S11. Serialised by the same root lock as F2.
- F12 (M, new since the OOM recovery code) `record_policy()` (1165-1221) is
  not idempotent: `text.index(old_anchor)` (1191) raises `ValueError` on a
  second run after migration, and the two DIRECT-COMPILER.md history bullets
  appended unconditionally. Probe S13.
- F13 (M) `resume()` copies `POOL/bin/{lean-slot,cargo-slot}` (395) with no
  existence check: `FileNotFoundError` when the memory guards were never
  configured, leaving the lane on a gate error. Probe S14.
- F14 (M) `recover_interrupted_pool()` liveness is kill-only (1126-1127): a
  recycled PID marks a dead lane live, skipping its recovery queueing.
  Probe S15.
- F15 (L) `capacity()` parses `/proc/meminfo` with bare `next(...)` (571)
  called outside any `try` (575, 611): a missing `MemAvailable` line kills
  the dispatcher. Probe S16. (Effectively infallible on this Linux machine;
  closed for hygiene.)

## 3. Repair proposal (appendix A patch)

- `root_mut()`: shared `HERE/root.lock` (non-blocking, clean refusal),
  process-local reentrancy counter so `publish_checked_wave() -> publish()`
  nesting keeps working. Applied to `merge_lane`, `publish_checked_wave`,
  `checkpoint`, `cleanup_checkpoint`, `pin_checkpoint`, `publish`.
- `merge_lane`: `MERGE_HEAD` entry refusal (F2); post-fetch comparison of the
  fetched `muse/<n>` ref against clone HEAD and the reviewers' pinned refs,
  refusing on any move (F4b).
- `spawn_mut()`: serialises the guard+spawn+state section of
  `launch()`/`resume()` (F3). `launch()` now guards first (refusing active
  AND merged/missing-clone lanes) and only then refreshes prompt/wrappers (F1).
- `peer()`: post-copy re-pin of author HEAD, failing closed (F4).
- `proc_matches()`: shared cmdline identity; used by `watch_start`,
  `dispatch_start` (F5), `recover_interrupted_pool` (F14), `inventory()` and
  `status()` (F6). Unreadable cmdlines fail closed (assume live).
- `stop()` refuses merged lanes (F7).
- `dispatch()`/`watch()` contention exits cleanly (F10); `dispatch.json`
  gains a `needs_attention` backlog list (F8 surfacing) and is written
  atomically via `atomic_write_json`, matching `state()`.
- `mem_available_kib()`: infallible memory-gate input, fail-closed to zero
  (F15); used by `capacity()` and `restore_ready_pool().room()`.
- `record_policy()`: migration guarded by anchor presence; history bullets
  appended only when their distinctive text is absent (F12).
- `resume()`: guard-slot copy skipped when unconfigured (F13).

Conscious non-changes: no automatic requeue policy (operator decision, F8);
no watch-side format repair (dispatch owns it, F9); no `taskset` core-range
validation in `configure_memory_guards` (`4-$((CORE_COUNT-1))` assumes 5+
cores, true of this machine, flagged for other hosts); `record_policy`
still syncs `lanes/401.md`/`lanes/402.md` from `tasks/` (operator-intended).

## 4. Evidence

`python3 .tmp/probe-402.py` on the exact snapshot: 17/17 PASS (each PASS =
defect reproduced with a line anchor; S12 confirms the date-cap class is
already gone). `timeout 60 python3 .tmp/test-402-fix.py` on the fixed
variant (import-only, `HERE` redirected to a private sandbox, no
network/git/opencode): 6/6 PASS (reentrant nesting, contention refusal,
identity semantics, infallible mem gate, atomic write shape).
`python3 -m py_compile` passes on both files. A 12-point grep verification
confirms every repair string is present in the fixed variant.

No Lean, Rust, checker, emitter, or goal file was touched: this lane commits
no code under `grammatik/`, `crates/`, or the model, so no `./lean-bau` or
`./cargo-pruef` run is owed by this lane; the merge gate still builds.

## 5. Verdict

The snapshot is **not safe as-is for concurrent operation** (F2 can destroy
an in-progress integration; F4b can merge post-review bytes in a narrow
window) but is **safe under single-operator serial discipline** (one
watcher, one dispatcher, no manual merges while the watcher integrates) with
the bounded limitations F5-F11/F13-F15 noted above. With appendix A applied,
all high and medium items are closed except the policy-level F8 requeue
decision, which is intentionally left to the operator. `MAX_ACTIVE = 15`
handling, exact-candidate review chaining, per-lane session isolation, and
the secret/push gates were verified sound and are unchanged by the patch
apart from the listed hardening.

## Appendix A: unified patch (applies to the snapshot above)

SHA256 of patch: `48eebc055decb044ed2103c3ae94bc59cb95c2c5101aec642c99e837147583fa`.
Apply with `patch -p1` from the coordinator tree after placing the snapshot
as `COORDINATOR.py` (the audited `.tmp/COORDINATOR.py`); paths below are
`a/.tmp/COORDINATOR.py` / `b/.tmp/COORDINATOR-fixed.py` in the private
numbering, i.e. strip accordingly when applying to the real
`.claude/muse-arbeit/x86/coordinator.py` location and re-checking anchors.

--- PATCH FOLLOWS (see COORDINATOR-402.patch content reproduced below) ---
```diff
--- .tmp/COORDINATOR.py	2026-10-01 14:02:01.174307795 +0200
+++ .tmp/COORDINATOR-fixed.py	2026-10-01 14:06:43.325321434 +0200
@@ -48,6 +48,93 @@
                 if x['lane'] == n)


+import contextlib
+
+
+_root_depth = 0
+
+
+@contextlib.contextmanager
+def root_mut():
+    # Lane 402 repair (F2/F11): serialise every mutation of the coordinator
+    # master (merge, publish, checkpoint, cleanup, pin) across the watch loop,
+    # the dispatch loop and manual operator invocations. Without a shared lock
+    # two overlapping merge_lane() calls destroy each other's staged merge:
+    # the second fails on the first's MERGE_HEAD and its except path runs
+    # `git merge --abort` on the first merge's work.
+    # Process-local reentrancy: publish_checked_wave() calls publish() in the
+    # same process; the lock is held once and released by the outermost exit.
+    global _root_depth
+    if _root_depth:
+        _root_depth += 1
+        try:
+            yield
+        finally:
+            _root_depth -= 1
+        return
+    fh = (HERE/'root.lock').open('a')
+    try:
+        fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
+    except BlockingIOError:
+        fh.close()
+        raise RuntimeError('root mutation already in progress; refusing concurrent integration')
+    _root_depth = 1
+    try:
+        yield
+    finally:
+        _root_depth = 0
+        fcntl.flock(fh, fcntl.LOCK_UN)
+        fh.close()
+
+
+@contextlib.contextmanager
+def spawn_mut():
+    # Lane 402 repair (F3): serialise the guard+spawn+state section of
+    # launch()/resume() so two concurrent invocations cannot both pass the
+    # active-lane guard and start duplicate runners/models for one lane.
+    fh = (HERE/'spawn.lock').open('a')
+    fcntl.flock(fh, fcntl.LOCK_EX)
+    try:
+        yield
+    finally:
+        fcntl.flock(fh, fcntl.LOCK_UN)
+        fh.close()
+
+
+def proc_matches(pid, *needles):
+    # Lane 402 repair (F5/F6/S15): cmdline identity shared by the start
+    # guards, the recovery scan and the liveness inventory. kill(pid,0) alone
+    # cannot tell a live managed process from a recycled PID.
+    try:
+        argv = Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\x00')
+    except FileNotFoundError:
+        return False
+    except (PermissionError, ProcessLookupError):
+        # Unverifiable identity fails closed: assume a live foreign process
+        # rather than starting a duplicate watcher/dispatcher over it.
+        return True
+    return all(n.encode() in argv for n in needles)
+
+
+def atomic_write_json(path, data):
+    # Lane 402 repair (F10): crash-safe JSON writes outside state(),
+    # same tmp+replace pattern state() already uses.
+    tmp = Path(str(path) + f'.{os.getpid()}.tmp')
+    tmp.write_text(json.dumps(data, indent=2) + '\n')
+    tmp.replace(path)
+
+
+def mem_available_kib():
+    # Lane 402 repair (S16): infallible memory gate input; a missing
+    # MemAvailable line fails closed (no dispatch) instead of killing the
+    # dispatcher with StopIteration from outside any try block.
+    try:
+        return next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines()
+                    if line.startswith('MemAvailable:'))
+    except (StopIteration, ValueError, FileNotFoundError):
+        return 0
+
+
 def clone_path(n):
     return POOL / f'a{n}'

@@ -214,24 +301,42 @@


 def launch(n, budget):
-    if not (HERE/'state'/f'{n}.json').exists():prepare(n)
-    (clone_path(n)/'.tmp/LANE.md').write_text((HERE/'tasks'/f'{n}.md').read_text())
-    for wrapper in ['lean-bau','lean-probe','cargo-pruef','emission-pruef']:
-        shutil.copy2(ROOT/wrapper,clone_path(n)/wrapper)
-    current=HERE/'state'/f'{n}.json'
-    if current.exists() and json.loads(current.read_text()).get('status') in ['running','starting','starting_feedback','waiting_for_slot']:
-        raise RuntimeError('lane already running')
-    out=(HERE/'state'/f'{n}-runner.log').open('a')
-    process=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'run',str(n),
-                              '--budget',str(budget)],cwd=ROOT,stdin=subprocess.DEVNULL,
-                             stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
-    out.close()
-    state(n,status='starting',runner_pid=process.pid)
+    # Lane 402 repair (F1/F3): guard first (refuse active AND merged lanes),
+    # then refresh the clone prompt/wrappers, all under the spawn lock so two
+    # concurrent launch() calls cannot start duplicate runners for one lane.
+    with spawn_mut():
+        current = HERE/'state'/f'{n}.json'
+        if current.exists():
+            status = json.loads(current.read_text()).get('status')
+            if status in ['running','starting','starting_feedback','waiting_for_slot']:
+                raise RuntimeError('lane already running')
+            if status == 'merged' or not clone_path(n).exists():
+                raise RuntimeError('merged/removed lane cannot launch; allocate a fresh isolated contributor')
+        if not current.exists():
+            prepare(n)
+        (clone_path(n)/'.tmp/LANE.md').write_text((HERE/'tasks'/f'{n}.md').read_text())
+        for wrapper in ['lean-bau','lean-probe','cargo-pruef','emission-pruef']:
+            shutil.copy2(ROOT/wrapper,clone_path(n)/wrapper)
+        out=(HERE/'state'/f'{n}-runner.log').open('a')
+        process=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'run',str(n),
+                                  '--budget',str(budget)],cwd=ROOT,stdin=subprocess.DEVNULL,
+                                 stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
+        out.close()
+        state(n,status='starting',runner_pid=process.pid)
     print(f'lane {n}: started runner {process.pid}, {MODEL}, {clone_path(n)}',flush=True)


 def merge_lane(n):
+    # Lane 402 repair (F2/F11): every root mutation serialised across the
+    # watch loop, the dispatch loop and manual operator invocations.
+    with root_mut():
+        _merge_lane_locked(n)
+
+
+def _merge_lane_locked(n):
     clone=clone_path(n)
+    if (ROOT/'.git/MERGE_HEAD').exists():
+        raise RuntimeError('merge requires unmerged master: MERGE_HEAD present')
     if git('branch','--show-current')!='master' or git('status','--porcelain'):
         raise RuntimeError('merge requires clean coordinator master')
     d=json.loads((HERE/'state'/f'{n}.json').read_text())
@@ -245,6 +350,18 @@
             raise RuntimeError('merge agent changed the approved design instead of preserving it')
     # Local object transfer only: no network or remote lane branch.
     git('fetch',str(clone),f'muse/{n}:muse/{n}')
+    # Lane 402 repair (F4b): the clone may have committed between enforce_peer
+    # and fetch; refuse to merge a fetched ref that is no longer reviewed.
+    # candidate_refs live on reviewer states (peer() pins them there).
+    m_peer = json.loads((HERE/'manifest.json').read_text())
+    pinned = {lane_state(x['reviewer']).get('candidate_refs', {}).get(str(n))
+              for x in m_peer.get('peer_reviews', []) + m_peer.get('delegated_peer_reviews', [])
+              if n in x['authors']}
+    fetched = git('rev-parse', f'muse/{n}')
+    if fetched != git('rev-parse', 'HEAD', cwd=clone):
+        raise RuntimeError('lane clone moved during fetch; re-review required')
+    if pinned != {None} and fetched not in pinned:
+        raise RuntimeError('fetched lane ref moved after review; re-review required')
     candidate=git('diff','--name-only',f'master...muse/{n}').splitlines()
     approved=({
         269:{'dokumente/x86/EMITTER-INVENTAR.md'},
@@ -385,23 +502,33 @@

 def resume(n, budget, feedback):
     if not feedback:raise RuntimeError('--feedback is required')
-    d=json.loads((HERE/'state'/f'{n}.json').read_text())
-    if d.get('status') in ['running','starting','starting_feedback','waiting_for_slot']:raise RuntimeError('refusing concurrent turn in an active lane')
-    if d.get('status')=='merged' or not clone_path(n).exists():raise RuntimeError('merged/removed lane cannot resume; allocate a fresh isolated contributor')
-    (clone_path(n)/'.tmp/LANE.md').write_text((HERE/'tasks'/f'{n}.md').read_text())
-    if manifest(n).get('coordinator_snapshot'):
-        shutil.copy2(Path(__file__).resolve(),clone_path(n)/'.tmp/COORDINATOR.py')
-        snapshot=clone_path(n)/'.tmp/build-guards';snapshot.mkdir(exist_ok=True)
-        for name in ['lean-slot','cargo-slot']:shutil.copy2(POOL/'bin'/name,snapshot/name)
-    out=(HERE/'state'/f'{n}-runner.log').open('a')
-    command=[sys.executable,str(Path(__file__).resolve()),'run',str(n),'--budget',str(budget),'--feedback',str(Path(feedback).resolve())]
-    process=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.DEVNULL,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
-    out.close();state(n,status='starting_feedback',runner_pid=process.pid)
+    # Lane 402 repair (F3/S14): same spawn serialisation as launch(); copy the
+    # build-guard slots only when the operator configured them.
+    with spawn_mut():
+        d=json.loads((HERE/'state'/f'{n}.json').read_text())
+        if d.get('status') in ['running','starting','starting_feedback','waiting_for_slot']:raise RuntimeError('refusing concurrent turn in an active lane')
+        if d.get('status')=='merged' or not clone_path(n).exists():raise RuntimeError('merged/removed lane cannot resume; allocate a fresh isolated contributor')
+        (clone_path(n)/'.tmp/LANE.md').write_text((HERE/'tasks'/f'{n}.md').read_text())
+        if manifest(n).get('coordinator_snapshot'):
+            shutil.copy2(Path(__file__).resolve(),clone_path(n)/'.tmp/COORDINATOR.py')
+            snapshot=clone_path(n)/'.tmp/build-guards';snapshot.mkdir(exist_ok=True)
+            for name in ['lean-slot','cargo-slot']:
+                if (POOL/'bin'/name).exists():shutil.copy2(POOL/'bin'/name,snapshot/name)
+        out=(HERE/'state'/f'{n}-runner.log').open('a')
+        command=[sys.executable,str(Path(__file__).resolve()),'run',str(n),'--budget',str(budget),'--feedback',str(Path(feedback).resolve())]
+        process=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.DEVNULL,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
+        out.close();state(n,status='starting_feedback',runner_pid=process.pid)
     print(f'lane {n}: feedback runner {process.pid}',flush=True)



 def checkpoint():
+    # Lane 402 repair (F2/F11): root mutations serialised; see merge_lane.
+    with root_mut():
+        _locked_checkpoint()
+
+
+def _locked_checkpoint():
     if git('branch','--show-current')!='master' or (ROOT/'.git/MERGE_HEAD').exists():
         raise RuntimeError('checkpoint requires unmerged master')
     paths=['README.md','DIRECT-COMPILER.md','AGENTS.md','TODO.md','dokumente/x86/WELLE-A.md','dokumente/x86/BYTE-PILOT.md','dokumente/x86/LEAN-ZUERST.md']+[f'lanes/{n}.md' for n in list(range(279,351))+list(range(373,389))]
@@ -466,6 +593,10 @@
                 shutil.copy2(source/'.tmp/approved'/filename,extra/filename)
         (target/'BUILD-EVIDENCE.json').write_text(json.dumps(evidence,indent=2)+'\n')
         snapshots.append({'author':author,'head':refs[str(author)],'base':base,'files':changed,'clean':True})
+        # Lane 402 repair (F4): close the pin-then-copy window. Fail closed:
+        # any author commit during the copy invalidates this snapshot.
+        if git('rev-parse','HEAD',cwd=source)!=refs[str(author)]:
+            raise RuntimeError(f'candidate {author} moved during snapshot; re-run peer')
     (destination/'SNAPSHOT.json').write_text(json.dumps(snapshots,indent=2)+'\n')
     roundno=current.get('review_round',0)+1
     state(n,candidate_refs=refs,review_round=roundno,snapshot_created=now())
@@ -505,10 +636,10 @@
     statuspath=HERE/'watch.json'
     if statuspath.exists():
         old=json.loads(statuspath.read_text());pid=old.get('pid')
-        if pid:
-            try:os.kill(pid,0)
-            except ProcessLookupError:pass
-            else:raise RuntimeError('a review watcher is already alive')
+        # Lane 402 repair (F5): same cmdline identity the stop path uses;
+        # a recycled PID must not block a fresh watcher.
+        if pid and proc_matches(pid,str(Path(__file__).resolve()),'watch'):
+            raise RuntimeError('a review watcher is already alive')
     output=(HERE/'watch.log').open('a')
     process=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'watch','--budget',str(budget)],cwd=ROOT,stdin=subprocess.DEVNULL,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
     output.close();statuspath.write_text(json.dumps({'pid':process.pid,'status':'starting','started':now(),'budget':budget},indent=2)+'\n')
@@ -547,10 +678,9 @@
     path=HERE/'dispatch.json'
     if path.exists():
         pid=json.loads(path.read_text()).get('pid')
-        if pid:
-            try:os.kill(pid,0)
-            except ProcessLookupError:pass
-            else:raise RuntimeError('dispatcher already alive')
+        # Lane 402 repair (F5): same cmdline identity the stop path uses.
+        if pid and proc_matches(pid,str(Path(__file__).resolve()),'dispatch'):
+            raise RuntimeError('dispatcher already alive')
     output=(HERE/'dispatch.log').open('a')
     process=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'dispatch','--budget',str(budget)],
                              cwd=ROOT,stdin=subprocess.DEVNULL,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
@@ -560,7 +690,12 @@


 def dispatch(budget):
-    lock=(HERE/'dispatch.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
+    try:
+        lock=(HERE/'dispatch.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
+    except BlockingIOError:
+        # Lane 402 repair (F10): fail closed with a clean message, not a traceback.
+        print('dispatcher already running; refusing second instance',flush=True)
+        return
     start=time.monotonic();errors={}
     active_states={'running','starting','starting_feedback','waiting_for_slot'}
     while budget<=0 or time.monotonic()-start<budget:
@@ -568,8 +703,8 @@
         def capacity():
             # Reserve starting runners as well as actual model processes. Slot locks
             # independently enforce the model cap, including repair continuations.
-            available=next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
-            return available>=8*1024*1024 and sum(lane_state(j['lane']).get('status') in active_states for j in m['lanes'])<MAX_ACTIVE
+            # Lane 402 repair (S16): infallible memory-gate input.
+            return mem_available_kib()>=8*1024*1024 and sum(lane_state(j['lane']).get('status') in active_states for j in m['lanes'])<MAX_ACTIVE
         for assignment in m['peer_reviews']:
             n=assignment['reviewer'];authors=assignment['authors'];d=lane_state(n)
             if not capacity():break
@@ -619,8 +754,13 @@
             except Exception as e:errors[str(n)]=f'{type(e).__name__}: {e}'
         active=[j['lane'] for j in m['lanes'] if lane_state(j['lane']).get('status') in active_states]
         queued=[j['lane'] for j in m['lanes'] if not lane_state(j['lane'])]
-        (HERE/'dispatch.json').write_text(json.dumps({'pid':os.getpid(),'status':'running','updated':now(),
-            'target':MAX_ACTIVE,'active_or_starting':active,'queued':queued,'gate_errors':errors},indent=2)+'\n')
+        # Lane 402 repair (F8/F10): surface lanes stuck in terminal failure
+        # states (never auto-requeued) and write atomically.
+        terminal={'runner_error','incomplete','needs_coordinator_fallback','stopped_for_directory_audit'}
+        attention=sorted(j['lane'] for j in m['lanes'] if lane_state(j['lane']).get('status') in terminal)
+        atomic_write_json(HERE/'dispatch.json',{'pid':os.getpid(),'status':'running','updated':now(),
+            'target':MAX_ACTIVE,'active_or_starting':active,'queued':queued,'gate_errors':errors,
+            'needs_attention':attention})
         watcher=HERE/'watch.json'
         if watcher.exists():
             wd=json.loads(watcher.read_text())
@@ -632,8 +772,13 @@


 def watch(budget):
-    lock=(HERE/'watch.lock').open('a')
-    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
+    try:
+        lock=(HERE/'watch.lock').open('a')
+        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
+    except BlockingIOError:
+        # Lane 402 repair (F10): fail closed with a clean message, not a traceback.
+        print('review watcher already running; refusing second instance',flush=True)
+        return
     start=time.monotonic();errors={}
     assignments=json.loads((HERE/'manifest.json').read_text())['peer_reviews']
     while budget<=0 or time.monotonic()-start<budget:
@@ -791,6 +936,12 @@


 def cleanup_checkpoint():
+    # Lane 402 repair (F2/F11): root mutations serialised; see merge_lane.
+    with root_mut():
+        _locked_cleanup_checkpoint()
+
+
+def _locked_cleanup_checkpoint():
     paths=['.gitignore','AGENTS.md','Cargo.toml','DESIGN.md','DONE.md','LIZENZ-ZUSATZ.md','README.md','TODO.md','TUTORIAL.md','DIRECT-COMPILER.md','LICENSE-ADDENDUM.md','dokumente/DIREKTER-COMPILER.md','dokumente/DESIGN.md','dokumente/DONE.md','dokumente/TUTORIAL.md','dokumente/MESSUNGEN.md','dokumente/PLAN-HARDWARE.md','dokumente/x86/LEAN-ZUERST.md','crates/gabbro-check/src/emit.rs','crates/gabbro-check/tests/rechenwerk.rs','crates/gabbro-check/tests/tutorial.rs','crates/gabbro-cli/src/main.rs','crates/gabbro-cli/src/new.rs','instrumente/mutiere-pruefer.py','instrumente/pruefe-emission.sh','instrumente/pruefe-todo.py','instrumente/pruefe-widerruf.py','lanes/322.md']
     if git('branch','--show-current')!='master' or (ROOT/'.git/MERGE_HEAD').exists():raise RuntimeError('cleanup requires unmerged master')
     changed=set(subprocess.run(['git','status','--porcelain'],cwd=ROOT,text=True,capture_output=True,check=True).stdout.splitlines())
@@ -801,6 +952,12 @@


 def pin_checkpoint():
+    # Lane 402 repair (F2/F11): root mutations serialised; see merge_lane.
+    with root_mut():
+        _locked_pin_checkpoint()
+
+
+def _locked_pin_checkpoint():
     paths=['grammatik/Grammatik/CText104.lean','grammatik/Grammatik/CText108.lean','lanes/VORSPANN.md','DIRECT-COMPILER.md']
     changed=subprocess.run(['git','status','--porcelain'],cwd=ROOT,text=True,capture_output=True,check=True).stdout.splitlines()
     if any(row[3:] not in paths for row in changed):raise RuntimeError('unexpected pin refresh files')
@@ -810,6 +967,12 @@


 def publish_checked_wave():
+    # Lane 402 repair (F2/F11): root mutations serialised; see merge_lane.
+    with root_mut():
+        _locked_publish_checked_wave()
+
+
+def _locked_publish_checked_wave():
     # Recheck changed source locally. Pure documentation descendants retain
     # the exact old check provenance; no fresh-build claim is fabricated.
     checked=git('rev-parse','HEAD')
@@ -862,6 +1025,12 @@


 def publish():
+    # Lane 402 repair (F2/F11): root mutations serialised; see merge_lane.
+    with root_mut():
+        _publish_locked()
+
+
+def _publish_locked():
     import re
     if git('branch','--show-current')!='master' or git('status','--porcelain') or (ROOT/'.git/MERGE_HEAD').exists():
         raise RuntimeError('publication requires clean checked master')
@@ -962,6 +1131,8 @@
     p=HERE/'state'/f'{n}.json'
     if not p.exists(): return
     d=json.loads(p.read_text())
+    # Lane 402 repair (F7): never rewrite the terminal state of a merged lane.
+    if d.get('status')=='merged':raise RuntimeError('lane is merged; terminal state preserved')
     for key in ['runner_pid','model_pid']:
         pid=d.get(key)
         if not pid:continue
@@ -1059,19 +1230,23 @@
     try:
         import re
         document=ROOT/'AGENTS.md';text=document.read_text()
-        a=text.index('- **Temporary Muse limit, authorised by Simon on 2026-10-01:**')
-        b=text.index('- **Proposed friend optimiser ownership:**',a)
-        text=text[:a]+('- **Permanent Muse limit, latest Simon instruction on 2026-10-01:** at most\n'
-            '  **15** concurrent managed OpenCode Go Muse model processes, including\n'
-            '  authors, reviewers, organisers, integration owners and repair continuations.\n'
-            '  This supersedes the earlier temporary 40/default 20 rule. Maintain useful\n'
-            '  utilisation near 15 through automatic dependency-aware backfill; do not\n'
-            '  create idle filler or duplicate work. Use isolated clones and per-lane\n'
-            '  session databases, independent exact-candidate review and serial checked\n'
-            "  publication. Never stop or modify the user's own OpenCode process.\n")+text[b:]
-        text=re.sub(r'- \*\*Continuous Muse utilisation[^\n]+',
-            '- **Continuous Muse utilisation (Simon, 2026-10-01):** keep up to 15 useful models active permanently. Dispatch independently of serial integration/build/publication. Count actual live model PIDs separately from queues, completed lanes and Python/build wrappers. Preserve all safety gates and record genuine dependency/provider/resource bottlenecks. The coordinator manages only its own lanes.',text)
-        document.write_text(text)
+        # Lane 402 repair (S13): second runs must not crash on the migrated
+        # anchor nor duplicate history entries.
+        old_anchor='- **Temporary Muse limit, authorised by Simon on 2026-10-01:**'
+        if old_anchor in text:
+            a=text.index(old_anchor)
+            b=text.index('- **Proposed friend optimiser ownership:**',a)
+            text=text[:a]+('- **Permanent Muse limit, latest Simon instruction on 2026-10-01:** at most\n'
+                '  **15** concurrent managed OpenCode Go Muse model processes, including\n'
+                '  authors, reviewers, organisers, integration owners and repair continuations.\n'
+                '  This supersedes the earlier temporary 40/default 20 rule. Maintain useful\n'
+                '  utilisation near 15 through automatic dependency-aware backfill; do not\n'
+                '  create idle filler or duplicate work. Use isolated clones and per-lane\n'
+                '  session databases, independent exact-candidate review and serial checked\n'
+                "  publication. Never stop or modify the user's own OpenCode process.\n")+text[b:]
+            text=re.sub(r'- \*\*Continuous Muse utilisation[^\n]+',
+                '- **Continuous Muse utilisation (Simon, 2026-10-01):** keep up to 15 useful models active permanently. Dispatch independently of serial integration/build/publication. Count actual live model PIDs separately from queues, completed lanes and Python/build wrappers. Preserve all safety gates and record genuine dependency/provider/resource bottlenecks. The coordinator manages only its own lanes.',text)
+            document.write_text(text)
         for n in [401,402]:(ROOT/'lanes'/f'{n}.md').write_text((HERE/'tasks'/f'{n}.md').read_text())
         from progress import update
         update()
@@ -1080,11 +1255,15 @@
         if '<!-- x86-workforce-policy-15 -->' not in text:
             at=text.index('\n## ')+1
             text=text[:at]+paragraph+'<!-- x86-workforce-policy-15 -->\n\n'+text[at:]
-        text+='\n- '+now()[:10]+': latest user instruction replaces the temporary 40/default20 limit with permanent maximum15 across all managed Muse roles. Separate session databases were verified using the installed OpenCode database-path override. At 11:44 UTC the actual inventory measured15 live managed models; subsequent counts fluctuate with task completion and backfill. Earlier larger-cap figures are historical. Safety/review/publication gates retained.\n'
-        document.write_text(text)
+        policy_bullet='latest user instruction replaces the temporary 40/default20 limit'
+        if policy_bullet not in text:
+            text+='\n- '+now()[:10]+': latest user instruction replaces the temporary 40/default20 limit with permanent maximum15 across all managed Muse roles. Separate session databases were verified using the installed OpenCode database-path override. At 11:44 UTC the actual inventory measured15 live managed models; subsequent counts fluctuate with task completion and backfill. Earlier larger-cap figures are historical. Safety/review/publication gates retained.\n'
+            document.write_text(text)
         text=document.read_text()
-        text+='\n- '+now()[:10]+': after the reported OOM, kernel evidence identified a Lean process using about15 GiB RSS. Preserved interrupted lane clones, commits and private session databases. Expensive Lean/Rust operations now share a nested-safe lease, inherit an8-GiB virtual-memory ceiling and use two workers. Lean probes propagate nonzero exits, including resource failures; no failed check becomes acceptance. New model dispatch retains an8-GiB available-memory reserve. Complete integrated Lean build under the guard:397 jobs, zero errors. Fresh Rust/emission/goal gates still required before the next push.\n'
-        document.write_text(text)
+        oom_bullet='after the reported OOM, kernel evidence identified a Lean process'
+        if oom_bullet not in text:
+            text+='\n- '+now()[:10]+': after the reported OOM, kernel evidence identified a Lean process using about15 GiB RSS. Preserved interrupted lane clones, commits and private session databases. Expensive Lean/Rust operations now share a nested-safe lease, inherit an8-GiB virtual-memory ceiling and use two workers. Lean probes propagate nonzero exits, including resource failures; no failed check becomes acceptance. New model dispatch retains an8-GiB available-memory reserve. Complete integrated Lean build under the guard:397 jobs, zero errors. Fresh Rust/emission/goal gates still required before the next push.\n'
+            document.write_text(text)
         checkpoint()
         publish_checked_wave()
         (HERE/'policy-recorded.json').write_text(json.dumps({'max_active':15,'recorded':now(),'head':git('rev-parse','HEAD'),'published':True},indent=2)+'\n')
@@ -1122,9 +1301,10 @@
         live=False
         for key in ['runner_pid','model_pid']:
             pid=d.get(key)
-            if pid:
-                try:os.kill(pid,0);live=True
-                except (ProcessLookupError,PermissionError):pass
+            # Lane 402 repair (S15): verify cmdline identity like isolate_pool;
+            # a recycled PID must not mark a dead lane live and skip recovery.
+            if pid and proc_matches(pid,str(Path(__file__).resolve()) if key=='runner_pid' else OPENCODE,str(n)):
+                live=True
         if live:continue
         feedback=HERE/f'recovery-handoff-{n}.md'
         feedback.write_text('The controlling session was interrupted by a reported OOM. Your clone, committed/uncommitted work, exact review snapshot and private session database were preserved. Continue your ORIGINAL owned task from those files and existing private session, keeping HARD RULES. Check actual git diff/build evidence; a dead process or interrupted check is NOT acceptance. Complete the required queued checks and fresh committed report, or preserve a precise honest blocker. User limit is permanently15 across every role. Read .tmp/LANE.md; no safety weakening or fake full-source-to-binary claim.\n')
@@ -1186,8 +1366,8 @@
 def restore_ready_pool():
     m=json.loads((HERE/'manifest.json').read_text());active={'running','starting','starting_feedback','waiting_for_slot'}
     def room():
-        available=next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
-        return available>=8*1024*1024 and sum(lane_state(j['lane']).get('status') in active for j in m['lanes'])<MAX_ACTIVE
+        # Lane 402 repair (S16): infallible memory-gate input.
+        return mem_available_kib()>=8*1024*1024 and sum(lane_state(j['lane']).get('status') in active for j in m['lanes'])<MAX_ACTIVE
     for entry in m['peer_reviews']:
         n=entry['reviewer'];d=lane_state(n)
         if room() and d.get('status')=='queued_isolated_restart' and all(lane_state(a).get('status')=='report_ready' for a in entry['authors']):
@@ -1205,10 +1385,9 @@
     active=[]; pending=[]; ready=[]
     for p in sorted((HERE/'state').glob('*.json')):
         d=json.loads(p.read_text()); pid=d.get('model_pid')
-        alive=False
-        if pid:
-            try: os.kill(pid,0); alive=True
-            except (ProcessLookupError,PermissionError): pass
+        # Lane 402 repair (F6): verify the model cmdline, not just PID
+        # liveness; a recycled PID must not inflate the active count.
+        alive=bool(pid) and proc_matches(pid,OPENCODE,str(d.get('lane','')))
         if alive:
             active.append({'lane':d['lane'],'pid':pid,'kind':d.get('kind'),'slot':d.get('slot')})
         elif d.get('status') in ['starting','starting_feedback','waiting_for_slot']:
@@ -1232,10 +1411,9 @@
         summary={k:d.get(k) for k in ['lane','status','model','runner_pid','model_pid','attempt','commits','session']}
         for key in ['runner_pid','model_pid']:
             pid=d.get(key)
-            try:
-                if pid:os.kill(pid,0)
-                summary[key+'_alive']=bool(pid)
-            except (ProcessLookupError,PermissionError):summary[key+'_alive']=False
+            # Lane 402 repair (F6): identity-checked liveness per role.
+            needle=str(Path(__file__).resolve()) if key=='runner_pid' else OPENCODE
+            summary[key+'_alive']=bool(pid) and proc_matches(pid,needle,str(d.get('lane','')))
         log=POOL/'logs'/f"{d['lane']}.log"
         if log.exists():summary['log_bytes']=log.stat().st_size
         print(json.dumps(summary,ensure_ascii=False))
```
