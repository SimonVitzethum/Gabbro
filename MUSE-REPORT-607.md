# MUSE-REPORT-607: Independent overnight closure review of 595

Lane 607. Clone `/home/simon/Dokumente/gabbro-muse/a607` and branch
`muse/607` verified before work (HEAD `377b290e`). This lane owns only
this report file. No other file was touched. No Lean, Rust, checker,
emitter, Spec/goal, optimiser, or coordinator file was changed, and no
Lean import was added.

## Candidate under review

Snapshot `.tmp/review/SNAPSHOT.json` pins author 595 at head
`cc05aa34fe178167a4b4ef9ab0e675b422b50777`, base `0044c258`,
`clean: true`, with exactly these files:

- `MUSE-REPORT-595.md`
- `dokumente/x86/AGENT-MONITOR.md`
- `instrumente/agent-monitor.py`
- `instrumente/tests/test_agent_monitor.py`

I inspected the review copies under `.tmp/review/author-595/` (report,
owner task, `PATCH.diff`, `BUILD-EVIDENCE.json`, and the three delivered
files). `PATCH.diff` contains exactly the four files above, all new, all
inside the owner's owned paths. No `.lean` file, no `Grammatik.lean`
edit, no Rust/checker/emitter change, no second scheduler, no network or
credential access. Scope is tools/docs only, which matches the owner
task.

## What I did

1. Verified clone path, branch, and clean tree before starting.
2. Read the owner task, the author report, the build evidence, the full
   patch, and all three delivered files end to end.
3. Copied the exact candidate `agent-monitor.py` and
   `test_agent_monitor.py` to a scratch directory and reproduced the
   fixture suite there (copies removed afterwards; tree is clean).
4. Ran additional adversarial probes against the exact candidate code:
   read-only inputs, unregistered-lane filtering, ambiguous report
   lines, sibling pause auto-detect, restart dedup, low-memory blocker,
   and cmdline-confidentiality checks.
5. Checked forbidden patterns (process killing, subprocess, sockets,
   environment/credential reads, coordinator import/execution) by
   inspection and grep.

## Evidence (actually run on the exact candidate)

- `python3 instrumente/tests/test_agent_monitor.py` on the exact
  candidate copy: all 11 tests pass (`Ran 11 tests ... OK`), covering
  clean running counts, completion with head plus the single report
  line, no-verdict-without-report, dead, reused-PID mismatch,
  wrong-model marker, explicit pause, restart dedup, dependency plus
  under-utilisation, stalled heartbeat, and unreadable-cmdline
  fail-closed.
- `python3 -m py_compile instrumente/agent-monitor.py`: clean.
  `--help` lists all documented flags.
- Adversarial probes, all passing: inputs (manifest, states, stray
  lane-999 file) byte-identical after `--once`; unregistered lane
  ignored; two conflicting report lines yield a null verdict (never
  inferred); sibling `coordinator-pause.json` auto-detected with the
  run marked paused and auto-actions ordered to stop; rerun emits zero
  new events; `MemAvailable` below reserve raises the resource blocker;
  status/events output contains no cmdline or lane-title fragments.
- No `./lean-bau` run: the candidate adds no Lean file and no
  `Grammatik.lean` import, so no Lean build is owed or claimed by it,
  and this review adds none either. No `./cargo-pruef` run: no Rust
  file is touched. Lean-axiom and joint-witness obligations are
  not applicable because the candidate states no generic proof claim
  and adds no Lean theorem.

## Requirement-by-requirement check

- Read-only: passes. The monitor only reads state files of registered
  lanes, the manifest, `<pid>/cmdline`, `meminfo`, log mtimes, and
  exact report lines. It writes only the explicit status, events, and
  seen destinations (atomic tmp-plus-rename for JSON, append plus
  flush/fsync for JSONL). No launches, kills, messages, environment or
  config reads, key scans, or full-cmdline output; cmdlines are matched
  by substring and never stored.
- Actual/model/runner/PID identity: passes. Runners match
  `coordinat` plus lane, models match `opencode` plus lane; a live PID
  with the wrong cmdline is reported as mismatch, is not counted, and
  raises the reused-PID blocker. Unreadable cmdlines fail closed as
  alive with identity `unknown`. Model and runner liveness are counted
  separately, so starting runners are never counted as models.
- Completions and transitions: passes. Events fire only on observed
  state transitions, carry the state's head (`null` for author lanes by
  design) and only an exactly-once report line; a green build alone
  produces no positive claim.
- Restart and pause: passes. The seen store (lane plus status plus
  updated plus head) deduplicates across restarts, verified on both the
  bundled suite and my rerun probes. Explicit plus sibling pause
  markers surface `paused` with an order to stop auto-actions; the
  monitor itself takes no action either way.
- No second scheduler: passes. The candidate never imports or runs the
  coordinator, holds no locks, and performs no restoration or backfill;
  the report and doc state that bounded recovery stays with the
  existing coordinator.
- Docs: passes with concrete content. `AGENT-MONITOR.md` gives runnable
  single, continuous, live-tree, and fixture commands, a flag and
  output reference, the pause/integration contract, and the dated
  registry assumptions with an explicit do-not-guess rule on drift.
- Out of scope for this candidate: the Rust repair lane, the
  docs/decision lanes, and the source-to-byte connection theorems are
  separate ownerships and were not re-verified here. Nothing in this
  candidate weakens any guarantee; it proves no theorem and refuses
  nothing, so there is no guarantee to weaken.

## Precise limits (accepted scope, not closure)

The author's CUTS block is accurate and stays a limit list, never a
closure claim: advisory status only; author-lane heads are `null` by
design with exact identity left to the review snapshot; heartbeat
staleness cannot separate slow from stuck below threshold; registry
drift needs an owned follow-up. Non-blocking notes: sibling-pause
auto-detect is exercised by my probes rather than the bundled suite,
and the smoke run over the real registry shape is reported without a
replayable fixture, but both behaviours re-verified from the exact
code here.

## Machine-readable result

CANDIDATE: 595 cc05aa34fe178167a4b4ef9ab0e675b422b50777
VERDICT: ACCEPT
