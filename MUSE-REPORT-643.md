# MUSE-REPORT-643 — independent exact review of candidate 642 (draft-recovery tool)

Lane 643 (`muse/643`, model opencode-go/muse-spark-1.3-contributor).
Task: report-only independent exact review of the lane-642 recovery
parser/tool candidate; own only this file.

## CANDIDATE / VERDICT

- CANDIDATE: 642 fb126d505d5bd15598480a6071511c923d3d1991
  (base 19b31567c91e1077c2232c5fb090c26164d52019 per supplied
  `.tmp/review/SNAPSHOT.json`; BUILD-EVIDENCE pins the same short hash
  `fb126d50` with the 4-file commit).
- VERDICT: ACCEPT

No unsupported desired-correctness premise, no weakened guarantee, no
fake closure was found. The candidate delivers exactly what its report
claims: a bounded replay tool plus tests/docs, with actual IR/Bis/Tmp
recovery honestly reported as blocked (nothing fabricated).

## 1. What was checked (all inside this clone, no other clone/live path)

- Clone/branch verified first: `/home/simon/Dokumente/gabbro-muse/a643`
  on `muse/643` at `5449d84f`; mismatch would have stopped the lane.
- Supplied copies used only: `.tmp/review/author-642/PATCH.diff`,
  `MUSE-REPORT-642.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`,
  `dokumente/x86/DRAFT-RECOVERY.md`, `SNAPSHOT.json`. No network, no
  push, no credential or config access. `.tmp/INPUTS/` and
  `.tmp/RECOVERED/` are absent in this clone, matching the author's
  account (nothing to replay here either).
- `git apply --stat` / `--check` on PATCH.diff: clean; exactly 4 new
  files, nothing else:
  `MUSE-REPORT-642.md`, `dokumente/x86/DRAFT-RECOVERY.md`,
  `instrumente/recover-lane-draft.py` (815 lines),
  `instrumente/tests/test_recover_lane_draft.py` (327 lines).
  No `grammatik/` path, no `.lean` addition, no import, no emitter or
  checker change, no reserved optimiser path.
- Expected hashes/lines cross-checked against the committed original
  `messung/muse/MUSE-REPORT-287.md` lines 25–27: IR.lean 2689 /
  `892abbf1962919b74f0625d647a4bbb0`, Bis287 1581 /
  `f56d11ef8126b0616e2a345a240bcbba`, Tmp287 120 /
  `77855458a919d7bb08dcaf14d0fb65e9`. The candidate's docs repeat
  these values exactly as expectations, not as recovered bytes. The
  patch contains no draft content (the 12 `IR.lean|Bis287|Tmp287`
  mentions are expectation/doc strings).
- Tool source audit: stdlib imports only (`argparse`, `ast`,
  `hashlib`, `json`, `re`, `sys`, `bisect`); no `exec`, `eval`,
  `os.system`, `subprocess`, `socket`, or network import. File writes
  go only to the CLI-given `--output`/`--report`; the only `open()`
  reads are the CLI-given `--input`/`--seed`. Python log blocks are
  parsed with `ast` and never executed; imports/docstrings are
  skipped, any other statement poisons the whole block. Target
  matching is exact-string only (`path != target` returns/skips);
  no program-name special case exists.
- Author's suite rerun verbatim in an isolated extract copy:
  `python3 instrumente/tests/test_recover_lane_draft.py` → 24 tests OK.
- Independent probes against the same extract (own fixtures, own
  assertions): (1) shell `rm` line plus `os.system('touch PWNED')`
  block → 0 replayed, 1 unsupported, no output, no marker file;
  (2) write + two ordered edits → `yz` replayed in order;
  (3) unquoted heredoc + `Delete File` + `diff` block → both refused
  by name, seeded `keep` content survives; (4) digest/line
  expectations on wrong values → exit 3, `verified: false`,
  `reason: digest_mismatch+line_mismatch`; (5) empty input with the
  real IR.lean expectations → exit 3, `recovered: false`,
  `verified: false`, no output file — exactly the author's §4
  account; (6) secret content never appears on stdout/stderr.
- Archive contract: DRAFT-RECOVERY §5 states the merger copies
  ignored `.tmp/RECOVERED/` drafts plus reports to root private
  preserved-drafts before clone deletion. With no draft recovered
  there is nothing to copy yet; the contract is documentation, not
  an executed step, and the report says so plainly. No fake
  durability is claimed.

## 2. Lean build result

`./lean-bau` was NOT run. Justification: the candidate adds no Lean
file (`git apply --stat` shows zero `grammatik/` paths) and this
lane's own change is this report only (`git status --short` shows
nothing under `grammatik/`). A 400-job build would consume the
shared slot for zero signal; the serial merge gate builds anyway.

## 3. What remains open (not objections)

- The actual IR/Bis/Tmp reconstruction still waits on
  `.tmp/INPUTS/` delivery; rerun commands are in DRAFT-RECOVERY §5.
  Accept a future reconstruction only on exit 0 with
  `verified: true` against the §2 hashes.
- The ignored-to-durable archive copy is a documented merger step,
  unexecuted because there is no draft yet.
- The author's Python-block `import` + literal-alias allowance is a
  reviewed judgment call (file-effect-free, poison-on-anything-else
  unchanged); my probes confirm markers are never created and
  other-path writes never execute.

## 4. Task feedback

Nothing in the lane-643 task was found wrong. The truncated OWNER-642
line ("root p...") is completed verbatim by DRAFT-RECOVERY §5, so no
information is missing. The "earlier/inexact draft is explicitly
partial" rule was not triggered: the author claimed no draft at all.

## CUTS

- No Lean theorems or definitions were added by the candidate or by
  this review; there are no axioms to print and no witnesses to owe.
- No live reconstruction was possible in this clone (no `.tmp/INPUTS/`);
  verification is of tool honesty and bounds, not of recovered bytes.
- No `./lean-bau`, `./cargo-pruef`, or `./emission-pruef` run (no
  Lean/Rust/emission surface touched by either the candidate or this
  report); the merge gate's checked build still applies.
