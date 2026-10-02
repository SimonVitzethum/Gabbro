# Draft recovery from recorded lane logs (lane 642)

## 1. The preservation bug

Lane 287 preserved its IR research drafts only under ignored clone
scratch (`.tmp/IR287-PRESERVED/`). Standard merged-clone removal then
deleted the only copies. The root coordinator retains an earlier
snapshot plus the entire recorded OpenCode lane-287 log; exact
log/report copies were to be delivered to the recovery lane under
`.tmp/INPUTS/`. The recovered drafts stay red/unaccepted research
material: they are never imported, built, or merged, and the root
archives them durably without adopting them as compiler IR.

## 2. Report-only evidence (not reconstruction)

From `messung/muse/MUSE-REPORT-287.md` (committed, prose only):

| Draft (original clone path) | Lines | MD5 |
|---|---|---|
| `.tmp/IR287-PRESERVED/IR.lean` | 2689 | `892abbf1962919b74f0625d647a4bbb0` |
| `.tmp/IR287-PRESERVED/Bis287.lean` | 1581 | `f56d11ef8126b0616e2a345a240bcbba` |
| `.tmp/IR287-PRESERVED/Tmp287.lean` | 120 | `77855458a919d7bb08dcaf14d0fb65e9` |

These hashes are expectations for the tool, not recovered bytes.
A hash mismatch is not recovered success.

## 3. Tool: `instrumente/recover-lane-draft.py` (stdlib only)

Replays exact-target file effects from a recorded log. The target
path is a CLI argument; no program name is special-cased. Stdout is
one JSON summary line; file content is never printed. Inputs are read
streamed with `--max-bytes` / `--max-events` / `--max-content` bounds.
Exit codes: 0 replayed (or nothing to replay), 2 usage/IO error,
3 expectation mismatch (digest/line refusal; the faithful fragment is
still written when one exists).

Replayed, in recorded order, all matched by exact target string only:

- JSON lines: `write` (full content), `edit` (`oldString`/`newString`/
  `replaceAll`; refuses empty, missing, or non-unique matches without
  the flag), `read` (seed only, fills empty state once).
- Tool-record blocks (`invoke` with a `write`/`edit`/`read` name and
  named value elements; entities unescaped; same uniqueness rules).
- Literal heredocs: `cat > 'TARGET' <<'DELIM'` through a line holding
  exactly `DELIM`. Quoted delimiter only.
- Literal Python fences: parsed with `ast`, never executed. Allowed
  are imports, docstring expressions, literal `Path`/`open` aliases,
  literal reads, constant-only `write`/`write_text`, and
  `read(...).replace(OLD, NEW)` write-backs with constant arguments,
  all against the exact target. Any other statement poisons the whole
  block: nothing from it is replayed.
- `apply_patch` sections `Add File: TARGET` (plus-lines only) and
  `Update File: TARGET` (`@@` hunks applied with exact context match;
  a mismatch marks that section unreplayed, later events still run).

Recorded as unsupported/unreplayed (never executed, listed with line
numbers in `--report`): shell commands, unquoted heredocs, truncated
blocks, non-literal code, `Delete`/`Rename`/`Move` sections, `diff`
blocks, incomplete events, oversized payloads, edits without a base,
and digest/line expectation mismatches.

## 4. Recovery attempt record (lane 642, 2026-10-01)

`.tmp/INPUTS/` was absent for the whole lane session (checked at start
and before the attempt; `.tmp/opencode/` empty), so no recorded event
was available. The tool was run once per draft against an empty probe
input with the §2 expectations; all three exited 3 with
`recovered: false, verified: false, reason: digest_mismatch+
line_mismatch`, and no output file was written. Per-draft reports are
kept under ignored `.tmp/RECOVERED/` (`IR.lean.report.json`,
`Bis287.lean.report.json`, `Tmp287.lean.report.json`). The most recent
faithful recovered fragment is therefore: none. Nothing was
fabricated to fill the gap.

## 5. Rerun once inputs land

Copy the recorded log/report files to `.tmp/INPUTS/` (never another
clone or live paths), then for each draft, e.g.:

    python3 instrumente/recover-lane-draft.py \
      --input .tmp/INPUTS/lane287.log --target .tmp/IR287-PRESERVED/IR.lean \
      --output .tmp/RECOVERED/IR.lean --expect-md5 892abbf1962919b74f0625d647a4bbb0 \
      --expect-lines 2689 --report .tmp/RECOVERED/IR.lean.report.json

Accept only exit 0 with `verified: true`. On exit 3, read the report's
`unreplayed`/`unsupported` lists: they name the exact gap (line
numbers, not content). The current merger copies ignored source
drafts from `.tmp/RECOVERED/` to root private preserved-drafts before
clone deletion; reports travel with them.
