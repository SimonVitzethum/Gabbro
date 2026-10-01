# MUSE-REPORT-642 — recovery parser/tool for recorded lane drafts

Lane 642 (`muse/642`, model opencode-go/muse-spark-1.3-contributor).
Task: recover the preserved lane-287 IR research drafts from recorded
edits after clone removal, via a reusable stdlib recovery tool.

## 0. Outcome up front

Delivered and committed (4 owned files only):

- `instrumente/recover-lane-draft.py` (tool v642.1, stdlib only)
- `instrumente/tests/test_recover_lane_draft.py` (24 tests, all pass)
- `dokumente/x86/DRAFT-RECOVERY.md` (bug, spec, attempt record, rerun)
- `MUSE-REPORT-642.md` (this file)

Actual source recovery: **blocked, nothing fabricated.** `.tmp/INPUTS/`
(the promised exact log/report copies) was absent for the whole lane
session, so no recorded event existed to replay. All three drafts were
probed with their report-287 expectations; each exited 3
(`recovered: false, verified: false, reason:
digest_mismatch+line_mismatch`) with no output file written. Refusal
reports sit under ignored `.tmp/RECOVERED/`. The coordinator can rerun
the tool verbatim once inputs land (exact commands in DRAFT-RECOVERY
§5); accept only exit 0 with `verified: true`.

No Lean file was touched, added, or imported; no proof claim is made
anywhere. The drafts remain red/unaccepted by design.

## 1. Tool: exact names

`instrumente/recover-lane-draft.py`, functions:
`build_parser`, `unescape_xml`, `parse_replace_all`, `is_str_const`,
`open_call_path_mode`, `analyse_python_block`, `process_py_stmt`,
`process_py_assign`, `read_of_target`, `replace_of`,
`write_receiver_target`, `process_py_write_expr`, `process_py_with`,
`apply_edit`, `split_keep`, `apply_patch_update`, `main`,
`read_bounded`, `line_offsets`, `collect_xml_event`,
`collect_line_events`, `collect_json_line`, `collect_heredoc`,
`collect_python_block`, `collect_patch_block`, `parse_hunks`,
`replay`, `finish`. Exit codes 0/2/3 (replayed / usage-IO error /
expectation refusal).

Replayed for the exact `--target` string only (no filename is
special-cased): JSON `write`/`edit`/`read(seed)` lines, tool-record
blocks, quoted-delimiter heredocs, constant-only Python write/replace
patterns via `ast` (never executed; imports and docstrings skipped,
any other statement poisons its block), `apply_patch` add/update
sections with exact-context hunks. Everything else (shell, unquoted
heredocs, non-literal code, delete/rename/move, diff blocks,
incomplete/oversized events, edits without base, digest mismatch) is
refused and listed with line numbers in `--report`. Stdout is one JSON
line; content is never printed.

## 2. Verification

- `python3 instrumente/tests/test_recover_lane_draft.py`: 24 tests OK
  (no-command-execution incl. `os.system`/`subprocess` plus
  other-path write non-execution, exact-path, ordered
  patches/replacements incl. `edit_without_base` and
  `patch_hunk_mismatch`, unsupported ops incl. `unquoted_heredoc`
  and `patch_refused`, digest refusal exit 3 vs match exit 0,
  seed via read-event, stdout secrecy).
- Manual probes: JSON/heredoc/python/patch/XML paths replay; `import`
  + alias-threading (`p = Path(T)` … `p.write_text(fixed)`) replays.
- `git status --short grammatik/`: empty (no Lean change).
- Last `./lean-bau` result line: **not run.** Justification: the lane
  owns no Lean file and `grammatik/` is byte-identical to master, so a
  400-job build would only consume the shared build slot for zero
  signal. If the merge gate wants it, it runs on an unchanged tree.

## 3. What remains open

- The actual IR/Bis/Tmp reconstruction, pending `.tmp/INPUTS/`
  delivery (rerun commands in DRAFT-RECOVERY §5).
- Independent checksum review of any future reconstructed output
  (required before archival; report-only hashes in DRAFT-RECOVERY §2).
- The merger copy step (ignored `.tmp/RECOVERED/` to root private
  preserved-drafts before clone deletion) is documented, not executed
  here: there is no draft to copy yet.

## 4. Task feedback

Nothing in the task was found wrong; one delivery gap is recorded,
not a task defect: the `.tmp/INPUTS/` copies the task promises never
arrived in this clone (`.tmp/opencode/` stayed empty). The tool,
tests, and docs assume nothing about the log beyond the formats in
DRAFT-RECOVERY §3; if the real lane-287 log uses further encodings,
the tool will refuse loudly (unsupported list) rather than guess.

One judgment call worth reviewing: Python blocks allow `import` lines
and literal alias threading. This was needed for precision (a bare
`open(T).write(...)` block almost always carries an import), and both
are file-effect-free. The poison-on-anything-else rule is unchanged.
