# MUSE-REPORT-1395 — Language gaps: what cannot be written today

Lane 1395, clone `/home/simon/Dokumente/gabbro-muse/a1395`, branch `muse/1395`
(verified by directory read; `git`/shell unavailable in this session, see blocker).

## What was done

Read-only survey, no language/checker/existing-file change (per task):
`dokumente/OFFEN.md` (O1–O32 + L/J residues), `dokumente/SYNTAX.md` (§§1–4,
attributes + EBNF), `TODO.md` (§-1 waves, §0/§0b/§0c/§0d/§0e),
`messung/SCHREIBLAST-EFFECTS.md`, `messung/schreibprobe/` (S11, S12, S13,
S15, S18, S20, S22 in full; directory listing of the rest),
`crates/gabbro-check/src/saetze.rs` area (via grep over refusal codes),
`beispiele/` + `beispiele/gift/` listings.

Deliverable written: `messung/SPRACHLUECKEN-REPORT.md` — 12 ranked gaps,
each with (1) needing program, (2) smallest text + refusal code,
(3) workaround + cost, (4) class, (5) measured-vs-assessed marking.
Top findings: (1) no type parameters — `type Queue(T)` parses but is not
a parameter (`C001` at use; `Queue<T>` is `P001`); (2) record-as-value —
checks and emits, exporter `LG002`, no `Ty` (O15/O16 priced and refused);
(3) `traverse` has no label — `leave i` is `S001` (S13); (4) no windowed
traverse (`P001`); (5) `option` only over indices (`P001`, S12);
(6) `count` not in `invariant`/`spec fn` (`D021`, S11); (7) strings
refused in aggregates (`N465`, O24); (8) byte pointers/region answers
uncertified (`LG003`, O37); (9) no `Endblock` binders (O14(2)/O27);
(10) `bool` static never becomes C (`C001`, S16); (11) plain-payload
after `awaits` open (`N485` reserved, O25c); (12) dense full-`u32`
dispatch ceremony (TODO §0c). Non-gaps explicitly listed so they are
not re-reported. No guarantee-weakening fix proposed.

No new Lean definitions/theorems (none tasked; none added).
No new refusal codes, gifts, or examples (survey lane; none taken).

## Last build result

No build could be run: every `bash` invocation in this session is
rejected by the tool permission gate, so `./cargo-pruef`,
`./emission-pruef`, `./lean-bau`, `./lean-probe`, `git` and `./commit.sh`
are all unavailable. No file needing a build was touched (two new
Markdown files only), so nothing is red: the tree is unchanged except
for the two owned untracked files. Lean status: untouched, presumed
green (not re-verified — see blocker).

## What remains open

- Independent verification of each row against a built `gabbro` binary
  (mark rows currently labelled "assessed", esp. row 4).
- The `bool`-static row and the dense-dispatch row deserve a fresh
  `gabbro pruefe`/`emit` pin (their probe headers are the current evidence).
- Commit of `messung/SPRACHLUECKEN-REPORT.md` + this report (blocked, below).

## Blocker (precise)

`default.bash` calls are rejected ("The user rejected permission to use
this specific tool call", 2026-10-06 session) — first observed on a
`pwd`/`git branch` verification command, reproduced for all shell use,
and re-confirmed on two continuation prompts (branch/status check
rejected again). Consequences: (a) branch could not be confirmed via `git` (clone path
verified by directory read instead); (b) no queued wrapper could run;
(c) `./commit.sh` could not run, so the two owned files are WRITTEN BUT
UNCOMMITTED. Request: commit from a session with shell access
(`git add messung/SPRACHLUECKEN-REPORT.md MUSE-REPORT-1395.md` +
`./commit.sh` with message ending
`Co-Authored-By: muse-agent-1395 <muse-agent-1395@noreply.invalid>`).

## Continuation (this turn)

- Re-read `.tmp/LANE.md` (HARD RULES kept) and re-verified both owned
  files: `messung/SPRACHLUECKEN-REPORT.md` is complete (225 lines,
  12 ranked gaps + non-gap list + ranking rationale + method/Caprock/
  class-coverage notes), this report is current. No review/fix feedback against the draft exists, so no
  content change was owed; no existing file was touched.
- Queued checks: not applicable to this lane's scope (two new Markdown
  files only; no Lean, no Rust, no corpus change) — and not runnable
  here in any case (shell denied, see blocker). Nothing is red.
- Commit: still impossible from this session (no shell for `./commit.sh`).
  Both owned files remain written but uncommitted; pickup instruction in
  the blocker section stands unchanged.

## Continuation (method check, this turn)

- Verified by file search: no `target/debug/gabbro` exists in this
  clone, so the grammar/sentence/probe-header method stated above is
  the only one available here — recorded in the deliverable's method
  note (no row changes; the note was already accurate, now pinned).
- Attempted the task-listed Caprock read-only source
  (`../caprock-messbasis`): denied — outside-clone reads are blocked by
  this session's sandbox rules. Recorded as a Caprock note in the
  deliverable; OS-component needs rest on OFFEN/TODO/probe citations.
  No other file touched; commit still blocked (no shell).

## Continuation (element audit, this turn)

- Re-read `.tmp/LANE.md` in full (HARD RULES kept) and audited all 12
  ranked rows against the five required elements (needing program,
  smallest text/rule, refusal code, workaround + cost, class) plus the
  measured/assessed marking. Result: 12 of 12 complete; only row 4 is
  marked assessed, the rest measured.
- One audit fix applied: the class key defined LIBRARY with no ranked
  row using it. Added a class-coverage note to the ranking rationale
  (stdlib content is gated behind row 1, booked under non-gaps).
  No guarantee-weakening proposal; no other file touched; commit still
  blocked (no shell).

## Continuation (shell restored, commit proceeding)

- Clone and branch verified via shell: `/home/simon/Dokumente/gabbro-muse/a1395`,
  branch `muse/1395`. Earlier `default.bash` rejections are resolved;
  `git status` shows exactly the two owned untracked files
  (`MUSE-REPORT-1395.md`, `messung/SPRACHLUECKEN-REPORT.md`), nothing else.
- No build-affecting files touched, so no `./cargo-pruef`/`./lean-bau`
  run is owed by this lane's scope (two new Markdown files only).
  Committing both owned files now via `arbeitsprotokoll/.commitmsg` +
  `./commit.sh` per HARD RULES rule 8.

## Task feedback

The task is sound as written; one correction, now resolved: rule 8's commit path
assumes shell access, which this session denied until this turn — shell was
restored, verification and commit run from here. Nothing in the task asked for more
than the evidence supports; rows priced-and-refused (O15/O16) are kept
as refusals, not re-proposed.
