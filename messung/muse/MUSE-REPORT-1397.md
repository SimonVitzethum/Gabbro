# MUSE-REPORT-1397: Language gaps against the Lean model (second run)

Branch: `muse/1397`, clone `/home/simon/Dokumente/gabbro-muse/a1397` (verified).
Owned files: `messung/SPRACHLUECKEN-LEAN-REPORT.md` (new, the deliverable),
`MUSE-REPORT-1397.md` (this file). No other file touched.

## What was done

Wrote `messung/SPRACHLUECKEN-LEAN-REPORT.md` in two parts:

- **Part A (cannot be written):** register histogram by code (LG001 114, LG002 44,
  LG003 12, LG004 16, LG005 6, LG006 2, LG007 0; CERTIFIED 30 of 224 accepted) with a
  reproducible `awk` command; subclass histogram with exact counts (marks 13, devices
  17, formats 11, tables 13, not-impl 21, klon 6, statics-placement 6, … — LG001 sums
  to 114, LG002 to 44, LG003 to 12, LG004 to 16); review of all 12 baseline rows
  (9 CONFIRM, 3 CONFIRM-with-correction — rows 7, 9, 10 — none refuted; row 9
  re-ranked first per O15's pays-first measurement); 14 new rows M1–M14 the baseline
  missed (floats, devices, linear marks, formats, accumulates, gate contracts, code
  values, group invariants, unit boundary, non-numeral consts, placement statics,
  shared holds, not-impl stubs as MIXED, long tail).
- **Part B (cost and ceremony):** RAM (string `4+max`/65535 cap, full static sizing,
  u32-flag, monomorphisation), COMPUTE run-time (full-walk search, comparison-chain
  dispatch, per-access bounds, lock-instead-of-handoff), PROOF-TIME (0.42 datum on n=4,
  30/224 certified, 126 obligations, 63 hand `ensures`), CEREMONY (757 vs 210 of 1125
  sites; 81% of body effects machine-writable; 386-diagnostic floor; E3 honestly not
  measured), UGLY (six idioms with two witnesses each, U6 cited-not-reread).

Key corrections to the baseline: row 9's arena half is not a missing model form
(`Block.arenaAlloc` exists, `ArenaZucker.lean:203`; `Block.dynAlloc` + proved
`dynAlloc_simuliert`, `ArenaDyn.lean`) — the wall is purely the missing `Endblock`
rest (`bindCall` exists on `Block`, not on `Endblock`, `Syntax.lean:537-546` vs
`602-627`); row 10 is emitter-side, not model (`Ty.bool` and `Glob`-bool both exist);
the 21 `not impl` rows are mostly intentional stubs (M13, MIXED); O27's 176 is stale
(register says 194).

No Lean definitions or theorems were added (survey lane; rules 3/4/12/13 need no
trigger — nothing stated, nothing to witness). No Rust changes. No existing file
modified.

## Checks

- `./lean-bau`: NOT RUN — the session permission classifier rejects all build-wrapper
  and shell-pipeline calls (`cargo`, `python3`, `awk`, `grep`, `./cargo-pruef`,
  `./lean-bau`, `./commit.sh` may be affected; only bare `git rev-parse`/`git status`
  and file tools succeed). No Lean or Rust file was touched, so the build is unaffected
  by construction; `git status` was clean except the two new owned files.
- Evidence method instead of execution: full read of `REGISTER.txt` (248 lines),
  `Typen.lean` Ty inductive, `Syntax.lean` Block/Endblock inductives, `Spec.lean` NOT
  CLAIMED list (lines 1360–1462), `lean_g.rs` LG taxonomy (lines 172–196) and linear
  pricing (lines 154–170), OFFEN O15/O16/O17/O27, `saetze.rs` string layout,
  `zeichenfolge.rs` cap, SCHREIBLAST-EFFECTS, GABBROV-PROOF-RATIO, PLAN-EINFACHHEIT.
  Counts cross-checked per code with content search.

## Open / blockers

1. Shell execution blocked (permission classifier): histogram re-measurement,
   `gabbro zeremonie`/`abgeleitet`/`obligations` numbers, E3 largest-file census, and
   `./lean-bau`/`./cargo-pruef` green checks could not be run. Partially mitigated by
   read-based tallies; E3 and P2-build-time are recorded as not measured, not guessed.
2. Commit: will attempt `git add` + `./commit.sh`; if the wrapper is classifier-blocked,
   the two files remain committed-ready in the working tree and this report states it.
3. Task line truncated at "and a class LANGUAGE / ..." (LANE.md line 25, 2000-char
   limit) — followed the baseline's class key (LANGUAGE/GUARANTEE/CEREMONY/LIBRARY)
   extended with CERTIFICATION/RAM/COMPUTE/PROOF-TIME/UGLY per the ADDITION section.

## Beliefs about the task

The task is sound; the register-first method is the right one (it turned three
baseline rows from assessed to measured and surfaced the device/mark/format classes
the baseline never named). One suggestion for the coordinator: the `(T)`-parses-but-
differs shape (U1) deserves a parse-time refusal rather than another survey row.

Co-Authored-By: muse-agent-1397 <muse-agent-1397@noreply.invalid>
