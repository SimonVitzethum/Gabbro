# MUSE-REPORT-1398: Exact review of candidate 1397 (language gaps vs Lean model)

Branch: `muse/1398`, clone `/home/simon/Dokumente/gabbro-muse/a1398` (verified at
start: pwd and `git rev-parse --abbrev-ref HEAD` matched before file review).
Owned file: `MUSE-REPORT-1398.md` (this file) — nothing else touched.
CANDIDATE: 1397 845b6e14d5984c28955c5b0f201adcc5d7b74920
Pinned snapshot (SNAPSHOT.json): base `e5ed4d2c`, files `MUSE-REPORT-1397.md` +
`messung/SPRACHLUECKEN-LEAN-REPORT.md`, clean.

## What was done

Read-only exact review from `.tmp/review/` (never used git on the pinned hash):
OWNER-TASK.md, MUSE-REPORT-1397.md, SPRACHLUECKEN-LEAN-REPORT.md (407 lines),
PATCH.diff (492 lines), BUILD-EVIDENCE.json, SNAPSHOT.json. Then re-verified
every review criterion against my own clone:

1. **Histogram reproducibility + register match.** The candidate's named `awk`
   command is well-formed for this register (tab-separated `STATUS path CODE
   message`; `print $3` yields the code — confirmed by reading REGISTER.txt
   lines 24-30 and the footer line 248:
   `# TOTAL: 224 accepted, 30 CERTIFIED, 194 UNCERTIFIED`). Independent tallies
   in my clone: CERTIFIED 30 (exact grep count), LG002 44, LG003 12, LG004 16,
   LG005 6, LG006 2, LG007 0 (all exact grep counts) — hence LG001 = 194-80
   = 114. Every headline number matches; the arithmetic closes (114+44+12+16+
   6+2+0 = 194; 194+30 = 224).
2. **Six gap rows re-derived (requirement was five):**
   (a) no generics — `Ty` inductive `Typen.lean:35-59` is closed, no parameter/
   application former; (b) option index-only — `Ty.opt (n : Int)`,
   `Typen.lean:40`; (c) missing `Endblock` rest — `Block.bindCall/bindCallElse`
   exist (`Syntax.lean:537-546`), `Endblock` (`Syntax.lean:602-627`) has
   `bind/bindAxiom/bindAxiomElse` but no `bindCall`, and register LG004 lines
   85/86/178/179 refuse top-level `alloc` on exactly this ground;
   (d) M1 floats — model HAS `Ty.fl` (`Typen.lean:49`) + `Block.gleit*`
   (`Syntax.lean:590-600`) while register line 123 refuses `26-gleitkomma`
   as LG002; (e) M2 devices — model HAS `Block.regLies` (`Syntax.lean:566`)
   while register line 59 refuses `12-umlaufendes-register` as LG001 (no `Reg`
   builder); (f) row-10 correction — `Ty.bool` exists (`Typen.lean:38`) and the
   LG002 message text itself names `bool` as a travelling `Glob` form, so the
   bool-static wall is emitter-side, as the candidate states.
3. **Language vs model gaps kept apart.** The LANGUAGE (no Lean former) vs
   CERTIFICATION (checker accepts/emits, exporter refuses) class key is applied
   per row; rows 2/8 are explicitly dual-classed with both walls named, and
   row 10 was moved out of "model gap" entirely. No CERTIFICATION row is
   presented as a language-missing-construct claim.
4. **No unbounded-dynamic-structure duplication.** Unbounded heaps are
   explicitly excluded in the scope header and the "Deliberately NOT listed"
   section; the only arena rows are the bounded-ceiling `grow`/commit shape
   (register line 90, LG005) and the `Endblock`-rest wall, both in scope per
   TODO section 0e.
5. **Measured vs assessed separated.** Method note (lines 10-24) declares the
   rule; row 4 "still assessed", M13 "assessed", R3 "Assessed", U4 "assessed
   as idiom, measured as refusal", U6 "cited, not re-measured", E3 and P2
   build-time "not measured, not guessed". Nothing guessed is labelled
   measured.
6. **No guarantee-weakening proposal.** Every fix is an exporter arm, an
   emitter lowering, a new refusal, or named proof work (M6 duties, C4 O25c
   rule); U1 proposes a parse-time refusal; E1 keeps `ensures` (63 sites)
   hand-written by design and E2 keeps the 386-diagnostic register as the
   floor. No row asks to admit an uncertified program or drop a check.
7. **Patch scope.** PATCH.diff contains exactly two `diff --git` entries, both
   owned files (`MUSE-REPORT-1397.md`,
   `messung/SPRACHLUECKEN-LEAN-REPORT.md`). No Lean, Rust, or existing file
   touched — consistent with a survey lane.

## New definitions/theorems

None. Report-only exact review; HARD RULES 3/4/12/13 need no trigger (nothing
stated, nothing to witness).

## Checks

`./lean-bau`: NOT RUN — no Lean, Rust, or build-input file was touched or
added by this lane (only this markdown report), so the build is unaffected by
construction. One `bash` file-listing call was refused by the session
permission classifier mid-review; all verification above used the file-search
and file-read tools instead, including exact per-code register counts.

## Open / blockers

None for this verdict. Carried notes (not blockers): the owner's shell block
meant its histogram was tallied by reading rather than executed — remedied
here by independent exact counts; E3 (largest-file ceremony census) and Lean
build-time cost remain honestly unmeasured, which the task permits without
running the congested Lean slot.

## Beliefs about the task

The task is sound and the register-first method is the right one; the owner's
three corrections (row 9 arena-half, row 10 emitter-side, M13 stubs-as-MIXED)
all check out against the cited lines. One suggestion for the coordinator:
pin the re-measurement shell command used for the histogram into the report's
method note as executed output once a lane with shell access re-runs it.

VERDICT: ACCEPT

Reasons (unchanged from the committed review): histogram reproduced exactly
(224/30/194; LG001 114, LG002 44, LG003 12, LG004 16, LG005 6, LG006 2,
LG007 0); six gap rows re-derived from cited Lean/register lines;
LANGUAGE/CERTIFICATION separation kept; unbounded structures excluded;
measured/assessed labelled; no weakening proposed; patch touches only the two
owned files.

Co-Authored-By: muse-agent-1398 <muse-agent-1398@noreply.invalid>
