# MUSE-REPORT-678: Organise and audit complete essential hardware-model coverage
# (revision 2 — root-review repair; committed after docs diff/link checks)

## What was done (revision 1, commit 0f87c00f)

- Verified clone `/home/simon/Dokumente/gabbro-muse/a678`, branch `muse/678` (match; proceeded).
- Wrote the owned deliverable `dokumente/x86/HARDWARE-MODEL-COMPLETION.md` (single actionable
  completion matrix) and this report. No other files touched; no Lean/Rust changes.
- Read as evidence: `DIRECT-COMPILER-DESIGN.md` §§0–12, `dokumente/x86/EMITTER-INVENTAR.md`
  §§0–13, all nine hardware task prompts `lanes/660.md`–`lanes/676.md` (even numbers),
  `ExtendedExecution.lean` interface + CUTS (828 lines), per-module declaration counts + CUTS
  first-lines for ~40 X86 modules, and targeted omission greps (AF, failed-CAS, noncanonical,
  FP sticky/payload, XCR0/OSXSAVE, device ordering).
- Matrix summary (unchanged by revision 2): pilot partial (proved); address encodings
  unimplemented; integer widths partial; LOCK/fences partial with proved obstruction
  (`cas_fehlschlag_stottert`); scalar FP partial (class-level NaN, sticky unmodelled,
  f32 refused); faults partial; interrupts admission-proved/async-rules-open; SIMD partial
  with proved obstruction (only `osXmm : Bool`, no CPUID/XCR0 model); ports/devices
  unimplemented in Lean; TSO bridge partial; image/ABI/entry/budget connections open.

## What was done (revision 2 — this repair)

Root review found three scope/handoff issues in the organiser document. All three are
repaired ONLY in the owned document `dokumente/x86/HARDWARE-MODEL-COMPLETION.md`; all
useful evidence is preserved (no row, witness, or file reference was removed).

1. **No completion by refusal/deferral of essentials.** Added a non-demotion rule at the
   top of §5 naming the AGREED ESSENTIAL families of design §2D plus ALL of their
   observable/fault/TSO/async/control obligations: none of them can become complete
   through refusal, a move to CUTS, or unilateral deferral. Only families ALREADY agreed
   as deferred by the design (or later explicitly changed by Simon) may stay deferred.
   An unsupported encoding outside selected scope may refuse at decode; missing essential
   supported-source behaviour keeps the milestone OPEN. Rewrote DONE item 6A.1 ("no escape
   by refusal") and 6A.3 ("omission ledger proved, not parked") to close the old escape
   hatch that let missing rows move to §5 with a dated refusal.
2. **Hardware-model DONE (6A) separated from required follow-on DONE (6B).** The old
   single DONE list is split: 6A covers the common architecture, exhaustive selected
   bytes/effects/faults/TSO-atomicity-facts/async/control/profile, exact reviews,
   witnesses and assumptions — and explicitly does NOT require the future complete
   compiler theorem or Rust backend. 6B keeps the mandatory OPEN follow-on:
   per-access TSO→W→GX bridge, image/ABI/entry/budget connection, `valX86_sound` +
   closing theorem, full publication + Rust backend + measurement. Added the
   classification rule: target hardware atomicity/per-access facts (single-copy table,
   LOCK unit, fence drain, tearing, fault-vs-observer order) belong to 6A item 4; the
   simulation mapping each target access onto W messages/GX runs belongs to 6B item 1.
   No per-access TSO/source obligation was discarded — bridge consumers must not
   re-abstract what 6A proves. Follow-ups relabelled: F1–F6 → 6A, F7–F8 → 6B follow-on
   (F7 dependency corrected to 6A item 4 facts + TSO-wave bridge interfaces; F8 to
   6A DONE plus F7). §2 rows J/K annotated with their 6B homes.
3. **Exact reviewer evidence instead of number arithmetic.** Struck "reviewer = author +
   18" (wrong wave) and replaced 6A.7 with assigned pairs read from the committed
   prompts: 661→660, 663→662, 665→664, 667→666, 669→668, 671→670, 673→672, 675→674,
   677→676. Recorded that 677's prompt text repeats the 660 title in parentheses after
   "author676" — kept as written, nothing inferred. No verdict is claimed for any
   pair; DONE requires each reviewer's committed VERDICT on its exact candidate.
   Counts updated with actual clone evidence only: 94 X86 modules, 50,368 physical
   lines measured in this clone (replacing the stale 62/~26,300 handoff snapshot).
   §8 + CUTS now state that lane 679's exact review of this matrix
   (`CANDIDATE: 678 <HEAD>`, `VERDICT: ACCEPT or REPAIR`) is pending — this revision
   is UNREVIEWED and claims no approval.

## Exact names of new definitions/theorems

None in either revision. Docs-only organisation lane: no Lean definitions or theorems
added or modified; `grammatik/Grammatik.lean` untouched.

## Last `./lean-bau` result line

No Lean build was run in either revision, by task design: the lane owns only two
Markdown files and changes no Lean/Rust input, so there is nothing to build and no
fictitious build is reported (task: "docs-only diff/link checks, no fictitious Lean
build"). Docs checks performed instead: full `git diff` of the owned document reviewed,
and every file path cited in the matrix re-verified to exist in this clone
(32 paths incl. all nine author prompts, all nine reviewer prompts, `lanes/679.md`,
design, emitter inventory, TSO-GX-BRUECKE, IMAGE-ABI, FLOAT-ZEIT, REFERENCES.json,
and all cited X86 modules) — link check clean, `git status` shows only owned files.

## What remains open

- All producer work (660–676 candidates, their +1 reviews, integration, publication).
- Independent fresh exact review 679 of the repaired candidate must approve the change;
  no change to any assigned reviewer verdict was made here (reviewer prompts untouched,
  no verdict claimed or altered).
- The matrix must keep moving rows only on merged + independently reviewed evidence.

## What I believe is wrong or risky

- Nothing in the repair instruction is wrong. One observed prompt-text anomaly (not a
  finding against any lane): `lanes/677.md` titles port-IO/device work but its review
  line reads "Review exact author676 (Hardware completion: coherent multicore
  architectural execution)". Pairing 677→676 is unambiguous from the author number;
  the parenthetical title is recorded verbatim in the matrix without inference.
- `MUSE-REPORT-679.md` does not exist in this clone (expected — 679 works in its own
  clone); no 679 verdict can or does exist here yet.
