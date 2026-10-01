# Muse report 415: adversarial implementation audit END-TO-END-TRUST

Clone: `/home/simon/Dokumente/gabbro-muse/a415`, branch `muse/415` (verified).
Snapshot read: `0b3132b7`.
Own files only: `dokumente/x86/AUDIT-END-TO-END-TRUST.md` (new),
`MUSE-REPORT-415.md` (this file). No other path touched.

## What was done

Produced the end-to-end trust audit as tasked: exact generic closing
theorem shape (`schluss_x86` with derived refinement), stage-by-stage
closure inventory, deep audit of the three focus modules
(`Bild.lean`, `Byteschritt.lean`, `InvariantenOpt.lean`) with
file/theorem/line evidence, consumer-gap analysis of the neighbouring
accepted modules (`Zugriffe`, `TSO`, `Relokation`, `AccessList`,
`OverlapRefusal`, `SpillPrivate`, `AufrufOpt`, `StaerkeReduktion`,
`ControlFlow`, `LockedOps`), vacuity-risk audit, validator-input trust
table, runtime/link/loader coverage audit, proof-vs-CUTS ledger, and a
prioritized P0-P3 repair / missing-bridge list. The audit explicitly
distinguishes correct-within-claim helpers from legitimately OPEN bridges
and names the one finding that is phrased as a review finding rather than
a defect (F3, the `Zugriffe` pilot-only footprint).

Read in full: `DIRECT-COMPILER.md`, `DIRECT-COMPILER-DESIGN.md` (§§1-7A
relevant parts), `grammatik/OPTIMIZER.md` (§§1-10), `WORK-ALLOCATION.md`,
all `dokumente/x86/*.md` review/bridge docs (headers, verdicts, gap
tables, CUTS), and the actual Lean sources listed above (definitions,
theorem statements, CUTS tails, `#print axioms` blocks). Resolved every
name from files; invented no behaviour; duplicated no IR/executor;
touched no friend path, checker, Spec, goal, Rust, emitter, or canonical
Typen/execution/codec beyond reading.

## Exact names of new definitions/theorems

No new Lean definitions or theorems (audit lane; none tasked, none
needed). New deliverable: `dokumente/x86/AUDIT-END-TO-END-TRUST.md`
(9 sections + appendices A-C). No experimental Lean probe files were
created (nothing to keep private in `.tmp`).

## Last `./lean-bau` result line

No `./lean-bau` run: this commit is docs-only (two markdown files, no
Lean/Rust/emitter change), so no Lean rebuild is owed by it. A fresh
`./lean-probe grammatik/Grammatik/X86/Bild.lean` was attempted and timed
out after 120 s on the queued Lean slot shared with other lanes; no
fresh build number is claimed. Verification actually performed: grep
over all eleven X86 modules for `sorry|admit|axiom |native_decide|unsafe`
(zero real hits — every `admit*` match is English "admitted/admits" in
comments), presence of `#print axioms` blocks in every module, and
reading of all CUTS sections. This is stated honestly in the audit's
build note.

## What remains open

- The full source-to-final-bytes chain remains OPEN (no `SCFG`,
  `lowerOk`/`check_C`/`layoutOk`/`valX86`/`valX86_sound`/`schluss_x86`,
  no 287 IR, no TSO bridge, no budget/time transfer) — the audit's
  central, expected result.
- Independent exact-candidate review of this audit (lane 495) happens
  separately; root integration happens separately.
- The prioritized work (§7 of the audit): P0 IR + validator skeleton +
  source-duty exports; P1 per-access bridge + O-align/O-access closure +
  patched-byte re-decode; P2 entries/ABI/loader/binding coverage + cost
  schema coupling; P3 width/profile/flag/SIMD gates + cache/profile
  discipline.

## Anything in the task believed wrong

Nothing wrong. Two remarks: (1) the "actual reproduced Lean probes"
ask could not be satisfied with fresh queued builds from this clone
today (slot contention); the audit substitutes committed closed
theorems re-verified by reading + grep and says so, rather than
claiming numbers not measured. (2) The lane prompt's generic witness
paragraph (joint non-degenerate witnesses for "all main results") fits
author lanes; for an audit lane with no new theorems the correct
analogue — checking that every cited helper HAS such witnesses and
refusals — was done instead (§5 of the audit).

Co-Authored-By: muse-agent-415 <muse-agent-415@noreply.invalid>
