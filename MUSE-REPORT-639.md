# MUSE-REPORT-639: Exact review of 638 (optimiser/compiler design alignment)

- Branch verified: `muse/639` in `/home/simon/Dokumente/gabbro-muse/a639`. Owns ONLY this file. No source edits; working tree clean except this report.

## Pinned candidate

CANDIDATE: 638 f398ec6d8c18bf2f21fa9aa2f7eb88014fedea13

- Pinned base `47f447d075e63a5bf53747e25287051b991e9d8c`, per `.tmp/review/SNAPSHOT.json`; `clean: true`, files exactly the 4 owned paths.
- Inspected: `.tmp/review/author-638/PATCH.diff` (708 lines), `OWNER-TASK.md`, `MUSE-REPORT-638.md`, `BUILD-EVIDENCE.json`, `SNAPSHOT.json`, and the three candidate docs in full.

## Finding

VERDICT: ACCEPT

## What was checked

1. Direct-source consistency across all three docs: every doc names the existing typed source AST with `execStmt`/`exec` as the single normative source reference and decision contracts L1–L4 for checked lowering to machine blocks/final bytes. Verified present in `OPTIMIZER.md` §§1.3/2/2.1, `DIRECT-COMPILER-DESIGN.md` §1 + chain diagram, `IR-VALIDIERUNG.md` alignment note + §§1.1–1.3/5.2/8.
2. No mandatory SSA or second executor: all `IRGraph`/`irRun`/`irWF` mentions in the candidate are explicit negations; `LowerMap`/§5.2 adapter shapes are labelled proposed validator checks, never a runner; `No irRun-style second executor` stated. No positive mandatory-SSA sentence found.
3. Friend handoff: `OPTIMIZER.md` §11 retargeted to typed source + accepted target interfaces (`SourceMemory` L1 rows, `Codec.decode`/`Byteschritt`/`Ausfuehrung.schritt`, TSO-bridge tables as they land). Reserved `OptimizationRules.lean`/`OptimizationWitnesses.lean` still absent in tree (verified), path-strings-not-links, untouched. Lane 287 recorded superseded (report-only, reviewer 303 ACCEPT); no `IR.lean` exists or is awaited.
4. Obligations preserved: -O3-like/invariant-derived scope, site-legality binding (actual site facts only; writer/held-section blackout; fast-math/atomics/MMIO/fault/cost default-refuse), faults/cost/budget/concurrency/entry/relocation/final-byte validation, `schluss_x86` takes NO independent refinement premise (`valX86_sound` derivation kept). Nothing deleted for simplicity; §12 change is vocabulary rename only.
5. No false closure: accepted rows (570 `SourceMemory` with `repOk`/`zahlWort`/`wortZahl`/`layoutOk`/`regionDisjunkt` verified in `SourceMemory.lean`; 559/560/568/569/571/572, 349 `valX86`, 567 `TSOHistory`) separated from OPEN gaps; TSO-to-GX refinement, budget/time transfer, FP/SIMD admission, full-source lowering, closing validator stay OPEN in all three CUTS. `ExpressionLowering` correctly absent (no such Lean file in tree). Explicit no-measured-speed disclaimers in all docs.
6. Names/links/lifecycle: `execStmt`/`execBlock` (`Semantik.lean`), `Codec.decode`/`Ausfuehrung.schritt`/`Byteschritt`, `valX86`, 82 X86 modules incl. `FlagBeweis.lean` (count matches doc claim exactly) all verified present. Scripted link check over all three candidate docs: 0 broken `.md`/`.lean` links. Stale `lanes/287.md`/`334.md` links removed (files confirmed deleted after integration). Decision doc and lifecycle reports `MUSE-REPORT-287/303/594/606` present in `messung/muse/`; 594/606 and 570/559/567/568/569/571/572 recorded merged in `DIRECT-COMPILER.md`.
7. Scope: PATCH touches only the 4 owned paths; no Lean/Rust/checker/emitter/build edits. `git apply --check` on the PATCH: clean. `git diff --check` in this lane: clean.

## Limitations / nits (not verdict-changing)

- Author report says lifecycle reports are "linked"; in the candidate they are named as text (lane 594/606/303) with only `DIRECT-LOWERING-DECISION.md` hyperlinked. All named reports exist; no dead link results.
- Author report says "20/20 module files" while the doc correctly states 82 modules; the doc is right (verified 82), the report line is stale.

## Build / verification

- Docs-only review: no Lean, Rust, checker or emitter file touched, so no `./lean-bau`, `./cargo-pruef` or `./emission-pruef` run is owed. No new definitions or theorems, no axioms, no CUTS obligation for this lane.
- New definitions/theorems: none.
