# MUSE-REPORT-594: Architecture decision, existing source model versus additional SSA

- Branch verified: `muse/594` in `/home/simon/Dokumente/gabbro-muse/a594`. Owned paths only: `dokumente/x86/DIRECT-LOWERING-DECISION.md`, `MUSE-REPORT-594.md`. No other file touched; no Lean import added; no source change.

## What was done

- Wrote `dokumente/x86/DIRECT-LOWERING-DECISION.md` (docs-only architecture decision for reviewer 606).
- Read from real code in this clone at base `0044c258`: `grammatik/Grammatik/Syntax.lean` (`Deklaration`, `Expr`, `Stmt`, `Block`), `grammatik/Grammatik/Semantik.lean` (`World`, `eval`, `execStmt:699`, `execBlock:788`, `execEnd:880`, `exec:952`), `programmlogik/Gabbro/Body.lean` (`Value`, `Stmt:966`, `exec:1357`), `bruecke/Bruecke/Quelle.lean` (`nutzer_aus_quelle`, `nutzerA_aus_quelle`), committed docs `dokumente/x86/IR-VALIDIERUNG.md`, `QUELLBRUECKE.md`, `CONNECTION-PLAN.md`.
- Read the supplied private snapshots only (never another clone): `.tmp/overnight-context/IR287-DRAFT.lean` (IROrd/IRSort/IROp/IRPhi/IRTerm/IRBlock/IRGraph/IRState, irStepOp/irStepBlock/irRun, irWF/domSets, FragE/FragS/FragB, lowerE/lowerB/lowerGraph) and `.tmp/overnight-context/SourceMemory570-CANDIDATE.lean` (zahlWort/wortZahl, zahlWort_wortZahl, repOk/repOk_klingt, TableLayout/Speicher/Regionen reuse).

## Decision (proposal for review)

- Recommended: the existing typed source model (`Syntax` + `exec`, candidate A) is the single reusable source representation. No persistent SSA IR. `Body` plus its bridge stays the duty-statement path for premise (b) only, not a compiler input. The IR287 draft is preserved as design input, not committed as `IR.lean`; its interpreter (`irRun`), trusted WF (`irWF`), and `Frag*` datatypes are not adopted.
- Lowering is specified as checked relations L1–L4 in the decision: L1 representation admission (`repOk` + `layoutOk`/`regionDisjunkt` + value roundtrips), L2 statement lowering (source-anchored blocks via `execStmt`/`World.schreibSlot` to `Codec.decode`/`Byteschritt`/`Ausfuehrung.schritt` bytes), L3 control/entries/stops (relocations with re-decoding, stack proofs, full-`E` identity, stutter/progress), L4 per-access TSO-to-W/GX simulation. CFG/dataflow/register facts are validator-recomputed claims, never trusted hints. Friend-reserved optimiser files untouched. Removing the SSA stage removes no source-to-bytes proof obligation (`schluss_x86`/`valX86_sound` shape unchanged, lowering leg stated directly).
- Deliverables in the decision: five-criterion comparison table, L1–L4 contracts with real definition names, validator analysis requirements and refusal surface, producer/consumer table, first implementable fragment (one more L1 width/object + one more L2 statement form through the 568 realised-footprint pattern), and the IR287/optimiser-friend migration and ownership plan.

## Build / verification

- No Lean or Rust change was made, so no `./lean-bau`, `./lean-probe`, `./cargo-pruef`, or `./emission-pruef` run is owed by this docs task; the baseline build is untouched. No new theorem, no new axiom, no `#print axioms` claim. No Lean build-result line to report beyond "not run (docs-only, baseline untouched)".

## What remains open

- Review by lane 606 against the exact candidate; coordinator recording in `DIRECT-COMPILER.md` on acceptance (not done by this lane).
- Everything in the decision's CUTS: validator adapter (`valX86 E bild`, `valX86_sound`, `schluss_x86`), L1 rows beyond accepted 570, L2 forms beyond the covered fragment, L3/L4 legs, LOCK/fence execution, vector correspondence, ghost-event and ghost-budget arguments, lane-278 timing bounds, full-source unit computation beyond `einheitAllg` defaults.

## Anything believed wrong in the task

- Nothing wrong. One note: the lane prompt's "actual AST->instruction-block lowering contracts" is delivered as checked relations (L1–L4) rather than a fixed block syntax, deliberately — fixing a block syntax now would recreate the IR fork this decision rejects. If Simon wants a pinned block vocabulary file later, it should enter as a validator-adapter proposal citing this decision, not as a second `IR.lean`.
