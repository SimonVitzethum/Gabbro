# MUSE-REPORT-606: Independent exact-candidate review of 594

- Branch verified: `muse/606` in `/home/simon/Dokumente/gabbro-muse/a606`. Owned path only: `MUSE-REPORT-606.md`. No other file touched; no Lean import added; no source change.

## Candidate

CANDIDATE: 594 0e2ab45ca124cbdfe31795587dfdcd84c2ac425c

Reviewed from the exact frozen snapshot in `.tmp/review/author-594/` (SNAPSHOT.json pins head `0e2ab45c`, base `0044c258`, files `MUSE-REPORT-594.md` + `dokumente/x86/DIRECT-LOWERING-DECISION.md`, clean tree). PATCH.diff confirms the candidate adds exactly those two new docs files and touches nothing else: no Lean, no Rust, no checker/Spec/goal, no friend-reserved optimiser files, no Lean import change.

## Verification performed

- Reference spot-checks against this clone (at merge `377b290e`, which contains base `0044c258` plus merges of 570/588): `Syntax.lean` `Deklaration` (114), `Expr` (342), `Stmt` (455), `Block` (533); `Typen.lean` `Ty` (35); `Semantik.lean` `World` (79), `eval` (214), `execStmt` (699), `execBlock` (788), `execEnd` (880), `exec` (952); `World.schreibSlot` present and used by the assign arms; `Body.lean` `Stmt` (966), `exec` (1357); `Quelle.lean` `nutzer_aus_quelle` (144), `nutzerA_aus_quelle` (156); `QUELLBRUECKE.md` refusal list (`assignB`, `assignTabB`, locks, `alt`/`erg` outside `ensures`) and `valX86_sound`/`schluss_x86` schema; accepted `X86/SourceMemory.lean` (`zahlWort`/`wortZahl`, `zahlWort_wortZahl`, `repOk`, `repOk_klingt`); committed `IR-VALIDIERUNG.md`, `QUELLBRUECKE.md`, `CONNECTION-PLAN.md` all present. All cited names exist at the cited lines (modulo blank-line drift of at most the doc's own approximations, which I confirmed exact above).
- The `axiom` string match in the decision is prose ("No new IR, interpreter, or axiom is created"), not a Lean axiom. No `sorry`/`admit`/`native_decide`; no new theorem so no `#print axioms` is owed. No OS names (Linux/POSIX/libc/ELF) in the document; OS/binding contracts are correctly placed as user logic, silicon/timing as the only named hardware premises.
- IR287 snapshot content itself could not be independently verified (private snapshot lives only in the author's clone, correctly never copied here), but the decision adopts nothing from it, so acceptance does not depend on its characterization.

## Findings

1. The core recommendation is sound and correctly argued from real code: candidate A (typed `Syntax` + `exec`, the goal theorem's own semantics) as the single source representation; `Body` + bridge kept as the duty-statement path for premise (b) only (its refusal of exactly the backend-relevant constructs is confirmed in `QUELLBRUECKE.md`); no persistent SSA IR. The five-criterion table is concrete, and the negative-proof-reuse argument for a second executor (`irRun` duplicating `exec`, plus `irWF` soundness and two correspondences) is valid.
2. No guarantee is weakened: the closing shape (`schluss_x86` with derived `valX86_sound`) is unchanged, the lowering leg is stated directly source-to-bytes, optimisation certificates stay in the untrusted middle arrow per `IR-VALIDIERUNG.md`, friend-reserved files untouched, and the `narrow` guard is kept loud. The L1–L4 contracts name real producer definitions and real refusal surfaces.
3. CUTS (§8) are precise and honest: the document proves nothing and lists every open leg (validator adapter, L1 rows, L2 forms, L3/L4, LOCK/fence, vectors, ghost events/budget, timing bounds, full-`E` identity). Success criteria for follow-ups correctly demand joint memory-changing witnesses, planted refusals, and standard axioms.
4. Ownership and migration plan is useful and disjoint: IR287 finishes under reviewer 303 on its own terms with no silent re-fork; reusable algorithms migrate as untrusted guidance only; four follow-up tasks (validator adapter, L1 width, L2 form, 573/574 per-access legs) with no overlapping writers of the representation interface.
5. Out-of-scope criteria from the lane prompt are correctly not applicable: Tools595 (no tool change in candidate), Rust618 (no Rust change, no verdict touched), Docs604/605 (not in this snapshot). Nothing in the decision constrains or pre-judges them.
6. Minor notes, not acceptance-blocking: (a) the "actual AST->instruction-block lowering contracts" requested by the owner task are delivered as checked relations L1–L4 rather than a fixed block syntax — the report explains why (a pinned syntax would recreate the IR fork), and I agree; (b) `Typen.lean:35` omits the `Grammatik/` path prefix used elsewhere, trivial.

## Verdict

VERDICT: ACCEPT

Bounded accepted scope: exactly the two new docs files at the pinned HEAD — `dokumente/x86/DIRECT-LOWERING-DECISION.md` (architecture decision, proposal status until the coordinator records it in `DIRECT-COMPILER.md`) and `MUSE-REPORT-594.md`. No Lean/Rust/build claim accepted; no `IR.lean` created or adopted; follow-up compiler tasks are to cite §§3–6 of the decision once the coordinator records it.

## Build evidence

Not run (docs-only review; this lane adds no Lean or Rust code and the candidate adds none either — baseline untouched, `git status` clean except this owned report). No new theorem, no new axiom, no `#print axioms` claim.
