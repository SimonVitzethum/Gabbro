# MUSE-REPORT-638: Align optimiser and compiler design with accepted direct-source lowering

- Branch verified: `muse/638` in `/home/simon/Dokumente/gabbro-muse/a638`. Owned paths only: `grammatik/OPTIMIZER.md`, `DIRECT-COMPILER-DESIGN.md`, `dokumente/x86/IR-VALIDIERUNG.md`, `MUSE-REPORT-638.md`. Nothing else touched; `git status` shows exactly the three docs plus this report.

## What was done

Aligned the three owned design docs with the accepted direct lowering decision ([DIRECT-LOWERING-DECISION.md](dokumente/x86/DIRECT-LOWERING-DECISION.md), owner lane 594, independent reviewer lane 606, both merged):

1. Canonical reference is now everywhere the existing typed source AST with its execution (`Deklaration`, `Programm D`, `Expr`/`Stmt`/`Block`/`Endblock`, `World`/`Env`, `eval`/`execStmt`/`execBlock`/`execEnd`/`exec`) — the exact execution the goal theorem speaks about.
2. Direct checked lowering (decision contracts L1–L4) from source-anchored blocks to machine blocks/final bytes replaces every "shared/frozen typed IR" statement. No mandatory persistent SSA language or interpreter stands on the trust path: no `IRGraph`, no `irRun`, no trusted `irWF`.
3. Internal Rust CFG/SSA/analysis artefacts are documented as transient untrusted hints only — never trusted, never required proof-language stages. Validator-recomputed claims (dominators, availability, liveness, token threading, colouring maps) are what the validator decides.
4. Friend handoff (`OPTIMIZER.md` §11) now points at the existing typed source plus the accepted target interfaces (`SourceMemory` L1 rows, `Codec.decode`/`Byteschritt`/`Ausfuehrung.schritt`, per-access TSO-bridge tables as they land). Reserved `OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched (still absent, still path-strings-not-links). Lane 287 recorded as superseded (report-only, reviewer 303 ACCEPT, draft under ignored `.tmp/IR287-PRESERVED/`); no `IR.lean` exists or is awaited.
5. Rule-legality binding made explicit in both docs: a rule binds ONLY facts actually available at its site (source invariant at its guaranteed place with actual values, site effect/duty binding, actually-holding W/GX ordering). Entry ranges do not travel into a running writer's loop, quiescent invariants do not enter held sections, pre-call versions die at unknown-body calls. Fast-math, atomic-ordering, MMIO/device, fault-elision and cost-bypass families refuse by default regardless of invariants.
6. Preserved without deletion: full -O3-like/invariant-derived scope, safety gates, portability/freestanding summary, final loaded-image/entry/support-code/relocation/concurrency validation, fast-compilation-including-validation pipeline, refusal catalogue, ghost budget/event obligations.
7. Accepted-vs-planned separated with real names: `SourceMemory` (570), decoder soundness (559), loaded-image execution (560), realised footprints (568), stack execution (569), entry (571), budget/work (572), `ValidatorSkeleton` (349), `TSOHistory` (567) cited as the bounded implemented rows; TSO-to-GX refinement, budget/time transfer, FP/SIMD admission, full-source lowering and the closing validator stay OPEN.
8. Removed stale links: numeric lane task files `lanes/287.md`/`334.md` no longer exist (deleted after integration) and are no longer linked; decision doc and committed reports (`MUSE-REPORT-287/303/594/606`) linked instead.

Per-file edits:
- `grammatik/OPTIMIZER.md` (+109/−48 from prior turn, plus §11.5/§12/CUTS/link fixes this turn): header inspection note, §1.3 trust-path diagram, §2 reframed to source-anchored blocks, §1.4 exact-cuts with accepted rows, §4 site-legality binding paragraph, §10.5 dependency graph root, §11 friend handoff, O1/O3 obligation rows, CUTS.
- `DIRECT-COMPILER-DESIGN.md`: §1 trust chain + diagram, §3A selection subject, §7 register intro + legality sentence + `IR §6` cross-ref fix, §8 block-form bullet, §10 throughput metrics, §11 step 3, §12 portability sentence.
- `dokumente/x86/IR-VALIDIERUNG.md`: alignment header note, §1 title + §1.1/§1.2/§1.3 reframed (claim shape, not language), §2.4 `G0` wording, §5.1 `LowerMap` + §5.2 ownership table (proposed validator-adapter shapes, never a runner), §4.2 transfer-function soundness, §3-item-4 `bsem_bindCall` wording, §8 checklist bullets, CUTS.

No new Lean definitions, no new theorems, no new API or type alleged: every cited name was verified present in this clone (20/20 module files, decision doc, all four referenced reports). `ExpressionLowering` was checked and is NOT in the tree, so nothing in the docs claims it — per the task's "only if accepted".

## Build / verification

- Docs-only lane: no Lean, Rust, checker, emitter or build file touched, so no `./lean-bau`, `./lean-probe`, `./cargo-pruef` or `./emission-pruef` run is owed (task: "no fictitious Lean build for docs-only"). Baseline build state untouched. No new theorem, no new axiom, no `#print axioms` claim.
- `git diff --check`: clean.
- Local-link checks (scripted, all three docs): 0 broken `.md` links, 0 broken `.lean` links. All cited reports and modules confirmed present (see above).

## What remains open

- Independent exact-candidate review of this docs candidate (reviewer to verify: owned-paths-only scope, no guarantee weakened, no implemented-vs-planned confusion, links resolve).
- Everything in the docs' CUTS/OPEN registers, unchanged by this lane: validator adapter (`valX86 E bild`, `valX86_sound`, `schluss_x86`), L1 rows beyond accepted 570, L2 forms beyond the covered fragment, L3 entry/budget/stutter legs, L4 per-access TSO–W/GX simulation, LOCK/fence execution, vector correspondence, ghost-event and ghost-budget arguments, lane-278 timing bounds, full-`E` identity.
- Follow-up doc hygiene (not owned by this lane): `DIRECT-COMPILER.md` history recording of decision 594/606 belongs to the coordinator per the decision's §7.

## Anything believed wrong in the task

- Nothing wrong. One note: the task's "SourceMemory, ExpressionLowering only if accepted" is satisfied asymmetrically — `SourceMemory` is accepted and cited, `ExpressionLowering` does not exist in the tree and is therefore absent from all three docs. If a future lane accepts an expression-lowering module, the §1.4/§5 tables are the places to add it.
