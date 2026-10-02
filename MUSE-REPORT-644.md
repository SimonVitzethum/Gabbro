# MUSE-REPORT-644: Organise the next generic source-to-final-byte closure wave

- Branch verified: `muse/644` in `/home/simon/Dokumente/gabbro-muse/a644`
  (`git rev-parse --show-toplevel` and `git branch --show-current`
  both confirm; working tree clean before writing).
- Owned paths only: `dokumente/x86/SOURCE-CLOSURE-PLAN-644.md` (new),
  `MUSE-REPORT-644.md` (this file). No Lean, checker, Spec, goal, Rust,
  emitter, ledger or control file touched; no umbrella import added.

## What was done

Wrote the organiser deliverable `dokumente/x86/SOURCE-CLOSURE-PLAN-644.md`:
a dependency/ownership plan for generic end-to-end validation after the
overnight source closures. Resolved every cited definition in this clone
before writing (no speculative names):

- Read `DIRECT-COMPILER.md` (ledger: 646/648/650/652/654/656 scheduled,
  658 waiting on dependencies, 575 candidate pending review, 570–574 and
  594–638 merged), `DIRECT-COMPILER-DESIGN.md` (§§2/2B/2C/3/5/7/7A/8),
  `grammatik/OPTIMIZER.md` (§§1–7, lane-638 alignment, no IR on the trust
  path), `dokumente/x86/QUELLBRUECKE.md` §4 (`valX86_sound` /
  `schluss_x86_aus_verfeinerung` / `schluss_x86` schema),
  `TARGET-PORTABILITY.md`, `DIRECT-LOWERING-DECISION.md`, and the
  558/605/401/638 plans and reports.
- Inspected the actual producer modules: 628 `SourceAssignmentLowering`
  (confirmed `senkAssign_korrekt` carries `hExec`/`hTgt`/`hRd` exactly as
  the task states, plus `hOk`/`hsenk`/`hrenv`/`hFr`/`hrsp`/`hBasis`/
  `hBaseR`/`hdisp`/`ha`), 599 `ExpressionLowering` (exists in this clone;
  note: lane-638 report predates its merge and says it was absent),
  634 `SourceCodeFrame`, 630 `SourceAccessCompleteness`, 598
  `ValidatorExecution`, 596 `TSOTrace`, 603 `WordAccessGrouping`
  (confirmed explicit void bridge `GruppeNachW`/`keine_gruppe_nach_w`),
  565 `ScalarFloatCodec`, plus 570 `SourceMemory`, 573/574 bridge legs,
  560 `LoadedExecution`, 568 `AccessExecution`, 349 `ValidatorSkeleton`.
- Plan contents: §1 fixes 632 as a fixed witness (`witD`/write-42/
  `bildStore`, `.p48`-pinned) and names its exact three-part replacement
  (full-unit computation, generic `valX86_sound`, derived `schluss_x86`);
  §2 lists verified stable producer interfaces with a reuse-not-fork
  rule; §3 itemises ten missing derived facts M1–M10; §4 separates model
  semantics/decoders from silicon fidelity; §5 describes O3/invariant
  certificate integration, validation-cost bounds, the untrusted-cache
  congruence rule, per-profile closure and named-assumption discipline
  (no numeric performance promise anywhere); §6 records in-flight-lane
  boundaries (646/648/650/652/654/656/658, 575-owned
  `ExtendedExecution.lean`); §7 gives eight follow-up tasks T-A–T-H with
  exact NEW paths, accepted-only dependencies, statement sketches,
  non-degenerate witness demands and refusals; §8 lists eight semantic
  rejection criteria; §9 gives launch order with the 654 double-gate
  stagger note.

## New definitions/theorems

None. Docs-only lane; no Lean file added or changed, so rule 13 needs no
witness and no `#print axioms` claim is made.

## Last build result

No `./lean-bau` run: this lane touches zero Lean files, so the baseline
build is unaffected and no new Lean build is claimed (per task: "no new
Lean build claim"). Verification actually run: `git diff --check` clean;
local-link check over the new document (all `.md` targets and all
`grammatik/Grammatik/X86/*.lean` targets resolved present in this
clone); new filenames in §7 checked absent from `grammatik/Grammatik/X86/`
at this base.

## What remains open

- Independent exact-candidate review of this plan (reviewer 645:
  owned-paths-only scope, no guarantee weakened, no planned-vs-accepted
  confusion, links resolve, at most eight tasks, no IR/second executor,
  no ledger/control edit).
- Everything the plan marks OPEN (M1–M10, T-A–T-H sketches, `valX86_sound`,
  per-access TSO→W/GX simulation, `f32` path decision, whole-image
  reachability).
- Coordinator re-check at launch: §7 filenames against 646–658 committed
  paths (their lane files name no Lean file), and T-D/T-F stagger on
  accepted 654.

## Task feedback

The task is sound as written. Two notes: (1) the "newly merged FP
codec565" merges after the lane-638 alignment report, which still says
`ExpressionLowering` is absent — both exist in this clone now, and the
plan cites only what it verified present; (2) 646–658 lane files name no
owned Lean file, so §7 collision-freedom is verified against the tree at
this base plus a coordinator re-check, not against their future paths.
