# MUSE-REPORT-712: Compiler pipeline Lean source-to-byte proof review

Clone `/home/simon/Dokumente/gabbro-muse/a712`, branch `muse/712` (verified at start;
`git status` clean throughout; no Lean sources touched).
Owned deliverable: `dokumente/x86/UPSTREAM-PR-2-LEAN-REVIEW.md` (this lane's only
content commit besides this report). Task scope: evaluate upstream PR1 (optimiser
premises) + PR2 (pinned `987b286df9d8465714a00bab8226f7b9c7f4afc1`), covering
ExpressionLoweringDeep / Pipeline / PipelineImage / PipelineEntry + witnesses.

## What I did

1. Verified clone/branch, read the full lane task, both METADATA.json bodies, and
   confirmed PR2 head/base hashes and PATCH scope (27 files: 18 new X86 Lean files,
   `Grammatik.lean` imports, 8 Rust x86 files; no Spec/goal/emitter/CLI).
2. Read all four closing modules + three witness files end to end at statement level:
   closing-theorem quantifier order, `validate` recomputation (`validate_sound`),
   register/displacement/prologue/image/entry checks, refusal-stub theorems,
   witness joint instantiation.
3. Read PR1 `OptimizationRules.lean` premises (`BlockEquiv`, certificate
   recomputation, strength-reduction refusals, pass order) and the ISA/Compact/
   IntegerCore/Select/Relax libraries with their CUTS.
4. Mechanical greps over the exact snapshot: forbidden tactics (word-boundary, minus
   comments), CUTS + `#print axioms` coverage per file, duplicate top-level names
   (namespace-aware), Rust `#[test]` counts.
5. Built the exact PR2 `grammatik/` snapshot in a disposable fixture tree
   (`.tmp/fixture-pr2`, ignored SSD scratch; copied wrappers + clone-local warm
   `.lake`) through the queued `./lean-bau`. Result: `== exit 1; 3 error line(s)`.

## Findings (details + exact locations in the review document)

- BLOCKING 1: duplicate `Gabbro.Grammatik.X86.waehle` — `FeatureProfile.lean:72`
  (pre-existing) vs new `ISASelect.lean:703`. Aggregator fails:
  `import Grammatik.X86.ISASelect failed, environment already contains ...`.
- BLOCKING 2: duplicate `Gabbro.Grammatik.X86.layoutOk` — `TableLayout.lean:80`
  vs new `ISARelax.lean:132` (masked behind finding 1). Both renames are contained
  to the two new files + their witnesses; no proof content changes.
- BLOCKING 3 (process): the PR body's "How to test" (per-module builds) cannot catch
  aggregation collisions — all 475 dependency modules build green standalone — and
  its full-build claim ("fails only in ElementTiefProben") is contradicted by the
  fixture result. Merge gate must be the full build.
- Wording MUST-FIX 4–9: straight-line qualifier for the placed-code theorem;
  compact-equivalence boundaries (jumpIf8 taken-only, AND/OR excluded); explicit
  statement that ISA/Compact/IntegerCore/Select/Relax are proved but NOT on the
  verified pilot-`Befehl` path; stub sentence belongs to `pipeline_refuses_loaded`/
  `_compiled`, not block-level `pipeline_refuses`; one mislabeled docstring
  (`senkTief_tief_ok`); axiom-report count drift (907 claimed vs 948 prints).
- No soundness-breaking proof bug found. Witnesses are genuinely non-vacuous
  (joint premises, 7→35 / 9→6 memory change, necessity of the fold proved).
  Rust is correctly out of the trust path (137 `#[test]` counted, matches claim).

## New definitions/theorems by this lane

None. Review-only lane; no Lean code added or modified, no witnesses required.

## Build results

- Fixture (exact PR2 tree): `./lean-bau` → `== exit 1; 3 error line(s) in the
  COMPLETE output`, 475/476 jobs green, `Grammatik` aggregator red (findings 1–2).
  Full log: `.tmp/fixture-pr2/lean-bau-pr2.log` (ignored scratch, not committed).
- Own clone `grammatik/`: untouched (`git status` clean for all tracked files), so
  no Lean regression possible from this lane; no `./lean-bau` run needed in-clone
  (docs-only commit). Fixture tree left in ignored scratch for the repair lane.

## What remains open / what I believe is wrong

- The two renames + wording fixes belong to the PR authors (or a repair lane with
  merge rights); I own only the review document and must not touch PR branches.
- Re-verify after repair with the FULL `lake build`, and re-count the axiom reports.
- Open obligations listed in review §9 (unified-ISA wiring, branch-target layout
  theorem, concurrency/time, wider fragment, silicon correspondence, proved Rust
  equality, real-loader ELF) are future work, not covered by either PR.
