# Muse report 710: optimizer PR 1 proof and scope review

Lane 710, clone `/home/simon/Dokumente/gabbro-muse/a710`, branch `muse/710`
(verified before starting). Owned files only:
`dokumente/x86/UPSTREAM-PR-1-OPTIMIZER-REVIEW.md` (the review) and this
report. No source, import, witness, test, semantics or PR-branch file was
changed.

## What was done

Reviewed pinned upstream PR 1 (`5d5a72e5889a3063b417b955fa7824e72c52ef7c`,
base `26c58bd4`) from the public pinned copies in `.tmp/UPSTREAM-PRS/pr-1`.
Read `OptimizationRules.lean` (1302 lines, 35 theorems, 36 defs) and
`OptimizationWitnesses.lean` (615 lines) in full, the complete
`OPTIMIZER.md` diff including the new honest-scope section 13, and checked
the constant evaluator arm-by-arm against the real `Zahl` operations in
`grammatik/Grammatik/Typen.lean`. Verified the zero-divisor boundary is
excluded by types (`Zahl.div` needs `1 <= l2`), read-event exactness
(`ExprEquiv` carries `orte` equality; `foldBool`/`dropCheckOk` require empty
`orte`), signed/overflow refusals, recursion coverage and its documented
gaps, certificate-shape (no trusted values) and the absence of circular
equivalence premises. Textual gate scan: 0 `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
(`admit` hits are `admittedOrder`; `: Prop` hits are `*Equiv` conclusions).

## Reproduced evidence (disposable fixture `.tmp/fix-pr1`, since removed)

- `./lean-probe OptimizationRules.lean`: 0 errors, exit 0; all axiom
  reports are subsets of `[propext, Classical.choice, Quot.sound]`.
- `lake build Grammatik.X86.OptimizationRules` via the queued slot:
  `Build completed successfully (63 jobs)`.
- `./lean-probe OptimizationWitnesses.lean`: 0 errors, exit 0; same
  standard-axiom result; computation-only probes list `[propext]`.
- Baseline check, not taken on trust: `Parser/ElementTiefProben.lean`
  fails identically (lines 526 and 1176, kernel excessive memory under
  `-M4096`) on own master and on the candidate tree.
- Own `./lean-bau` after this lane's doc-only work:
  `== exit 0; 0 error line(s) in the COMPLETE output`.

## Verdict

MUST-FIX: none. The delivery is honestly scoped (single-thread exact
`Ausgang` refinement; G/GX, time, bytes/image, parser and Rust bridges
explicitly open), witnesses are non-degenerate (table written by contract,
slot `0 -> 5` runs, loop/retry/option paths), and every named boundary has
a computational poison probe. Two scope notes for consumers: strength
reduction certifies a word fact and is not wired into `applyPipeline`;
the PR body's "mapped to shift" phrasing overstates this by one step
(`OPTIMIZER.md` 13.5 is honest). Reviewer recommendation: accept; merge
via the coordinator's serial checked integration, ordered before PR 2
(which stacks on this head). This lane merges nothing.

## New definitions/theorems by this lane

None. Review-only lane; no Lean code added, so no `_zeuge` obligation
arises.

## Open / not reproduced

- `lean -M 16384` compiling `ElementTiefProben.lean` (orthogonal to PR 1).
- Full fixture `lake build` (covered at every point this 4-file diff can
  affect: new modules green, nothing else changed, baseline failure
  identical).
- PR 2 review is separate work; noted only its base dependency on PR 1.
