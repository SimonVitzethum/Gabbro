# Muse report 711: exact review of candidate 710 (optimizer PR-1 audit)

Lane 711, clone `/home/simon/Dokumente/gabbro-muse/a711`, branch `muse/711`
(verified: `git rev-parse --abbrev-ref HEAD` = `muse/711`). Report-only
review lane. Owned file: this report only. No source, import, witness, test,
semantics or PR-branch file was changed.

## Candidate and verdict

CANDIDATE: 710, pinned HEAD `7c9ac116a9a764139a82c164370c6813d53db0bc`
(doc-only lane: `dokumente/x86/UPSTREAM-PR-1-OPTIMIZER-REVIEW.md` +
`MUSE-REPORT-710.md`), reviewing upstream PR 1 head
`5d5a72e5889a3063b417b955fa7824e72c52ef7c` (base `26c58bd4`)
from the pinned public copies in `.tmp/UPSTREAM-PRS/pr-1`
(`METADATA.json`, `PATCH.diff`, full source tree).

VERDICT: ACCEPT.

The author audit is accurate on every checkable claim. No MUST-FIX issue
was found; no audit statement needed correction beyond immaterial drift
noted below. ACCEPT means the audit is accurate; it does not merge PR 1
itself (serial checked integration remains the coordinator's path, ordered
before PR 2 which stacks on PR 1's head).

## What was independently checked

- Read the full review document (160 lines), the author report (63 lines),
  the author PATCH (2 files, doc-only: confirmed via `diff --git` list),
  and the PR-1 `PATCH.diff` (102651 bytes, 4 files).
- Read `OptimizationRules.lean` (1302 lines, confirmed) and
  `OptimizationWitnesses.lean` (615 lines, confirmed) in the pinned tree:
  `Grammatik.lean` hunk is two import lines only; `OPTIMIZER.md` gains
  honest-scope section 13 (`## 13`, `### 13.1`--`13.5` present).
- Gate scans on both pinned files: 0 `sorry`, 0 `axiom` declarations,
  0 `native_decide`, 0 `unsafe`, 0 `intro _`, 0 `have _ :=`,
  0 `forall rho`; `admit` hits are only `admittedOrder`; no `(h : Prop)`
  premise. Matches the audit.
- Constant evaluator: all `constInt?` arms use the same operations
  `eval` uses (`Zahl.add/sub/mul/div/rem/sdiv/srem/band/bor/bxor/shl/shr/
  neg/weiter`, with `toNat` bitwise/shift treatment); soundness proofs
  cite exactly these. `Zahl.div` requires `1 <= l2`, `sdiv`/`srem`
  require `1 <= l2 \/ h2 <= -1`, so the zero-divisor boundary is excluded
  by types as claimed.
- Read-event exactness: `ExprEquiv` carries `orte` equality; `foldBool`
  and `dropCheckOk` require empty `orte`; `foldInt` goes through
  `constInt?_orte`. Poison probes `foldBool_refuses_read`,
  `dropCheck_refuses_read` are `decide` computations over a slot read.
- Strength reduction: `checkStrength` matches only unsigned
  `mul`/`div`/`rem`; `checkStrength_sdiv`/`_srem` are proved `= none` by
  `rfl`. Bounds are as stated (`h1 * 2^k < 2^64`, `h1 < 2^64`,
  `k <= 64`, constant `2^k` validated by `constInt?`, both product orders,
  divisor never commuted). Confirmed in source lines 548--720.
- Recursion: `StmtCert`/`BlockCert` descend into `ite` cond/branches,
  `locks`/`breaking` bodies, both `onOption` branches,
  `traverse`/`retry`/`forever` bodies, `retry` cond/body/overflow, and the
  stated expression positions; `on tag`/`on reason` arms, other call
  binders, register/float binders, `exchange`/`awaits` and loop invariants
  are refused by the catch-all `none` arm. The CUTS block states exactly
  this. Confirmed.
- Scope honesty: `BlockEquiv`/`StmtEquiv` are single-thread `Ausgang`
  equalities with an explicit G/GX-open paragraph in the definition
  comment; strength reduction certifies a `TargetOp.run` word fact on
  `SourceMemory.zahlWort` and is not wired into `BlockCert`/
  `applyPipeline` (audit clarification 1 confirmed, including the noted
  PR-body overstatement); parser/Rust bridges open per section 13.5;
  `foldInt` out-of-range branch documented unreachable; `breaking` gap
  documented in the witness CUTS (line 540).
- Witnesses: joint `_zeuge` pattern confirmed (64 `_zeuge` hits);
  `pipeline_zeuge` conjoins acceptance, soundness instantiation, a
  memory-changing run (`wP_run`: slot `0 -> 5`, `wWorld0_slot`,
  `wit_schreibt`), i.e. non-degenerate. Loop/retry/option paths witnessed
  (`wL_run`, `retry_accepts`, `optNone_zeuge`).

## Reproduced build evidence (disposable fixture `.tmp/fix-711`, removed)

Exact candidate `grammatik/` tree + copied queued wrappers + warm
clone-local `.lake`, only `./lean-probe` and queued `lean-slot lake build`:

- `./lean-probe OptimizationRules.lean`: `== 0 error(s) ..., exit 0`;
  all 21 `#print axioms` lines are subsets of
  `[propext, Classical.choice, Quot.sound]`.
- `lake build Grammatik.X86.OptimizationRules`:
  `Build completed successfully (63 jobs)`.
- `./lean-probe OptimizationWitnesses.lean`: `== 0 error(s) ..., exit 0`;
  67 axiom lines, all standard subsets, computation-only probes `[propext]`.
- Baseline: `Parser/ElementTiefProben.lean` still fails on current master
  without the PR (pre-existing, not PR-caused). Line-number note: this
  clone's master (`c3400beb`) fails at 1 line (1176); the pinned old-base
  candidate tree fails at 5 lines (530/778/797/862/1176); the author's own
  master (`011ff474`) failed at 2 lines (526/1176) identically with and
  without the PR. The drift is base age (same 1298-line file, shifted
  content); the PR does not touch that file, so no conclusion of the audit
  changes. The author's "identical on master" comparison was against its
  contemporaneous base and is not contradicted.

## New definitions/theorems by this lane

None. Review-only lane; no Lean code added, so no `_zeuge` obligation arises.

## Open / not reproduced

- `lean -M 16384` compiling `ElementTiefProben.lean` (orthogonal to PR 1).
- Full fixture `lake build` (covered at every point this 4-file diff can
  affect: new modules green, nothing else changed, baseline failure
  pre-existing).
- PR 2 (`987b286d`) is separate work; noted only its base dependency on PR 1.
- Own `./lean-bau` was not rerun after doc-only work (no tree files
  changed; `git status` clean except this report); fixture probes above
  are the build evidence for this lane.
