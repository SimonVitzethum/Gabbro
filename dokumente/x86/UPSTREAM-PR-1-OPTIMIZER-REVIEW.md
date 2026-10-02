# Upstream PR 1 review: optimizer rule library (friend handoff)

Reviewer: lane 710. Candidate: PR 1 head `5d5a72e5889a3063b417b955fa7824e72c52ef7c`,
base `26c58bd41b2c6ad413b54c08c646c1313e4b297e`.
Reviewed from the pinned public copies in `.tmp/UPSTREAM-PRS/pr-1`
(`METADATA.json`, `PATCH.diff`, full source tree), not from a live branch.
No source, import, witness, test, semantics or PR-branch file was changed by
this lane. This document and `MUSE-REPORT-710.md` are the lane's only outputs.

## 1. What the PR contains

Four files (`PATCH.diff`, 2162 lines):

| File | Change |
|---|---|
| `grammatik/Grammatik/X86/OptimizationRules.lean` (new, 1302 lines) | certificates, executable validators, generic soundness theorems |
| `grammatik/Grammatik/X86/OptimizationWitnesses.lean` (new, 615 lines) | joint `_zeuge` witnesses, positive and poison probes |
| `grammatik/Grammatik.lean` | two import lines only |
| `grammatik/OPTIMIZER.md` | status updates plus new honest-scope section 13 |

No Rust, no `Spec.lean`, no goal-theorem, no emitter/CLI file is touched.
PR 2 (`987b286df9d8465714a00bab8226f7b9c7f4afc1`) declares PR 1's head as its
base, so PR 2 stacks on this delivery; merge order must respect that.

The two Lean files are the friend-reserved paths. This PR is the friend
handoff and is reviewed here under the user's explicit review/repair/merge
request, which is the only basis on which the reservation is lifted.

## 2. How it was checked

- Read both new files in full, plus the complete `OPTIMIZER.md` diff.
- Checked the constant evaluator against the real operations in
  `grammatik/Grammatik/Typen.lean` (`Zahl.add/sub/neg/mul/div/rem/sdiv/srem/
  band/bor/bxor/shl/shr/weiter`): every `constInt?` arm uses exactly the
  operation `eval` uses, including the `toNat` bitwise/shift treatment.
- Checked the zero-divisor boundary: `Zahl.div` requires `1 <= l2` and
  `Zahl.sdiv`/`srem` require a zero-excluding divisor range, so a
  well-typed divisor can never evaluate to zero; folding `div`/`sdiv` as a
  value is total. An uninhabited shape (constant zero at a `1 <= l2` type)
  cannot be built because the widening proof would be false.
- Checked read-event exactness: `ExprEquiv` requires `orte` equality, not
  just value equality; `foldInt` goes through `constInt?_orte`, `foldBool`
  and `dropCheckOk` require `orte.isEmpty`. A range-decided comparison over
  a slot stays refused (poison probes `foldBool_refuses_read`,
  `dropCheck_refuses_read`).
- Checked the signed/overflow boundaries: `checkStrength` matches only
  unsigned `mul`/`div`/`rem`; `sdiv`/`srem` are refused by construction
  (`checkStrength_sdiv/srem`, proved `= none` by `rfl`). Product bounds use
  the type maximum (`h1 * 2^k < 2^64`), the shifted operand is nonnegative
  by type, division/remainder additionally require `h1 < 2^64`, the mask
  requires `k <= 64`. Both product orders are handled; division/remainder
  accept only a constant divisor.
- Checked recursion coverage: `applyStmt`/`applyBlock` descend into `ite`
  branches, `locks`/`breaking` bodies, both `onOption` branches,
  `traverse`/`retry`/`forever` bodies, the `retry` condition and overflow
  block, and expression positions of `ite`/`assignSlot`/`assignVar`/
  `assignGlob`/`pruefung`/`bind`/`narrow`. `on tag`/`on reason` arms, other
  call binders, register/float binders, `exchange`/`awaits` and loop
  invariants are unreachable (refused, never trusted); the CUTS text and
  section 13.5 say so explicitly.
- Checked for trusted values and circular premises: certificates carry only
  rule names, paths and the shift count `k`; every fact (`constInt?`,
  `bounds`, `decide*`, range entailment, `2^k` equality) is recomputed from
  the source text. The shift count is validated because acceptance requires
  `constInt? b = some (2^k)`. Each validator has one derived soundness
  theorem; no desired equivalence is assumed. `refl`/`trans` are the only
  structural lemmas.
- Textual gate scan of both files: 0 `sorry`, 0 `axiom` declarations, 0
  `native_decide`, 0 `unsafe`, 0 `intro _`, 0 `have _ :=`, 0 `forall rho`
  contract-away quantification. (`admit` grep hits are the identifier
  `admittedOrder`; `: Prop` hits are the `*Equiv` conclusion types.)
- Reproduced on a disposable fixture (`.tmp/fix-pr1`, ignored scratch):
  exact candidate `grammatik/` tree plus copied queued wrappers and a copy
  of this clone's warm `grammatik/.lake`, using only `./lean-probe` and the
  queued `lean-slot lake build` path. Full logs are in section 4.

## 3. Findings

### MUST-FIX: none found

No present bug, no counterexample, no hidden trusted value, no circular
premise and no weakened guarantee was found. The refusal set covers every
boundary the task named: signed division/remainder, non-power-of-two
multipliers, possibly-negative or wrapping operands in both product orders,
variable divisors, over-wide masks/dividends, wrong shift counts, reads that
would vanish from the trace, undecided and always-failing checks, unentailed
`narrow`s, float conditions, wrong-type and wrong-path certificates, and
out-of-order or mislabelled pipelines. Each is a `decide`/`rfl` computation.

### Scope clarifications (not bugs)

1. Strength reduction certifies a target *word fact* (`TargetOp.run` on the
   `SourceMemory.zahlWort` encoding equals the source value), not a
   source-to-source rewrite and not encoded bytes. It is deliberately not
   wired into `BlockCert`/`applyPipeline`; a lowering consumer must invoke
   `checkStrength` directly. The PR-body phrase "`x * 2^k` ... mapped to
   shift" overstates this one step; `OPTIMIZER.md` section 13.5 states the
   honest boundary (bytes/registers/image stay with lowering lanes).
2. `BlockEquiv`/`StmtEquiv` are exact single-thread `Ausgang` equalities
   (world, trace, environment, returns, reasons, `logik` stops including
   budget refusal). Section 13.2 honestly records that a removed check
   removes a machine-G step, so the G/GX (concurrency, time, call-log)
   transfer stays OPEN. Nothing in the PR claims otherwise.
3. Generic quantification is over every *typed* source program
   (`Expr`/`Stmt`/`Block` with `eval`/`execStmt`/`execBlock`). The
   parser-text-to-AST bridge and the Rust certificate producer remain open;
   section 13.5 says there is no Rust (Lean-first order respected).
4. `foldInt`'s out-of-range refusal branch is unreachable for a sound
   `constInt?` and is documented as such; no probe can exercise it. Kept as
   a recomputed check, correctly.
5. `breaking` has no dedicated witness (`InvariantenOpt.wD` declares no
   invariant to build one over); the arm is covered by generic
   `applyStmt_sound` only. The witness file's CUTS says this plainly.

### Not independently reproduced

- The `lean -M 16384` claim that `ElementTiefProben.lean` compiles with a
  larger heap was not reproduced (heavyweight, and orthogonal to this PR).
  What *was* reproduced: the file fails identically with and without the PR
  (section 4).
- Full `lake build` was not run in the fixture; the two new modules plus
  the baseline-failure comparison cover the PR's build claim at the only
  points where this 4-file diff can affect it (new modules build; nothing
  else in the tree changes; the umbrella adds two import lines).

## 4. Reproduced build evidence

Fixture `.tmp/fix-pr1/grammatik` (exact candidate tree) with copied warm
`.lake`, own clone at `011ff474004a8a617338584d68b13a64c87b1051`:

- `./lean-probe OptimizationRules.lean`: `== 0 error(s) ..., exit 0`.
  All 21 `#print axioms` lines list subsets of
  `[propext, Classical.choice, Quot.sound]` (several list fewer).
  `lake build Grammatik.X86.OptimizationRules`: `Build completed
  successfully (63 jobs)`.
- `./lean-probe OptimizationWitnesses.lean` (after building the rules
  module): `== 0 error(s) ..., exit 0`. All axiom reports are subsets of
  the three standard axioms; probes depending only on computation list
  `[propext]`.
- Baseline comparison for the reported pre-existing failure:
  own master `grammatik/Grammatik/Parser/ElementTiefProben.lean` via
  `./lean-probe` fails with `526:8: error: (kernel) excessive memory
  consumption detected` and `1176:8` under `-M4096`; the fixture's copy of
  the same file fails at exactly the same two lines with the same error.
  The "also fails on master" statement is therefore confirmed, not taken
  on trust.
- Own clone `./lean-bau` after this lane's work (review docs only):
  `== exit 0; 0 error line(s) in the COMPLETE output`.

## 5. Merge recommendation

From this reviewer: **accept** — no must-fix issue, honestly scoped, all
mechanical gates reproduced (build green on the candidate modules,
standard axioms only, no forbidden tactics/axioms, non-degenerate joint
witnesses with memory-changing runs over a table the contract writes,
poison probes by computation). Merging remains the coordinator's serial,
checked integration path: exact-candidate review pairing, `./lean-bau`,
test/emission/key gates and publication rules still apply, and PR 2 (which
stacks on this head) must be ordered after it. This lane performs no merge
itself.
