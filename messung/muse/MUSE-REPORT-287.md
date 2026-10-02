# MUSE-REPORT-287 — single typed IR lane: superseded draft, preserved

Lane 287 (`muse/287`, model opencode-go/muse-spark-1.3-contributor).
Task: one typed IR + source-linked lowering foundation (`grammatik/Grammatik/X86/IR.lean`).

## 0. Outcome up front

The merged architecture decision 594 (reviewer 606) selects existing
typed `Syntax`/`exec` directly and **rejects introducing `IR.lean` or
another source interpreter**. This lane therefore delivers **no source
file**: per the follow-up instruction, every IR draft is preserved
unchanged under ignored `.tmp/IR287-PRESERVED/`, all unstaged IR
sources were removed from `grammatik/`, and my one-line umbrella
import in `grammatik/Grammatik.lean` was reverted. Final tree state is
exactly committed master plus this report. **No compiler was built, no
bytes were validated, no full-language claim is made anywhere below.**

Last `./lean-bau` result line (restored tree, no IR sources):
`Build completed successfully (368 jobs).`

## 1. Preserved drafts (exact paths, all under ignored `.tmp/`)

| Path (in this clone) | Content | Size | Final measured state |
|---|---|---|---|
| `.tmp/IR287-PRESERVED/IR.lean` | Full IR draft (representation, lowering, `ecorrW` proof, witness scene, `lowerE_mono`, unfinished `lowerB_mono`) | 2689 lines, md5 `892abbf1962919b74f0625d647a4bbb0` | `./lean-probe`: **6 errors**, all inside `lowerB_mono` (parse-level, see §5) |
| `.tmp/IR287-PRESERVED/Bis287.lean` | Early subset snapshot (defs through `fitVal_weiter` era, no `ecorrW`) | 1581 lines, md5 `f56d11ef8126b0616e2a345a240bcbba` | superseded snapshot, kept for archaeology |
| `.tmp/IR287-PRESERVED/Tmp287.lean` | Mini-family scratch (`Mini`, `lowerStub`, `reproE`, `hlow_idiom`, `storeSlot_same_*` probes) | 120 lines, md5 `77855458a919d7bb08dcaf14d0fb65e9` | scratch, green at time of use |

Further session scratch (already ignored, left in place, not deleted):
`.tmp/scratch_var*.lean`, `.tmp/scratch_mut/mt/nest/om/ds/rec/rec2/xd/fit.lean`,
`.tmp/probe_*.lean`, `.tmp/BisB-backup.lean`, `.tmp/ecorrW-block.txt`,
`.tmp/newmono.txt`, `.tmp/newmono2.txt`, `.tmp/*_out.txt`, `.tmp/probe_full.txt`.

No file contains `sorry`, `admit`, `axiom`, or `native_decide`
(verified by grep over the preserved `IR.lean`: 0 hits each).

## 2. What was built (preserved draft content)

Single typed SSA/CFG IR reusing real source types (`Deklaration`,
`Ty`, `Wert`, `World`, `Env`, `Zahl`; canonical target widths; no
independent source semantics), as the lane task required:

- Representation: `IROrd` (plain/atomic), `IRSort` (val/tok), `IROp`
  (const/fetch/mov/add/sub/cmp/store/setvar/push/pop with source
  anchors), `IRPhi`, `IRTerm` (halt/br/cond), `IRBlock`/`IRGraph`,
  `IRState` (world + vars + ssa + toks + label/pred).
- Interpretation over memory-changing operations: `ssaGet`,
  `varsGet`, `irInit`, `fitVal`, `asInt`, `asBool`, `irStepOp` (real
  `Zahl.add`/`sub`, real `World.schreibSlot` for stores),
  `findBlock`, `irStepPhi`, `runList`, `runPhis`, `irStepBlock`,
  fuelled `irRun`.
- Decided checker: `nodupB`, `termTgts`, `blockLabels`, `predsOf`,
  `opDefs`, `opUses`, `blockDefs`, `defsBefore`, `interAll`,
  `lookupDom`, `domStep`, `domSets`, `defBlock`, `useOK`, `armOK`,
  `opDepth`, `blockDepthOut`, `blockTokOut`, `termUseOK`, `blockWF`,
  `irWF`.
- Fragment + lowering: `FragE` (10 arithmetic forms), `FragS`
  (assignVar/assignSlot/ite), `FragB` (nil/cons/bind), `LSt`,
  `lowerE`, `closeBlock`, `noBindS`, `noBindB`, `lowerB`,
  `lowerGraph`.
- Execution/agreement facts: `ssaGet_push`, `ssaGet_cons_other`,
  `runList_append`, `runList_single`, `stepOp_vars_length`,
  `runList_length`, `opDefIds`, `runList_stable`, `runPhisTok`,
  `varsAgree`, `memEq`, `phiSrcLive`, `lenOfGetSome`,
  `find?_none_of_ne`, `find?_nodup_mem`, `varLvl_inj`,
  `varLvl_inj_ty`, `envGet_set_same`, `envGet_set_other`, `tailGet`,
  `setAgree`, `pushAgree`, `fitVal_same`, `asInt_same`,
  `envVals_get`, `IRStep`, `IRStar`, `irStar_trans`, `IRHalt`,
  `IRBig`, `irStar_halt_run`, `irBig_run`, `flatBridge`,
  `fitVal_weiter`.
- Generic correspondence: `ecorrW` (all 10 `FragE` cases: lowered
  expression runs evaluate to source `eval`, with preservation of
  vars/world/toks/token/base/label/pred, freshness bounds, and
  definition lower bounds).
- Block-correspondence scaffolding: `envLen`, `envVals_length`,
  `bindsS`/`bindsB`, `adjAgree`, `plain_of_adj_matched`,
  `adj_of_plain_matched`, `shrinkAdjTail`, `lese_memEq`,
  `memEq_symm`, `memEq_trans`, `storeSlot_same_other`,
  `storeSlot_same_same_other`, `storeSlot_hit`, `storeSlot_andere`,
  `storeSlot_congr`, `schreibSlot_congr`, `lowerE_mono`.
- Witness scene: `XD` (minimal declaration: one int table some
  function writes), `XV`, `Xρ` (one int variable holding 5), `Xσ`
  (zeroed world), `Xfe` (`(var hier) + 3` derivation), `Xst`, `Xs`
  (`irInit`), `Xagree`, `Xfresh`, `ecorrW_zeuge` (joint premise
  instantiation on the non-degenerate program).
- Unfinished: `lowerB_mono` (counter monotonicity through blocks;
  drafted, red — see §5).

Two soundness repairs found while proving (in the preserved draft):
`lowerB` ite arms now thread the fresh tokens (`tokT tokT` /
`tokE tokE` instead of a stale `tok`, which stuck the first store of
a branch); `noBindB` recurses into `bind` bodies
(`(!flag) && noBindB false hrest`).

## 3. Measured verification history (lean-probe on the draft)

- Start of this continuation: 38 errors (the pre-pause state).
- Var-case index fix (`| @var τ x =>` shadowing, §6 finding 1): 38 → 30.
- `show`-before-`omega` for record projections (6 sites), two-step
  `rcases` for left-nested `++` (5 sites): 30 → 24.
- Local `storeSlot_hit`/`storeSlot_andere` (Maschine/Satz not
  imported), subst-direction fix (`t' k' f'`): 24 → 18 → 2.
- `shrinkAdjTail` length premise + `varLvl (Var.dort (σ := τ) x)`
  pinning: 2 → **0 errors, exit 0** (full `ecorrW` + witness scene
  green, single-file probe).
- `ecorrW_zeuge` added on the green tree: still 0 errors.
- `lowerE_mono` added: still 0 errors.
- `lowerB_mono` appended: red; final preserved state is the 6-error
  output quoted in §5. The draft was preserved at that point per the
  supersession instruction instead of being repaired further.

`#print axioms` was never run for `ecorrW` (file removed first), so
**no axiom claim is made** for any preserved theorem.

## 4. Reusable items for validator-adapter work (decision §7 mapping)

Algorithms (untrusted implementation guidance, soundness to be proved
against `exec`/bytes, never against `irRun`): token threading via
single-arm phis and join-phi arm resolution (`runPhisTok` shape);
source anchors on every op; pure-expression lowering shape
(`lowerE`: one fresh id per node, bounds riding along);
`noBindB`-style refusal of unbalanced scopes; `irWF` components as
validator recomputation checklist (unique labels, entry presence,
token-phi coverage per predecessor with matching token outputs,
use-before-definition via dominance, depth threading, edge order).

Lemmas (restatable over source-anchored blocks): `runList_stable`
(untouched definitions survive a run), `runPhisTok` (token-only phi
resolution), `setAgree`/`pushAgree`/`envVals_get` (environment
agreement), `memEq` + `storeSlot_congr`/`schreibSlot_congr` +
`lese_memEq` (trace-ignoring memory congruence for
`World.schreibSlot`), `lowerE_mono` (counter discipline),
`flatBridge` (definition membership), `find?_nodup_mem`.

Not adopted per the decision: `irRun`, `irWF`-as-trusted-code, and
the `FragE`/`FragS`/`FragB` derivation datatypes.

## 5. Precise defects and cuts in the preserved draft

1. `lowerB_mono` (line 2607 of preserved file): 6 errors, all local
   to that proof — multi-line `{ ... with ... }` record literals
   fail to parse in this toolchain (trailing-comma newline:
   "unexpected identifier; expected '}'"), and `simp only [lowerB]`
   makes no progress inside term-mode `match` arms (the discriminand
   is not refined for equation lemmas there; use tactic
   `induction`/`cases` or fully explicit constructor applications).
   Counter monotonicity through `lowerB` is therefore unproved in
   the draft; a tactic double-induction rewrite was drafted
   (`.tmp/newmono2.txt`) but never spliced or verified.
2. No statement-level correspondence (`scorrW`/`bcorrW` over
   `lowerB` output to `execStmt`/`execBlock`) was written — designed
   only. Consequently: no block-label nodup lemma, no exits/terminator
   characterization, no ite-arm/join composition, no `bind`-scope
   adjusted-agreement composition, and no memory-changing run witness.
3. `ecorrW` covers expressions only (`eval`); stores, binds, and
   control flow have no proved correspondence in the draft.
4. The `CUTS` comment in the preserved file (line 2300) is stale
   (predates the `ecorrW` completion); the operative cuts list is
   this section.
5. `Bis287.lean` is an early subset snapshot (defs through the
   `fitVal_weiter` era); `Tmp287.lean` is Mini-family scratch. Neither
   was ever part of the build.

## 6. Elaborator findings (for future Lean-first lanes)

1. In `induction fe with | var x =>`, outer indices persist in
   context while branch goals use case indices; referencing outer
   `τ`/`e` in tactic code then mismatches. Fix that worked:
   `| @var τ x =>` (explicit shadowing). Verified by 8 scratch
   replicas before applying.
2. A dependent pair `∃ hty : τ = τ', hty ▸ x = y` with
   obtain-then-`cases`-on-both-components crashed elaboration
   (`failed to create thread`, exit 134); weakened to the
   type-equality-only `varLvl_inj_ty`, which is all `setAgree` needs.
3. Same crash family for `▸` + double-`subst` in `envGet_set_other`;
   reformulated premise as level inequality
   (`varLvl x ≠ varLvl y`) with explicit revert-before-induction.
4. `omega` does not see through record-update projections; precede
   with `show` (or `dsimp only`) reducing them to plain atoms.
5. `rcases a | b | c` follows the actual `++` association in the
   goal (here left-nested after double `mem_append`); split in two
   steps when unsure.
6. `simp [varLvl]`-style unfolding can leave ambiguous auto-bound
   implicits (`σ` of `Var.dort`); pin with `(σ := τ)` and prefer
   `rfl`-stated projection facts.
7. `Nat.add` literal-vs-nested (`+3` vs `+1+1+1`) defeq should not be
   relied on across `rw` matching; transcribe source-faithful
   nested forms for rewrite rules.
8. `lowerE.eq_N`/`rw`+`obtain`-rfl is the robust idiom for
   destructuring let-heavy lowering bodies (`hlow_idiom` pattern).

## 7. Why this architecture is superseded (per decision 594/606)

The draft is a second language with a second executor (`irRun`),
a second WF notion (`irWF`), and second environments/arithmetic
(`varsAgree` vs `Env`, re-stated `Zahl` ops) alongside `exec` and
the checker. Every new construct would have needed a `Frag*`
derivation extension, a lowering case, an `irWF` rule,
execution-fact lemmas, and a new correspondence — proof obligations
the selected direct path (source-anchored blocks to validated
bytes via `execStmt`/`World.schreibSlot`) discharges by
construction. No statement here disputes that assessment.

## 8. What remains OPEN (direct source-to-bytes work)

Per decision §§4–5, as applicable to this lane's fragment: L1 width
rows beyond the pilot (draft covers int arithmetic only); L2
statement forms — `assignSlot`/`bind`/`ite` lowering relations with
`TableLayout` admission, footprint realisation, and joint
memory-changing witnesses plus planted refusals (overlap,
out-of-range, width mismatch); block-label/exit infrastructure for
multi-block composition; `#print axioms` evidence for any revived
correspondence; validator-adapter closing (`valX86`, `valX86_sound`).
Untouched by this lane: L3 entries/budget/stutter, L4 per-access
TSO, LOCK/fence execution, SIMD, ghost-event preservation.

## 9. Task feedback

Nothing in the lane task itself was found wrong; the end state
follows the merged decision, not a task defect. One environmental
note: single-file `lean-probe` intermittently dies with exit 134
(`failed to create thread`) under full-machine load while smaller
files pass; all defect claims above rest on repeated deterministic
runs (exit 1 with locations), never on a single crashed run.
