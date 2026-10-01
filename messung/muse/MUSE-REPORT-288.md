# MUSE-REPORT-288: Invariant-derived optimisation on actual source semantics

Lane 288 (Lean-only). Owner file: `grammatik/Grammatik/X86/InvariantenOpt.lean`
(550 lines) + one additive umbrella import in `grammatik/Grammatik.lean`.
Model: opencode-go/muse-spark-1.3-contributor. No delegation, no other files,
no Rust, no numbers, no MARKE_EMIT.

## What was delivered

Generic optimisation-legality rules proved against the REAL typed source
language (`Syntax.lean`: `Expr`/`Block`/`Stmt`) and its REAL world semantics
(`Semantik.lean`: `eval`/`execBlock`/`execStmt`). Every rewrite is an
executable function on source syntax (or a direct syntax equation); every
correspondence a theorem over `eval`/`execBlock`.

Definitions: `alsLitOpt`, `litLeBool`, `litEqBool`, `isWahrAll`, `holdsBool`,
`isWahr`, `foldAddLit`, `InvScope` (`ruhe`/`sicht`/`wechsel`), witness
`wSig`/`wD`/`wV`/`wCond`/`wIdx`/`wVal`/`wRest`/`wSonst`/`wFull`/`wWorld0`/
`wO`/`wR`.

Theorems (proven, no sorry/admit/axiom/native_decide/unsafe):
- `alsLitOpt_lit`, `eval_alsLit` (extractor inversion + value bridge),
  `litLeBool_sound`, `litEqBool_sound`,
- `isWahrAll_sound` (checker soundness over `eval` at any type, via
  `Expr.rec` with the mutual `NutzlastExpr` motive discharged by `True`;
  IHs take `ρ` explicitly since `Env` depends on the context),
- `eval_foldAddLit` (constant fold, `rfl`), `eval_weiter_n` (widening keeps
  the number, `rfl`),
- `exec_pruefung_wahr`, `exec_ite_wahr` (branch elimination with EXACT
  trace transfer: the rest runs in the post-`lese` world, so read
  observations are preserved; the refused `else` is unreachable by proof),
- `exec_pruefung_inv` (same transfer, evidence from a program invariant
  through a NAMED `InvScope` tag consumed by cases),
- `slot_read_stabil` (redundant-load value identity under explicit index
  + carrier-stability premises),
- witness facts `wit_schreibt` (contract writes a table), `wit_isWahr`,
  `wit_elim` (generic correspondence on the witness), `wit_step`
  (reached run: slot reads `5` afterwards, closed by `decide`),
- eleven `_zeuge` companions, one per syntax-quantified theorem
  (`alsLitOpt_lit_zeuge`, `eval_alsLit_zeuge`, `litLeBool_sound_zeuge`,
  `litEqBool_sound_zeuge`, `isWahrAll_sound_zeuge`,
  `eval_foldAddLit_zeuge`, `eval_weiter_n_zeuge`,
  `exec_pruefung_wahr_zeuge` (= `wit_elim`), `exec_ite_wahr_zeuge`,
  `exec_pruefung_inv_zeuge` (scope `ruhe`), `slot_read_stabil_zeuge`),
  all on the table-writing witness program; non-degeneracy via
  `wit_schreibt` + `wit_step`.

Axioms: `#print axioms` for all 8 main theorems = exactly
`[propext, Classical.choice, Quot.sound]` (standard triple, in the file
output and the full build).

Last full build: `./lean-bau` → `Build completed successfully (369 jobs)`
(368 before + this file). `lean-probe` on the file: 0 errors.

## What remains open (also in the file's CUTS block)

Scope-tag discharge, stability-premise discharge, cost/ghost-budget
transfer, call-log transfer for call-changing transforms, fault transfer
beyond the unreachable else, interleaving/concurrency, atomics/MMIO/
foreign memory, any source-to-bytes claim.

## Findings and task remarks

1. `isWahrAll` has NO `nicht` arm by design: negation soundness would need
   completeness (true `eval` through non-literal shapes answers `false`),
   which is false. A polarity-aware checker is later work.
2. Multiplication folding is refused at this layer, honestly: `mul`'s
   four-corner `imin`/`imax` range type is not definitionally a literal
   type, so no `rfl` equation exists; it needs range evidence (a
   `weiter`-style bridge), not a syntactic fold.
3. `cases`/`split`/functional induction all fail on matches over the
   indexed `Expr` family where declaration indices (`gtyp`, `typ`) leave
   unification stuck; the working patterns are: general-type worker +
   `cases` at free index, `Expr.rec` with explicit `motive_2`, and
   `subst`/`injection` with verified orientation (subst eliminates the
   RHS variable). A stale scratch-restore once reverted committed work;
   recovered via `git checkout` (lesson: no backup files, use git).
4. Nothing in the task statement asked for anything I believe is wrong;
   the bounded scope (rewrite legality + obligations as data, no
   end-to-end chain) is exactly what was built.
