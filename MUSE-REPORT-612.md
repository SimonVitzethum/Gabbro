# MUSE-REPORT-612: Independent closure review of 600

## Scope and method

Verified directory `/home/simon/Dokumente/gabbro-muse/a612`, branch `muse/612`.
Reviewed the exact snapshot in `.tmp/review/SNAPSHOT.json` (author 600, base
`0044c2585bdd2ebad67d8d7bd5c3a4db11b171eb`, files `MUSE-REPORT-600.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/InstructionSelection.lean`)
against the actual candidate file in `.tmp/review/author-600/` and the owner
task. Copied the candidate file into `grammatik/Grammatik/X86/` temporarily,
ran `./lean-probe` (0 errors) and full `./lean-bau` with the umbrella import
appended (441 jobs green), then reverted both so this commit is report-only.
Checked for banned tactics, premise use, witness non-degeneracy, refusal cases,
CUTS precision, axioms, reserved paths, and overclaim.

CANDIDATE: 600 1e8359bb6a4444fe238a850f9016517c6e5b0cb5

VERDICT: ACCEPT

## Findings

- Build reproduced on the current tree: `./lean-probe` prints
  `== 0 error(s) in the COMPLETE output; exit 0`; `./lean-bau` ends
  `Build completed successfully (441 jobs).` (440 baseline + the new file).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no premise typed `Prop`
  itself; every theorem premise is used (`h : dst != src` fires the alias simp
  in `waehleSelbstMov_fremd`; `h0` rewrites in `schritt_addNull_wert`;
  `hdead` in `zweig_weicht_ab`; `hslot` in `inv_standort_falsch`;
  `h : alsLitOpt b = some 0` drives `quelle_add_lit_null` via `eval_alsLit`).
- Genuine source connection, no trusted metadata: `quelle_add_lit_null` uses
  the COMPUTED `alsLitOpt` with the accepted `eval_alsLit` lemma over real
  `eval`; no Rust-provided fact is trusted. Canonical executor reused
  throughout (`schritt_*` lemmas, `decode`/`roundtrip`); no new interpreter,
  no new IR.
- Joint non-degenerate witness present: `quelle_add_lit_null_zeuge` conjoins
  the source fact with `wit_schreibt` (contract writes table `()`) and the
  memory-changing run `wit_step` (slot `0 -> 5`). Meets the gate.
- Negative cases present: `wahlOk_verweigert_xor_le` (clobbering choice refused
  under live flags), `zweig_weicht_ab` (following `je` diverges, justifying the
  refusal), `waehleInv_verweigert` (no stability, no elimination),
  `inv_nach_lauf_falsch` (entry fact killed by the actual witness writer run),
  `waehleSelbstMov_fremd` (alias inequality checked).
- Flag/alias liveness are explicit `Bool`/equality parameters gated by `wahlOk`
  and the `dst != src` premise, not silent derivations; the file does not claim
  a full liveness analysis. `waehleInv` tags all three `InvScope` cases with
  identical behavior, honestly labelled as scope discharge deferred to the goal
  legs in CUTS. Real bytes compared (`null_laengen` 10 vs 3, pinned
  `pin_xor_rax`/`pin_mov0_rax` by `decide`, `runde_null_rax` via accepted
  `roundtrip`).
- CUTS block precise; `#print axioms` for 16 theorems, all standard subsets of
  `propext, Classical.choice, Quot.sound` (several axiom-free), reproduced in
  probe output. No self-consistency-as-hardware claim, no timestamp reset, no
  guessed ISA (14 pilot forms only), no hidden simulation premise.
- Only owned paths touched (`InstructionSelection.lean` + umbrella import +
  report); no checker/Spec/goal edits; no friend-reserved optimiser paths.
- One doc imprecision, not verdict-relevant: the header names `StaerkeReduktion`
  value facts but imports only `InvariantenOpt`; the add-zero identity is proved
  directly via `add64`. The report itself scopes the shift half as an explicit
  CUT, so nothing is overclaimed. No repair needed; optional follow-up is a
  one-line header clarification by the owning author lane, not a condition.

## Bounded accepted scope

Accepted as: three register-only selection functions (`waehleNull`,
`waehleAddNull`, `waehleSelbstMov`) with value lemmas, real byte-length/pinned
facts, executed-step observations through canonical `schritt`, flag-cost with a
diverging following branch, checker verdicts (`wahlOk`, `waehleNull_*`,
`waehleAddNull_*`, `waehleSelbstMov_*`), one computed-literal source rule with
a joint memory-changing witness, and entry-vs-site invariant discipline with
refusal without held stability. Explicitly NOT accepted as: shift/mul strength
at byte level, `InvScope` discharge, load/store aliasing, cost/budget/call-log/
concurrency transfer, or hardware correspondence (all in CUTS).

## Interfaces and next tasks

- Produces for `valX86`/validator lanes: `waehleNull`/`waehleAddNull`/
  `waehleSelbstMov` as a checked peephole table with byte lemmas;
  `wahlOk` as the flag-gate shape; `runde_null_rax` + `schritt_null_gleich`
  compose decode-then-execute observations.
- Useful next independent tasks (exact ownership to coordinator): (a) load/store
  selection over `Zugriffe`/`AccessList` permission facts; (b) wiring
  `wahlOk`-style gates into the branch-layout leg; (c) shift-form pilot
  extension unlocking the `staerkeMul` byte half.

## New definitions/theorems by this reviewer

None. Review-only lane; no Lean or Rust changes.

## Last build result

`Build completed successfully (441 jobs).` (candidate integrated; reverted after
the check; working tree clean at commit).

## What remains open / task remarks

Nothing in the lane-612 task text is wrong. No further review debt from 600
beyond its own CUTS. Minimal repair locations: none.
