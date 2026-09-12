# MUSE-REPORT-58 (lane 58): ghost carriers (PLAN-SYSCALL.md S3) -- reviewer revision

## What was done

Ported the ghost-carrier flag from `ref-wip` to the current core and proved
the G001 checker decision sound plus erasure, in a new file.

Core change (`grammatik/Grammatik/Syntax.lean`): two new fields on
`Deklaration`, `geist : Tab -> Bool := fun _ => false` and
`ggeist : Glob -> Bool := fun _ => false`, marking ghost (spec-only)
carriers. The DEFAULT VALUES are the merge-safety fix requested by the
reviewer: all seven existing declaration literals (`Extraktion.miniD`,
`VertragOrtB.miniContrD`, `Satz.leer`, `BlattGegenbeispiel.D1`, `QLeer.qD`,
`RufMaschineD.rufD`, `Zeugnis.TestD`) compile UNCHANGED -- my earlier
round's per-literal edits were reverted. So will every literal written in
parallel by other lanes. The semantics never consults these fields, so every
existing definition behaves as before; the emitter omits ghost carriers.
This matches the `ref-wip` design (`geist`/`ggeist`, rule G001) minus its
stale-base remainder (that branch also dropped `shared` and renamed
`vorzustand`; neither was ported).

New file `grammatik/Grammatik/Geist.lean` (namespace
`Gabbro.Grammatik.Geist`, witness namespace `Zeuge`), wired via
`import Grammatik.Geist` at the end of `grammatik/Grammatik.lean`.
It reuses `Extraktion.stmtOrte`/`blockOrte`/`endblockOrte`/`armsOrte`/
`grundArmsOrte` (section 13) and `Extraktion.eval_liest_orte` (section 19
R1) by qualified name -- not redefined:

- `istGeist`: ghost predicate over `Tab (+) Glob` from the flags.
- `orteOhneGeist`: footprint-level proposition (every member real).
- `geist_leer_unveraendert` (task item 1): with no ghost flags, `istGeist`
  is constantly false -- no new case, no changed behavior.
- (a) DECISION: `orteOk` (footprint-level `Bool`), and `g001Stmt`/`g001`
  (Block -- the reviewer's exact form)/`g001End`/`g001Arms`/`g001Grund`,
  each by structural recursion over its body form, checking every
  executable `Expr.orte`/`Args.orte`/`ErgExpr.orte` position against the
  flags (`awaits`/`exchange` name their global directly, as `execBlock`
  reads it). Bodies have no contract positions (`requires`/`ensures` live
  in `Programm`), so accepted bodies leave ghosts to contracts.
- (a) SOUNDNESS: `orteOk_korrekt` plus `g001Stmt_korrekt`/
  `g001_korrekt` (Block -- the reviewer's exact statement
  `g001 b = true -> forall o in blockOrte b, not istGeist o`)/
  `g001End_korrekt`/`g001Arms_korrekt`/`g001Grund_korrekt` as ONE `mutual`
  block with `termination_by structural`, each calling its siblings
  directly. `nge_of_eq_false` bridges `= false` leaves to the `¬`
  conclusions.
- (b) ERASURE: `eval_gleich_ausser_geist` -- a ghost-free-footprint
  expression evaluates equal in two worlds agreeing off-ghost -- via
  `Extraktion.eval_liest_orte`; lifted to `assignVar` by
  `assignVar_orte_mem` (step footprint is the bound expression's) and
  `assignVar_eval_gleich`.
- Witness: `GD` (two `Bool` tables; `true` ordinary, `false` ghost -- the
  only non-default field), `GD_ordentlich`/`GD_geist`, `GV`, `gi`/`gslot`,
  `gstmt`, `gbody : Block` with `gbody_g001 : g001 gbody = true` by `rfl`,
  `gendbody : Endblock` feeding `GP` (`requires` true, `ensures` `GPost`
  over the ghost slot, `gpost_liest_geist`), `GO`, `gwelt`,
  `gschritt_schreibt` (fired write reaches a world with the write event),
  `gslot_ohne_geist`, `gwelt_gleicht`, `erasure_zeuge` (two worlds
  differing only on the ghost table agree on the witness read).
- `g001_korrekt_zeuge`: joint instantiation of ALL premises of the target
  at `gbody` on the non-degenerate program `GD`.

The reviewer's defect 2 verdict ("`emittiert_liest_keinen_geist` is a
tautology: premise IS conclusion unfolded") is accepted without reserve:
the old `rumpfOhneGeist` predicate, its fold/unfold pair, and the old
theorem are DELETED. The replacement has content in both directions: the
`Bool` decision computes independently of the `Prop` claim (a checker
could run it), and erasure connects ghost-freedom to evaluation.

## Exact names of new definitions/theorems

`Geist.istGeist`, `Geist.orteOhneGeist`, `Geist.geist_leer_unveraendert`,
`Geist.orteOk`, `Geist.orteOk_korrekt`, `Geist.nge_of_eq_false`,
`Geist.g001Stmt`, `Geist.g001` (Block), `Geist.g001End`,
`Geist.g001Arms`, `Geist.g001Grund`, `Geist.g001Stmt_korrekt`,
`Geist.g001_korrekt`, `Geist.g001End_korrekt`, `Geist.g001Arms_korrekt`,
`Geist.g001Grund_korrekt`, `Geist.eval_gleich_ausser_geist`,
`Geist.assignVar_orte_mem`, `Geist.assignVar_eval_gleich`,
`Geist.Zeuge.GD`, `Geist.Zeuge.GD_ordentlich`, `Geist.Zeuge.GD_geist`,
`Geist.Zeuge.GV`, `Geist.Zeuge.gi`, `Geist.Zeuge.gslot`,
`Geist.Zeuge.gstmt`, `Geist.Zeuge.gbody`, `Geist.Zeuge.gbody_g001`,
`Geist.Zeuge.g001_korrekt_zeuge`, `Geist.Zeuge.gendbody`,
`Geist.Zeuge.GPost`, `Geist.Zeuge.GP`, `Geist.Zeuge.gpost_liest_geist`,
`Geist.Zeuge.GO`, `Geist.Zeuge.gwelt`, `Geist.Zeuge.gschritt_schreibt`,
`Geist.Zeuge.gslot_ohne_geist`, `Geist.Zeuge.gwelt_gleicht`,
`Geist.Zeuge.erasure_zeuge`.

Deleted from the previous round: `orteOhneGeist_links/_rechts/_append`,
`expr_orte_ohne_geist_of_leer`, `args_orte_ohne_geist_of_leer`,
`exprOhneGeist`, `rumpfOhneGeist`, `rumpfOhneGeist_orte`,
`rumpfOhneGeist_of_orte`, `geist_leer_unveraendert_tab/_glob`,
`emittiert_liest_keinen_geist`,
`emittiert_liest_keinen_geist_zeuge`, `gbody_ohne_geist`, `GPre`,
Geist's own `stmtOrte`/`blockOrte`/`endOrte`/`armsOrte`/`grundOrte`
duplicates (now reused from `Extraktion`).

## Last ./lean-bau result line

`Build completed successfully (37 jobs).` -- 0 error lines, whole project
green including `Grammatik.Geist`.

`#print axioms` (all six): only `[propext, Classical.choice, Quot.sound]`
for `g001_korrekt`, `g001_korrekt_zeuge`, `geist_leer_unveraendert`,
`eval_gleich_ausser_geist`, `erasure_zeuge`, `gschritt_schreibt`.

Guardians: `pruefe-kennungen.py` ALL PASS; `pruefe-englisch.py` exit 0 with
no finding on new files; `pruefe-todo.py`/`pruefe-praemisse.py` not runnable
here (need `cargo`/ssh respectively -- neither is available on this lane
by rule 1). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`,
no `intro _`, no `have _ :=` in `Geist.lean`; every premise of every new
theorem is consumed by its proof (checked by inspection; the two
`hg`-binder linter warnings in `erasure_zeuge` are vacuous global
agreements over `GD.Glob = Empty`, kept named rather than `_`-discarded).

## What remains open

- No emitter-omission theorem: the read side (accepted bodies name no
  ghost) and erasure (ghost-free reads evaluate equal off-ghost) are
  proved; that omitting ghost tables preserves emitted behavior is not
  stated -- emission lives in `crates/`, not in `grammatik/`.
- `gschritt_schreibt` fires the witness write in place (`T[true] :=
  T[true]` keeps the value `b`); the trace records the write event, but no
  slot VALUE change is exhibited. A value-flipping witness (negation write)
  would show a memory-changing step in the stronger value sense.
- `assignVar_eval_gleich` lifts erasure to one statement form only
  (`assignVar`); the remaining statement forms are not lifted.

## Anything in the task believed to be wrong

Nothing is wrong. Two notes:

- Item 1 ("every existing definition behaves as before, stated as
  equalities of the relevant functions") cannot be a deep theorem: the
  semantics functions do not take the flags as arguments, so there is no
  "before" function to compare against. `geist_leer_unveraendert` states
  the checkable content, and the whole-project green build with untouched
  literals is the behavioral half.
- On the reviewer's hint for (b): it says "a lemma that eval depends only
  on `e.orte` likely exists" -- it does (`Extraktion.eval_liest_orte`,
  section 19 R1), and erasure reuses it rather than re-proving it. The
  ghost-specific content is discharging its four agreement premises from
  off-ghost agreement plus the ghost-free footprint.
- Proof engineering, measured: mutual tactic-theorem induction over
  `Stmt`/`Block` needs tactic `match` (not `cases` -- `cases` elaborates
  to something `brecOn` cannot eliminate, failing with
  `true = g001 e` unsolved) plus `termination_by structural` (the
  `termination_by x => e` form is rejected for tactic theorems in this
  toolchain with a spurious "binds 0 parameters"). Equation-compiler style
  fails on the dependent indices. No precedent exists in-tree -- nobody
  inducts over these types in proofs today.
- 2026-09-12 (post-merge): master added `hd`/`hgd` guard premises to
  `Stmt.axiomCall` (lane 74) and a width prefix to `Expr.shl`/`shr`
  (lane 61); adapted two `axiomCall` patterns in `Geist.lean` (extra `_`
  binders, statements unchanged) -- the `shl`/`shr` change needs nothing
  here since footprints are reused via `Expr.orte`.
