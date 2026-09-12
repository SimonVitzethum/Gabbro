# MUSE-REPORT-58 (lane 58): ghost carriers (PLAN-SYSCALL.md S3)

## What was done

Ported the ghost-carrier flag from `ref-wip` to the current core and proved
the emission-relevant read-freedom theorem in a new file.

Core change (`grammatik/Grammatik/Syntax.lean`): two new fields on
`Deklaration`, `geist : Tab -> Bool` and `ggeist : Glob -> Bool`, marking
ghost (spec-only) carriers. Default: none is ghost. The semantics never
consults these fields, so every existing definition behaves as before; the
emitter omits ghost carriers. This matches the `ref-wip` design
(`geist`/`ggeist`, rule G001) minus its stale-base remainder (that branch
also dropped `shared` and renamed `vorzustand`; neither was ported).

Declaration literals fixed with defaults only (no proof changes):
`Extraktion.miniD`, `VertragOrtB.miniContrD`, `Satz.leer`,
`BlattGegenbeispiel.D1`, `QLeer.qD`, `RufMaschineD.rufD` (all
`geist := false`-shaped), `Zeugnis.TestD` (`false`/`false`).

New file `grammatik/Grammatik/Geist.lean` (namespace
`Gabbro.Grammatik.Geist`, witness namespace `Zeuge`), wired via
`import Grammatik.Geist` at the end of `grammatik/Grammatik.lean`:

- `istGeist`: ghost predicate over `Tab (+) Glob` from the flags.
- `orteOhneGeist`: footprint-level check (every member real).
- `orteOhneGeist_links/_rechts`, `orteOhneGeist_append`: side projections
  and append closure (all premises consumed).
- `stmtOrte`/`blockOrte`/`endOrte`/`armsOrte`/`grundOrte`: the
  emission-relevant read footprint of bodies, defined as the union of the
  executable `Expr.orte`/`Args.orte`/`ErgExpr.orte` lists. Bodies have no
  contract positions (`requires`/`ensures`/invariants live in `Programm`),
  so "ghost only in contracts" holds by construction for accepted bodies.
- `exprOhneGeist`, `rumpfOhneGeist` (rule G001 as a predicate over an
  accepted body), `rumpfOhneGeist_orte`/`rumpfOhneGeist_of_orte` (unfold/fold
  pair, both premises used each).
- `expr_orte_ohne_geist_of_leer`, `args_orte_ohne_geist_of_leer`: with no
  ghost flags every footprint is ghost-free.
- `geist_leer_unveraendert_tab/_glob`, `geist_leer_unveraendert` (task item
  1): with no ghost table and no ghost global, `istGeist` is constantly
  false -- stated as equalities of the relevant functions (no new case in
  the semantics, which never reads the flags).
- `emittiert_liest_keinen_geist` (task item 2): an accepted body reads no
  ghost carrier. Stated over one fixed accepted body `b` (acceptance
  premise `hb : rumpfOhneGeist b`, member premise `ho`), NOT over all
  statements -- deliberately, to avoid the wave-1/2 vacuity defect (a
  universal over all `Stmt` would be falsified by any ghost-reading body
  and discharge nothing).
- Witness: `GD` (two `Bool` tables; `true` ordinary, `false` ghost),
  `GD_ordentlich`/`GD_geist`, `GV`, `gi`/`gslot`, `GPre`/`GPost` (contract
  naming the ghost table, body never reads it), `gbody` (writes the
  ordinary table), `gbody_ohne_geist`, `gpost_liest_geist`, `GP`
  (program), `GO` (oracle), `gwelt` (worlds), `gschritt_schreibt`
  (fired write reaches a world with the write event in the trace).
- `emittiert_liest_keinen_geist_zeuge`: joint instantiation of ALL
  premises of the target at `gbody` on the non-degenerate program `GD`.

## Exact names of new definitions/theorems

`Geist.istGeist`, `Geist.orteOhneGeist`, `Geist.orteOhneGeist_links`,
`Geist.orteOhneGeist_rechts`, `Geist.orteOhneGeist_append`,
`Geist.stmtOrte`, `Geist.blockOrte`, `Geist.endOrte`, `Geist.armsOrte`,
`Geist.grundOrte`, `Geist.exprOhneGeist`, `Geist.rumpfOhneGeist`,
`Geist.rumpfOhneGeist_orte`, `Geist.rumpfOhneGeist_of_orte`,
`Geist.expr_orte_ohne_geist_of_leer`, `Geist.args_orte_ohne_geist_of_leer`,
`Geist.geist_leer_unveraendert_tab`, `Geist.geist_leer_unveraendert_glob`,
`Geist.geist_leer_unveraendert`, `Geist.emittiert_liest_keinen_geist`,
`Geist.Zeuge.GD`, `Geist.Zeuge.GD_ordentlich`, `Geist.Zeuge.GD_geist`,
`Geist.Zeuge.GV`, `Geist.Zeuge.gi`, `Geist.Zeuge.gslot`,
`Geist.Zeuge.GPre`, `Geist.Zeuge.GPost`, `Geist.Zeuge.gbody`,
`Geist.Zeuge.gbody_ohne_geist`, `Geist.Zeuge.gpost_liest_geist`,
`Geist.Zeuge.GP`, `Geist.Zeuge.GO`, `Geist.Zeuge.gwelt`,
`Geist.Zeuge.gschritt_schreibt`,
`Geist.Zeuge.emittiert_liest_keinen_geist_zeuge`.

## Last ./lean-bau result line

`Build completed successfully (37 jobs).` -- 0 error lines, whole project
green including `Grammatik.Geist`.

`#print axioms` (all four): only `[propext, Classical.choice, Quot.sound]`.

## What remains open

- No emitter-omission theorem: the read side is proved (accepted bodies
  name no ghost); that omitting ghost tables preserves emitted behavior is
  not stated -- emission lives in `crates/`, not in `grammatik/`.
- No per-constructor footprint-membership lemmas for
  `stmtOrte`/`blockOrte`/`endOrte` (member-of-body implies member-of-subterm
  directions).
- `gschritt_schreibt` fires `T[true] := T[true]` in place: the trace
  records the write event, but no slot VALUE changes. A value-flipping
  witness (negation write, as in `BlattGegenbeispiel`) would show a
  memory-changing step in the stronger value sense. The non-degeneracy bar
  (a table the function writes + a reached run with a memory-changing
  step) is met in the trace-event sense only; a strict gate should ask for
  the value flip.

## Anything in the task believed to be wrong

Nothing is wrong, but item 1 ("every existing definition behaves as
before, stated as equalities of the relevant functions") cannot be a deep
theorem: the semantics functions do not take the flags as arguments, so
there is no "before" function to compare against. `geist_leer_unveraendert`
states the checkable content: with all flags false, `istGeist` is
constantly false, i.e. the new field introduces no new case anywhere.
The build staying green across all pre-existing files (whose literals
needed only default values) is the behavioral half of the claim.
