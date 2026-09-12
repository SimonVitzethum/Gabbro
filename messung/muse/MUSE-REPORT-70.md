# MUSE-REPORT-70: Hoare rule for the call statement (lane 70)

## What was done

New file `grammatik/Grammatik/HoareRuf.lean` (~250 lines), wired via
`import Grammatik.HoareRuf` at the end of `grammatik/Grammatik.lean`.
It adds the missing call rule on top of `HoareRegeln.lean` (merged wave 2),
stated against a contract-respecting call handler.

New definitions/theorems (all `Gabbro.Grammatik`):

- `RespektiertVertraege (P : Programm D) (R : ...) : Prop` --
  `forall f sig rho, ReqAmEintritt P f sig rho -> forall s' v,
  R f sig rho = RufAusgang.ok s' v -> EnsAmRueck P f sig s' rho v`.
  Adapted to the real shapes: `RufAusgang f` has `.ok world value`
  (no separate `returns normally` constructor), and
  `ReqAmEintritt`/`EnsAmRueck` are taken from `VertragOrtB.lean`
  at the actual entry world, return world, arguments and result.
- `hoare_call (P O passes R) (hR : RespektiertVertraege P R)
  (f args hp hr) (s0 rho0 r0) : STTripel ... (.call f args hp hr) Pre Post`
  with LOGICAL VARIABLES fixed by the precondition:
  `Pre sig rho` is `sig.lese ... = s0 /\ evalArgs ... = rho0 /\
  rho = r0 /\ ReqAmEintritt P f s0 rho0`, and `Post s' rho'` is
  `rho' = r0 /\ exists v, R f s0 rho0 = .ok s' v /\
  EnsAmRueck P f s0 s' rho0 v`.
  The postcondition pins the ACTUAL call (reviewer fix 2026-09-12: the
  previous version bound `s0`/`rho0` existentially, so any entry world
  leading to `s'` satisfied it); the caller environment is unchanged
  (`rho' = r0`, carried as third logical variable, since `.call`
  discards the result and keeps `rho`).
  Proof: rewrite the `execStmt` unfolding with the `hPre` equalities,
  case-split `R f s0 rho0`; the `.ok` branch closes with `hR`, the
  `.grund` branch by the empty `Fin` (`hr : D.gruende f = 0`), the error
  branches by discrimination. All premises used (`hR`, all four `hPre`
  conjuncts, `hr`). The old existential-`s0`/`rho0` version is replaced,
  not kept (nothing else used it).
- Witness on the instructed one-function `rufPD` program of
  `RufMaschineD.lean` (increment, ensures result = param + 1) with a
  handler that runs the body:
  - `witVal70`, `rufD_params_any70`, `rufD_erg_any70` (helpers),
  - `Rwit70`: gated handler -- answers `.ok` with `param + 1` and the
    world unchanged when `requires` holds, else `.logik (.vorbedingung f)`,
  - `hRwit70 : RespektiertVertraege rufPD Rwit70` (gate selects the
    `ok` branch; ensures duty by computation),
  - `witStmt70` (`.call rufIncD rufArgsD ...`), `witPre70` (entry gate
    by `rfl`), `witRun70` (normal run by `rfl`),
  - `s0wit70`/`rho0wit70` (witness logical variables: read world,
    evaluated args),
  - `hoare_call_zeuge`: handler respect (`hRwit70`) AND the precondition
    conjuncts at the witness state AND the postcondition for EVERY normal
    outcome of the witness run (proved by applying `hoare_call` itself,
    so the rule fires on the witness) AND existence of such an outcome
    (`witRun70`, so the universal is not vacuous).

## Last `./lean-bau` result line

`Build completed successfully (38 jobs).` --
first line: `== 0 error line(s) in the COMPLETE output`.
`./lean-probe grammatik/Grammatik/HoareRuf.lean`: `0 error(s)`.
`#print axioms` for all six main names: only
`[propext, Classical.choice, Quot.sound]` (no sorry/axiom).

## What remains open

Listed in the file's `CUTS` block: `callInd`/`bindCall`/`bindCallInd`/
`bindCallElse` not covered; witness handler keeps the world (`s0 = s'`,
`rufD` writes nothing); `hRwit70`'s ensures duty is computational
(`rfl`) since `rufD` contracts read only values, not memory.

## Believed-wrong parts of the task

None outstanding after the reviewer fix; two notes:
- The sketch's `R` type omits the `Programm`/`Orakel`/`passes` context of
  `execStmt`; the statement is elaborated against the real `execStmt`
  `.call` equation (argument-world read, then match on `R`).
- The witness program `rufD` declares one table (`Tab := Unit`) but with
  `schreibt := fun _ => false`, so no function writes it and the witness
  run moves no memory. The instructed witness (`rufPD`) is used anyway;
  the strict rule-13 non-degeneracy clause (a written table, a
  memory-changing step) is not met on this program. The reached call with
  a normal outcome IS exhibited (`witRun70`), and the postcondition is
  proved non-vacuously for it.
