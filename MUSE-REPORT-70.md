# MUSE-REPORT-70: Hoare rule for the call statement (lane 70)

## What was done

New file `grammatik/Grammatik/HoareRuf.lean` (~230 lines), wired via
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
  (f args hp hr) : STTripel ... (.call f args hp hr) Pre Post`
  where `Pre sig rho` is "requires holds at the argument world
  `(sig.lese ... args.orte)` with the evaluated arguments
  `evalArgs ...`", and `Post s' _` is
  `exists s0 rho0 v, R f s0 rho0 = .ok s' v /\ EnsAmRueck P f s0 s' rho0 v`.
  Proof: unfold `execStmt` on `.call` (argument-world read, then match
  on `R`); the `.ok` branch closes with `hR`, the `.grund` branch by
  the empty `Fin` (`hr : D.gruende f = 0`), the error branches by
  discrimination. All three premises used (`hR`, `hPre`, `hr`).
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
  - `hoare_call_zeuge`: the CONJUNCTION of all three, i.e. all premises
    of `hoare_call` instantiated jointly with concrete values and proved.

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

One deviation, forced by the real code and weaker than the task sketch
in one respect: the sketch's `R` type
`World D -> Env D (D.params f) -> RufAusgang f` omits the `Programm`/`Orakel`/`passes`
context of `execStmt`, and the sketch's postcondition names "the actual
entry world" -- but a `Stmt.call` outcome is just `.ok s' rho` with the
CALLER env; the entry world `s0` and result `v` are not recoverable from
the outcome alone, so they are existentially bound in the postcondition
(`exists s0 rho0 v, R f s0 rho0 = .ok s' v /\ EnsAmRueck ...`).
This is the standard formulation (cf. `hoare_assignVar_fwd`'s
existential postcondition in `HoareRegeln.lean`); nothing is added or
dropped beyond that elaboration.
The witness program `rufD` has no tables (inherited from `RufMaschineD.lean`),
so "at least one table that some function writes" is met only in the
degenerate `schreibt = false` sense; the reached call with a normal
outcome is exhibited (`witRun70`), and memory motion is vacuous there.
