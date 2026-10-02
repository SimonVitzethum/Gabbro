# Muse Report 656: Fetched conditional byte-step flag dependency simulation

## What was done

New file `grammatik/Grammatik/X86/FetchedCondBranch.lean` (plus its one
import line in `grammatik/Grammatik.lean`), lifting
`FlagDependencies.jccSchritt_stabil` and the per-condition read sets
(`liestFlag` / `stimmtUebberein`) to the actual
`Byteschritt.fetchDekodiert` / `byteschritt` path. Committed as
`c49fea08`; `./lean-bau` green.

## Exact new definitions and theorems

Definitions: `fjDisp`, `fjBytes`, `fjExec6`, `fjDaten`, `fjSpeicher`,
`fjReg`, `fjTaken`, `fjAnder`, `fjAf`, `fjFall`, `fjStumpf`,
`fjOhneExec`, `fjFalschBytes`, `fjFalsch`.

Theorems:

- Fetch identity from equal code/map/RIP (nothing assumed identical):
  `holeFetchAux_gleich`, `geholt_gleich`, `fetchDekodiert_gleich`
  (consumed-prefix check reuses accepted
  `SourceCodeFrame.ausfuehrbarN_gleich`; my own duplicate of that
  name was removed after the full-build collision).
- Main: `fetchedJcc_stabil` — agreement on exactly the consumed flags
  gives the same successor RIP, the same branch outcome, the derived
  second fetch and the same `byteschritt` outcomes, via the accepted
  `jccSchritt_stabil` on actual fetched bytes (fetch from
  `fetchDekodiert_entspricht`, length from `decodeJumpIf_laenge`).
- `fetchedJcc_len_layout` — fetched length is the carried
  `BranchLayout` length (`zweigLaenge true .weit`).
- Lowering connections: `cmovLower_fetched_stabil` (admitted
  `cmovLowerOk` implies byte-step select stability for every
  condition), `wahlOk_fetched_notwendig` (the `wahlOk` refusal of
  clobbering `xor` under live flags is load-bearing: different fetched
  `je` successors, from `Anweisungswahl.zweig_weicht_ab`).
- CMOVcc/SETcc on their real `ControlCodec` byte helpers (no
  `fetchDekodiert` path exists for them):
  `cmov_e_unverbraucht_stabil`, `setcc_e_unverbraucht_stabil` (under
  `.e` only ZF is consumed), `cmov_setcc_len0_verweigert`.
- Pins (`decide`): `fj_kante_genommen` (4096 -> 4118),
  `fj_kante_ander_stabil`, `fj_kante_af_stabil`,
  `fj_mutation_faellt_durch` (ZF clear falls through to 4102),
  `fj_stumpf_verweigert`, `fj_ohneExec_verweigert`,
  `fj_falsch_verweigert` (all as `ausgangRip ... = none`, since
  `ByteAusgang` has no `DecidableEq`).
- Joint witnesses: `fetchDekodiert_gleich_zeuge`,
  `fetchedJcc_stabil_zeuge` (taken edge plus a store after it that
  changes the data byte 0 -> 42, plus truncation refusal),
  `cmovLower_fetched_stabil_zeuge` (value 20 stored and read back,
  plus flag-clobber refusal).

## Last `./lean-bau` result line

`Build completed successfully (458 jobs).`

`./lean-probe` on the new file: 0 errors. `#print axioms` for every
main theorem lies within `propext`, `Classical.choice`,
`Quot.sound` (several depend on fewer; none on anything else; no
`sorryAx`).

## What remains open (see CUTS in the file)

- No hardware correspondence (read sets are Intel-manual
  self-consistency, not silicon).
- No `fetchDekodiert` path for CMOVcc/SETcc (no `Befehl`
  constructor, pilot-decoder only); the fetched-branch claim stays
  `jumpIf32`-only. A unified fetched dispatch over `ControlCodec`
  would need a new decoder composition theorem (not attempted: it
  would touch the pilot dispatch story owned elsewhere).
- No liveness analysis or optimiser decision procedure; no TSO/GX,
  concurrency, cost, time, termination, source, checker, Spec or goal
  claim.

## Next useful independent task

Compose `fetchedJcc_stabil` with a multi-step fetched run
(`laufBytes`): agreement on consumed flags across a whole
conditional chain with a per-step read-set cover, or connect the
`zweigLaenge` bridge to an actual `ZweigBeleg` acceptance
(`zweigOk_weit`) for the fetched site.

## Task feedback

Nothing in the task appears wrong. Two readings were resolved by
derivation rather than assumption: (a) "derive fetch/decode identity
from equal code/map/RIP" is proved as `fetchDekodiert_gleich`
(including the `ausfuehrbarN` leg), and (b) "include CMOV/SETcc only
if supported by real byte-facing helpers" is honoured by keeping them
on `ControlCodec` byte steps with exact non-consumed-flag conditions
and stating the missing `fetchDekodiert` path as an explicit CUT
rather than forging one.
