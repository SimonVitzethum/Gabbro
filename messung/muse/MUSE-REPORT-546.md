# MUSE-REPORT-546: N13 ContractSites (non-gated half)

Lane 546, branch `muse/546`, clone `/home/simon/Dokumente/gabbro-muse/a546`
(verified at start). Owned files only: `grammatik/Grammatik/X86/ContractSites.lean`
(new), one additive import line in `grammatik/Grammatik.lean`, this report.
No existing file touched; friend paths untouched; no second IR; no new executor.

## What was built

`grammatik/Grammatik/X86/ContractSites.lean` (374 lines) proves the non-gated
half of NEXT-PROOF-WAVE N13 over the real source model: call-site contract
application and preservation at actual entry/return parameter/result worlds,
with no `forall rho` / `forall v` weakening anywhere.

Definitions/theorems (all in `Gabbro.Grammatik.X86`):

- `FernVertrag` (inductive, intentionally empty) + `kein_fern_vertrag`:
  the inadmissible shape (WITNESS-): a contract use with the call values
  quantified away does not exist. Axioms: `[propext]`.
- `callSite_vorOk`: a `Stmt.call` that runs clean through `execStmt` with
  the `rufAt` handler leaves `requires` true at the ACTUAL argument
  environment (`evalArgs` at the args-read world). Inversion follows the
  `execStmtH_call_fall` case shape (`grund` impossible by `hr`, `logik` /
  `hardware` contradict `.ok`); the `ok` case reuses `AufrufOpt.rufAt_ok_vorOk`
  (nothing reproved).
- `rufAt_ok_gibt_ens`: a `.ok` outcome of `rufAt` at depth `fuel + 1`
  carries `RufEnsCheck` (true `ensures` over the ACTUAL result between the
  entry-side and return-side read worlds) plus the return-world identity.
  Derived through the shared unfolding `RufAtNachB.rufAt_fall_nach`.
  This closes the return-duty extraction that `AufrufOpt` lists as OPEN
  (`InlinePflicht.nachOk` was stated there, only `vorOk` derived).
- `inlinePflicht_aus_rufAt` (def): one successful `rufAt` outcome yields the
  full `InlinePflicht P caller g Λ` with actual `rho`/worlds/result --
  `hp`/`hr` carried, `vorOk` from the gate, `nachOk` from `rufAt_ok_gibt_ens`
  at the body-return world (whose ensures-read is exactly `sret`, so no
  trace-frame lemma was needed).
- `vertrag_bricht_nach_schreiber`: any world with `konto[0] = 0` refuses
  `pruefe`'s entry contract (via `of_decide_eq_true`, the same extraction
  `geistRekon_zeuge` uses) -- the concrete obstruction for a contract used
  across an invalidating writer.
- `pruefe_requires_falsch_am_start`: the start world already refuses it.
- `ort_statt_allquantor`: `EnsAmRueck miniContrP fTrue ...` holds
  (`mini_ens_am_ort`) while `QEnsuresB miniContrP fTrue miniWelt` is false
  (`mini_qensures_falsch`) -- quantifying away is false, not weaker.
- `callSite_vorOk_zeuge`: joint premise instantiation for `callSite_vorOk`
  on the real `setze` call (the `execStmt` equation holds by reduction).
- `rufAt_ok_gibt_ens_zeuge`: joint premise instantiation for
  `rufAt_ok_gibt_ens` (body outcome and `.ok` outcome both by reduction)
  plus `RufEnsCheck`, the written table, the `0 -> 5` memory change and the
  discharged `Nonempty (InlinePflicht eP eHaupt eSetze [])`.
- `vertragStandort_lauf_zeuge`: reached five-step run (replaying
  `geistRekon_zeuge` + `eP_zertifiziert`) with the real ghost pair in the
  log, `0` at start / `5` at entry, `ReqAmEintritt` at the actual entry and
  `FolgeLog Φ50` -- table-writing, memory-changing, non-degenerate.

`#print axioms` for every theorem: `[propext]` once, otherwise exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`; every premise of every theorem is used.

## Build evidence

- `./lean-probe grammatik/Grammatik/X86/ContractSites.lean`: 0 errors
  (final).
- `./lean-bau` (full project): `Build completed successfully (416 jobs)`,
  including `Built Grammatik.X86.ContractSites` and `Built Grammatik`.

## What remains open (see CUTS in the file)

IR lowering closure is WAITING on lane 287 and stays OPEN: everything here
is source-side; the SCFG/target bridge (QUELLBRUECKE phase B) is the named
open dependency. Further cuts: `hp`/`hr` carried not discharged; indirect
calls have no site form; `Block.bindCall` not separately wrapped (the return
half lives at the `rufAt` outcome both arms consult); no executable
body-splice simulation (same cut as `AufrufOpt`); no budget/timing claims.

## Notes on the task (plainly stated)

- The N13 row lists `Zugriffe` under USES. The non-gated (source-side) half
  does not need target footprints, so `Zugriffe` is not imported here; it
  belongs to the gated lowering half with the 287 interface. If the reviewer
  wants the import cited anyway, say so -- it would be an unused import.
- WITNESS+ asks for "inlined call preserving the call log". That preservation
  is already proved (`geistRekon_folge`, both channels, in `AufrufOpt`) and
  is reused, not duplicated, here; my witnesses cover the site-duty side
  (`InlinePflicht` discharge) plus the same M5 log-shape run. The executable
  inline rewrite itself stays OPEN (stated in CUTS).
- Follow-up suggestion (not done: file owned elsewhere): `AufrufOpt.lean`'s
  CUTS still lists return-duty extraction as OPEN; `rufAt_ok_gibt_ens` here
  proves it in site form, so that CUTS entry can be reworded on merge.
