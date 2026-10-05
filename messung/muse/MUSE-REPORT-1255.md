# MUSE-REPORT-1255: Pipeline calls with three-or-more-statement callee bodies

## What was done

New file `grammatik/Grammatik/X86/PipelineCallsN.lean` (plus one import line
appended to `grammatik/Grammatik.lean`), generalising `PipelineCallsExec`
(single-assignment callee bodies) to callee bodies that are chains of three
or more `assignSlot` statements. For an admitted caller frame and validated
callee bytes, the fetched byte-level run reaches the end of the code with the
world of the REAL `execBlock` run represented, the environment represented,
and every callee-saved register preserved across the WHOLE body. Unsupported
shapes are REFUSED, never guessed. Rust out of scope. No existing file was
edited except the one import line; `OptimizationRules`/`OptimizationWitnesses`
untouched.

## New definitions and theorems (exact names)

Shape and validator (`§1`): `istAssignStmt`, `istAssignBlock`, `blockLaenge`,
`istDreiPlus`, `rufExecN`, `rufExecN_teile`.
Refusals (`§2`): `istDreiPlus_verweigert_form`, `istDreiPlus_verweigert_kurz`,
`rufExecN_verweigert_rot`, `rufExecN_verweigert_form`,
`rufExecN_verweigert_kurz`, `rufExecN_verweigert_bytes`.
Induction (`§3`): `istAssignBlock_cons_inv`, `assignChunkN_lauf`,
`assignBlockN_lauf_aux` (fuel version: `Block` is mutually inductive, so the
`induction` tactic does not apply; induction runs on `sizeOf` fuel with
`cases` splits, the `rumpfBlock_total_aux` pattern), `assignBlockN_lauf`.
Correctness (`§4`): `rufExecN_korrekt`.
Witness (`§5`): `nwV6`, `nwV42`, `nwBody` (three assignments), `nwProg`,
`nwBytes`, `nw_laenge`, `nw_drei`, `nw_rufExecN` (validator accepts, by
computation), `nwChunk1/2/3`, `nwMemBytes`, `nwCode`, `nwDaten`, `nwMem`,
`nwStart`, `nw_laenge_bytes`, `nw_code`, `nw_worldRep`, `nw_envRepr`,
`nw_rip`, `nw_quelle` (source run `7 -> 35 -> 42` on row 0, `9 -> 6` on
row 1, by `rfl`), `nw_chunks_laufen` (three reached chunk runs, by `rfl`).
Probes (`§6`): `nwProbe_kurz` (one-statement body), `nwProbe_form` (body
with a check), `nwProbe_rot` (red zone), `nwProbe_bytes` (tampered byte).
Joint witness (`§7`): `rufExecN_korrekt_zeuge` (admitted frame, disjoint
registers, validated bytes, code region, represented world/environment,
reached source run, reached byte run with all six callee-saved registers
preserved, chunk runs composed via reused `ketteLauf_lauf`, reached frame
saves with observably changed result byte; non-degenerate: `pwV` writes
its table and every run changes memory).

Reused unchanged: `senkBlock_assign`, `senkWertT`/`senkWertT_gerade`,
`einzelChunk_lauf`, `worldRep_store`, `lauf_zu_laufBytes`,
`validate_sound`, `optimise_nil`, `repOk_int`, `constInt?_sound`,
`execStmt_assignSlot`, `lauf_anhang`, `addrOff_null`, `addrOff_natAdresse`,
`rufOk`/`calleeGerettet`/`pipeline_ruf_verweigert_rot`/`rufWit_*`,
`calleeFremd`/`calleeFremd_mem`/`cwCfg`/`cw_fremd`/`cw_cfgOk`/`cwReg`,
`pwD`/`pwV`/`pwL`/`pwO`/`pwR`/`pwCtx`/`pwIdx0`/`pwWert0`/`pwHw`/`pwHL`/
`pw_layoutSep`/`codeAt_von`/`witnessFlags`, `KetteLauf`/`ketteLauf_lauf`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineCallsN.lean`: 0 errors.
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` in the new file
  (only the English word "admitted" in two doc comments).
- `#print axioms` for every new definition/theorem: at most
  `propext`, `Classical.choice`, `Quot.sound` (the standard set); several
  are axiom-free.
- Last `./lean-bau` result line: `Build completed successfully (644 jobs).`

## What remains open (see CUTS in the file)

Only all-`assignSlot` bodies of length three or more are covered; shorter
bodies, `ite`/checks/loops/calls/gates/floats, optimiser certificates,
TSO/GX, time/budget transfer, loader/entry/relocation, callee-saved
push/pop emission and silicon correspondence stay open/refused as stated.

## What I believe is wrong in the task

Two named predecessors do not exist in this tree: lane 1229's
`PipelineCallsBlock.lean` (`istZweiZuweisung`) and
`PipelineChunkDerive.lean`. I generalised directly instead:
`istDreiPlus` covers every all-assignment body of length three or more
(pairs only by refusal here), induction runs on the `Block` itself
(fuel + `cases`, since `Block` is mutually inductive), and chunk-run
composition reuses `PipelineBlockInduct` (`KetteLauf`, `ketteLauf_lauf`)
(load-bearing in the joint witness). A `pipeline_refuses_*` correspondence
in the style of `pipeline_refuses` (failed-check route to a refusal exit)
is not included: all-assignment bodies cannot fail a check
(`senkBlock_ausgang` admits only `ok`/`grund`, and no `pruefung` lowers
here), so there is no refusal exit to reach; the refusal side is covered
by the four validator refusals plus four poison probes instead.

## Addendum: independent review 1256 (procedural REPAIR, no substance)

Review lane 1256 returned VERDICT: REPAIR against candidate
`f51af8d268cf0416f1084c68cb9004a816f02785`, judging REVIEWABILITY only:
the pinned commit had no objects inside the reviewer clone
(`/home/simon/Dokumente/gabbro-muse/a1256`), so zero checklist items were
executed and NO defect in `PipelineCallsN.lean`, its proofs, its witness,
or this report is claimed there.

Response from lane 1255:

- No substantive finding exists to resolve, so no Lean change was made:
  editing green proved code without a finding would be change for its own
  sake. Source guarantees are unweakened (nothing touched), no desired
  correctness is assumed, and no claim is overstated.
- The candidate was re-verified fresh in its own clone/branch
  (`/home/simon/Dokumente/gabbro-muse/a1255`, `muse/1255`):
  `./lean-probe grammatik/Grammatik/X86/PipelineCallsN.lean` reports
  `0 error(s)`; `./lean-bau` reports
  `Build completed successfully (644 jobs).`
- The fetchability blocker is coordinator infrastructure (shipping the
  candidate objects into the reviewer clone before dispatching exact
  reviews), outside this lane's owned files and unreachable under HARD
  RULES (no push, no network, nothing outside this directory). Resubmission
  with the pinned commit readable in the reviewer clone can proceed
  straight to the content checklist; this candidate needs no repair first.

## Addendum 2: re-review of snapshot `abb24fbd` (again procedural, no substance)

Review lane 1256 re-ran against the new pinned head `abb24fbdc89fad...`
(the report-only commit from the previous addendum) and returned REPAIR
again for the same boundary reason: the pinned commit has no objects in
the reviewer clone, so the content checklist was not executed and again
NO defect is claimed. Standing response is unchanged: no Lean change
(no finding to resolve), candidate re-verified fresh
(`./lean-probe .../PipelineCallsN.lean`: `0 error(s)`;
`./lean-bau`: `Build completed successfully (644 jobs)`).
