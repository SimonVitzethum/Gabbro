# MUSE-REPORT-82 — The call machine with compound statements (attempt G)

## What was done

New file `grammatik/Grammatik/RufMaschineG.lean` (~1700 lines), wired into the
build via `import Grammatik.RufMaschineG` at the end of `grammatik/Grammatik.lean`.
Nothing else touched. `RufMaschineF.lean` was reused by import, never edited:
the witness reuses `rufDF`, `rufRhoF`, `rufOF`, `spF`, `leafSF`,
`leafSF_blatt`, `leafSF_ok`, `restF`, `eF`, `vF`, `rufHpF`, `rufArgsF`,
`rufCallerRumpfF`, `rhoCallerF`, `rufCallerF`, `rufIncF`, `heldLeerF`,
`argsOrteF`, `outWF`, `outWF_moves`, `initF`, `rufDF_params`.

## Design

Frame residue is a new `GRest D V l Γ Λ` (continuation stack in one type):
`ende` (plain end block), `dann` (block then rest), `schrumpf` (drop one
bound value), `frei L` (release marker, holdings-typed so the `locks` body
runs at `held L :: Λ`), `trav`/`travRest`, `wieder`/`wiederRest`,
`ewig`/`ewigRest` (loops with remaining indices/tries/budget plus a shim
that runs one iteration at loop context and resumes the loop).
`RufSchrittG` has 34 constructors: F-copies `blatt nimmt gibt ruf rueck`
(residues wrapped in `.ende`) plus 29 unfold steps. Reads go through the
read world `(weltVon).lese Λ orte` exactly as `execStmt` reads them;
`GEntfaltbar` routes only non-call compounds (`ite onOption locks
breaking traverse retry forever`) from `ende`-position into `dann`, so
`ruf` keeps ownership of `call`. The fidelity proof follows F exactly
(key stack ignores residue, new steps keep key triple + log):
`rufG_treu` with companion `rufG_treu_zeuge`.

## New names (machine)

`GRest` (+10 ctors), `RufRahmenG`, `RufFadenG`, `RufMaschineG`,
`RufMaschineG.weltVon`, `RufFreiG`, `rufEigenG`, `rufUpdateG`,
`rufUpdateG_self/noteq`, `GEntfaltbar`, `RufSchrittG` (+34 ctors:
`blatt nimmt gibt ruf rueck endeEntf dannBlatt dannLeer dannIteWahr
dannIteFalsch dannOnOptionSome dannOnOptionNone endeBind dannBind
dannNarrowOk dannNarrowElse dannPruefWahr dannPruefFalsch dannBreaking
dannLocks freiGib schrumpfVergiss dannTravWeiter dannTravFertig travNext
travFort travDone dannRetry wiederUeber wiederWeiter wiederSchritt
wiederFort dannForever ewigWeiter ewigFort rufDann`),
`RufStartG`, `RufErreichbarG`, `RufSchluesselG`, `RufFadenSchluesselG`,
`RufLogPasstG`, `RufFadenPasstG`, `rufRueckGedecktG`,
`rufLogPasstG_mem_eintritt/eintritt_mem/gedeckt`,
`rufFadenSchluesselG_behalte`, `rufFadenPasstG_behalte`,
`RufMaschinePasstG`, `rufStartG_passt`, `rufSchrittG_passt_acting`
(catch-all `_` closes 27 log-preserving steps; `ruf`/`rufDann`/`rueck`
have explicit branches), `rufSchrittG_passt_anders/passt`,
`rufErreichbarG_passt`, `rufG_treu`.

## New names (witness)

`cG thenG elseG iteG iteG_entf calleeG gP gP_rumpf_true M0G M0G_kopf
M0G_start M1G schritt1G reach1G M1G_kopf M1G_welt M2G schritt2G reach2G
M2G_kopf M2G_welt cG_orte M3G schritt3G reach3G M3G_kopf M3G_welt M4G
schritt4G reach4G M4G_kopf M5G schritt5G reach5G M5G_kopf M6G schritt6G
reach6G M6G_kopf s1G M7G schritt7G reach7G reach7G_start M7G_log M7G_slot
M7G_moves rufG_treu_zeuge`. Run (thread 0): `ruf`, `endeEntf`,
`dannIteWahr` (literal-`true` condition), `dannBlatt` (writing leaf,
slot 0 moves 0 -> 2), two `dannLeer`, `rueck`. `rufG_treu_zeuge`
instantiates all premises jointly and adds the memory move
(`M.speicher.slots () 0 () ≠ spF.slots () 0 ()`) as a fourth conjunct.

## Last build result

`./lean-bau` ends with `Build completed successfully (51 jobs).`
`./lean-probe grammatik/Grammatik/RufMaschineG.lean` reports
`0 error(s)`; `#print axioms` shows only
`[propext, Classical.choice, Quot.sound]` (project standard, no
`sorry`/`axiom`/`native_decide`/`unsafe` anywhere in the file).

## Coverage (as tasked)

Covered stepwise: `ite`, `onOption`, `locks`, `breaking`, `traverse`,
`retry`, `forever` (budget = `passes`), `let` (both levels), `narrow`,
`pruefung`, calls in blocks (`rufDann`). Leaves run atomically via
`execStmt` (`blatt`/`dannBlatt`). NOT covered: `onTag`/`onGrund`
(arm-selection helpers live only in `ref-wip`, not in this tree),
`callInd`, `bindCall*`/`bindAxiom`/`regLies*`/`awaits`/`exchange`/
`gleit*` (stuck `dann` heads), `leave`/`next`/`retGrund` in loop bodies
(stuck: `dannBlatt` needs `.ok`), exhausted `forever` budget / false
invariant (stuck; reference reports hardware/logic exits there),
top-level `ret` on empty stack (as in F). All listed in CUTS.

## What I believe is wrong or risky in the task

1. "if its bodies fit" for `refD`: they do not — neither `refP` body
   contains an `if`, so the witness builds on `rufDF` instead, as the
   task allows.
2. The `forever` budget silently reuses the machine-wide `passes`
   parameter; a program needing more iterations than the ambient fuel
   gets stuck with no diagnostic. This mirrors `execStmt` (which also
   takes `passes`) but the coupling is implicit.
3. `rufDann` advances the caller past the call while F's `ruf` leaves
   the stale call in the caller frame; after `rueck` the two disagree
   about what the caller does next. Fidelity (the only theorem) does
   not see this, but a future execution-correctness claim must pick one.
