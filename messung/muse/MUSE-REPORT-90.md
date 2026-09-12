# MUSE-REPORT-90 — Call machine G: the remaining statement forms

## What was done

Extended `grammatik/Grammatik/RufMaschineG.lean` (lane 82's file; nothing
else touched). `RufSchrittG` grows from 34 to 68 constructors; `rufG_treu`
stays green with its original witness plus a new one. Full `./lean-bau`
passes; `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`
for every new theorem. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## New names

Residue: `GRest.wartet` (caller waits for a bound call: bound block plus
continuation). Selection helpers: `armWahlG` (tag value chooses arm and
payload, like `execArms`), `grundWahlG` (grund value chooses arm, like
`execGrund`); `GEntfaltbar` now also true for `onTag`/`onGrund`.

Step rules (34): `dannOnTagSome`, `dannOnTagNone`, `dannOnGrund`,
`dannCallInd`, `rufCallInd` (pointer value resolved, callee pushed with
`eintritt` like `ruf`), `dannBindCall`, `dannBindCallInd`,
`dannBindCallElse` (push with `wartet` caller residue), `rueckBind` (pop,
bind value in caller env, log `rueck`), `dannLeaveTrav`,
`dannNextTrav`, `dannLeaveWieder`, `dannNextWieder`, `dannLeaveEwig`,
`dannNextEwig` (abrupt head at a loop shim; trav-leave checks the
invariant like `traverseLauf`, retry/forever exits are direct like
`retryLauf`/`foreverLauf`), `peelDannLeave`/`peelDannNext`,
`peelSchrumpfLeave`/`peelSchrumpfNext`, `peelFreiLeave`/`peelFreiNext`
(abandon holdings-uniform scaffolding; `frei` emits `gibt`),
`dannRet`, `rueckCons` (early return pops with a `rueck` event),
`dannRegLies`, `dannRegLiesElseWahr`/`Falsch`, `dannAwaits`,
`dannExchange`, `dannGleit`, `dannGleitLit`, `dannGleitVon`,
`dannGleitNarrowOk`/`Else`, `dannBindAxiom` (one layer deep, mirroring
each `execBlock` equation; value pushed, body stepwise under `schrumpf`).

Fidelity: `rufPushG_passt`, `rufPopG_passt` (key-stack argument factored
out of the old inline proofs) plus explicit `rufSchrittG_passt_acting`
branches for the eight log-touching constructors
(`dannCallInd`, `rufCallInd`, `dannBindCall`, `dannBindCallInd`,
`dannBindCallElse`, `rueckBind`, `dannRet`, `rueckCons`); all other new
steps keep key triple and log and fall into the catch-all.

Witness (9 steps from the start state): `bisH`, `bisH_orte`, `leaveH`,
`restLeaveH`, `leaveHd`, `bodyH`, `retryStmtH`, `retryH_entf`,
`driverRet` (reuses `restF`: contracts coincide by computation),
`driverBodyH`, `hP` (writer `true` = `rufRumpfF`, driver `false` = loop),
`hP_rumpf_false`, `hP_rumpf_true`, `M0H`, `M0H_kopf`, `M0H_start`,
`H1H`–`H9H` with `schritt1H`–`schritt9H`, `reach1H`–`reach9H`,
`H1H_kopf`/`H1H_welt`, `H2H_kopf`/`H2H_welt`, `H3H_kopf`/`H3H_welt`,
`H4H_kopf`/`H4H_welt`, `H5H_kopf`, `callerH`, `s1H`, `H6H_kopf`,
`H6H_log`, `H7H_kopf`, `H8H_kopf`, `H9H_log`, `H9H_slot`, `H9H_moves`,
`reach9H_start`, and the joint witness
`rufG_treu_zeuge_bind_leave` (loop with `leave` + bind-call + memory
move 0 -> 2 at slot 0, `rueck` in log with matching `eintritt`).

## Last build result

`./lean-bau` ends with `Build completed successfully (53 jobs).`
`./lean-probe grammatik/Grammatik/RufMaschineG.lean` reports
`0 error(s)`.

## Coverage table

Leaves (`assignSlot`, `assignDurch`, `assignGlob`, `schreibBytes`,
`assignVar`, `uebergang`, `axiomCall`, `regSchreib`, `transition`,
`publish`, `advances`, `retires`): `blatt`/`dannBlatt`. `ite`,
`onOption`, `locks`, `breaking`, `traverse`, `retry`, `forever`, `let`,
`narrow`, `pruefung`: old unfold steps. `onTag`, `onGrund`, `callInd`,
`bindCall`, `bindCallInd`, `bindCallElse` (ok-path), register/atomic/
float binders, `leave`/`next` at loop shims and through
holdings-uniform scaffolding, early `ret`: new steps above.
Not covered, why: `retGrund`/`Endblock.retGrund` anywhere and the
`bindCallElse` grund path (no log event names a grund value; a silent
pop breaks `RufLogPasstG`); `leave`/`next` at `ende` position
(else-branch jumps discard the loop shim -- needs shims threaded
through else-branches); peels through holdings-changing scaffolding
(`advances`/`retires` mid-block) or `wartet` (unreachable as a live
continuation); exhausted `forever` budget / false invariants
(`hardware .fortschritt` / `logik .schleife`); top-level `ret` on an
empty stack (as in F). Full detail in the file's CUTS block.

## What remains open

- An execution-correctness theorem (machine steps agree with
  `execStmt`/`execBlock`/`execEnd`) -- the step rules mirror the
  equations premise by premise, but no theorem says so.
- Grund returns end-to-end (needs a log event for grund plus the
  invariant extended over it).
- `ende`-position abrupt exits (shim-preserving else-branches).

## Findings (mechanically verified, relevant beyond this lane)

1. Auto-bound implicit type indices in inductive constructor binders
   break downstream `cases ... with` matching: adding `dannGleit` with
   free `l1 h1 l2 h2` turned every later alternative into garbage
   (bisected to the single constructor; explicit binders fixed it).
   Lanes adding float-typed constructors should bind indices explicitly.
2. `rueckBind` must rebuild the caller frame from projections (the
   residue changes), unlike `rueck` which reuses it whole: the machine
   def has to be written in rule-conclusion shape or `rfl`/`exact`
   fail on structure eta.
3. Peel soundness is a holdings question, not just a control question:
   abandoning a block is only valid if it preserves holdings, so the
   peel rules pin the abandoned prefix to uniform holdings. The type
   checker found this, not review.
4. No new theorem added here has a universal premise over program
   syntax (only step constructors, fidelity branches over machines,
   and concrete witness definitions), so rule 13 needs no further
   witnesses; the ZEUGE target `rufG_treu` keeps its original witness
   and gains `rufG_treu_zeuge_bind_leave`.
