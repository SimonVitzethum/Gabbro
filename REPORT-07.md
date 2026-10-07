# Agent 07 report — Arm axiomatic memory model (`arm/Arm/Mem/Axiomatic.lean`)

## Status
- Step 1 done: skeleton `arm/Arm/Mem/Axiomatic.lean` with `OrderingParts`
  (`aob`, `bob` plug-in for agents 09/10), `noParts`, `isReadEv`, `isWriteEv`,
  `sameCorePair`, `sameLocPair`. Probe: `== 0 error(s) in the COMPLETE output; exit 0`.
  Full build `./arm-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`.
- Open: derived relations (`rfe`, `fre`, `coe`, `rfi`, `fr`, `po_loc`, `dob`,
  `obs`, `ob`), the three axioms (`internal`, `external`, `atomic`),
  `consistent`, witnesses (one passing + three failing executions), the
  `import` line in `arm/Arm.lean`, final build, `.agent/DONE`.

## Definitions so far
- `Arm.OrderingParts` — structure with `aob : Rel; bob : Rel`.
- `Arm.noParts`, `Arm.isReadEv`, `Arm.isWriteEv`, `Arm.sameCorePair`, `Arm.sameLocPair`.

## Sources
- Arm ARM section B2.3 and Arm's herd model `aarch64.cat`, from the agent's
  knowledge of the published model, NOT a measured copy (the Arm ARM text is
  not on this machine; no `.cat` file is vendored in this clone — checked).
- Frozen vocabulary: `arm/Arm/Mem/Event.lean`, `arm/Arm/Basic.lean` (not edited).

## CUTS (honest, current)
- Only the skeleton exists; no axiom is stated yet, nothing is proved.
- Planned exclusions (per task): mixed-size accesses, address translation,
  instruction-side (I-side) effects are not modelled.
