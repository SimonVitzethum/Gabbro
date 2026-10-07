# Agent 07 report — Arm axiomatic memory model (`arm/Arm/Mem/Axiomatic.lean`)

## Status: DELIVERABLES COMPLETE
- New file `arm/Arm/Mem/Axiomatic.lean` (~210 lines) + one import line at the
  end of `arm/Arm.lean`. Full build `./arm-bau`:
  `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (7 jobs)`.
- Probe `./arm-probe arm/Arm/Mem/Axiomatic.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- Commits: `2870a5eb` skeleton, `4f152bda` coherence relations,
  `54fe478c` dob/axioms, `9d742351` witnesses/theorems (+ final commit).

## Definitions (all in `namespace Arm`)
- `OrderingParts` — structure with `aob : Rel; bob : Rel` (plug-in for agents
  09/10); `noParts` (empty plug-in for the witnesses).
- Endpoint helpers: `isReadEv`, `isWriteEv`, `sameCorePair`, `sameLocPair`,
  `acc`, `Rel.union`, `Rel.inter`, `targetIs` (the `;[S]` restriction).
- Derived relations: `fr` (`rf^-1;co`), `rfi`/`rfe` (same-/cross-core `rf`),
  `fre` (cross-core `fr`), `coe` (cross-core `co`), `po_loc` (same-address
  `po`), `dob` (five clauses: `addr|data`, `ctrl;[W]`,
  `(ctrl|addr);po;[W]`, `addr;po;[W]`, `(addr|data);rfi`), `obs`
  (`rfe|fre|coe`), `ob` (`obs|dob|aob|bob`).
- Axioms (all `Bool`, decidable): `internal` (acyclic `po_loc|co|rf|fr`),
  `external` (acyclic `ob`), `atomic` (`rmw & (fre;coe)` empty),
  `consistent` (conjunction of the three, well-formedness-independent).

## Theorems (13, all `by decide`)
- `wit_coherent_ok`: `consistent noParts xCoherent = true` (message passing
  with initial writes, no barriers — allowed, so consistent).
- `wit_coherence_bad*`: cyclic-`co` fails `internal` only (external/atomic true).
- `wit_lb*`: load buffering with address dependencies fails `external` only.
- `wit_rmw*`: split exclusive pair fails `atomic` only.
- `#print axioms` for the four `consistent` verdicts: each depends only on
  `[propext]` (standard).

## Sources and honesty notes
- Clauses cite Arm ARM B2.3 / `aarch64.cat` by section and name FROM THE
  AGENT'S KNOWLEDGE OF THE PUBLISHED MODEL, NOT A MEASURED COPY: the Arm ARM
  text is not on this machine and no `.cat` file is vendored in this clone
  (checked: no `**/*.cat` in the clone). The Sail citation rule of
  ARM-VORSPANN §7 does not apply here — the memory model is not in the Sail
  ISA sources; the task file orders B2.3/`aarch64.cat` citations instead.
- One judgment call: the `dob` clause `addr;po;[W]` is a subset of
  `(ctrl|addr);po;[W]`; both are kept (union is idempotent over subsets, so
  this is semantically harmless and preserves the published clause shape).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. All theorems are closed
  `Bool` equations (no `Prop`-typed premises, no unused premises). Toolchain
  notes: dot notation on `let`-bound lists needs a `: Rel` annotation (else
  `List.union` is sought); `|>.union` after a union chain mis-parses — both
  fixed with explicit `Rel.union`.
- Frozen files `Basic.lean`/`Event.lean` untouched. Only `Arm.lean` (import
  line) and the new file were edited.

## CUTS (honest)
- NOT modelled: mixed-size accesses, address translation, instruction-side
  effects, `aob`/`bob` contents (agents 09/10 own them).
- `consistent` assumes nothing about `Exec` well-formedness (agent 06 owns it).
- `dob` clause fidelity rests on knowledge, not on a measured copy (see above).
