# Agent 07 report — Arm axiomatic memory model (`arm/Arm/Mem/Axiomatic.lean`,
`arm/Arm/Mem/Model.lean`)

## Status: FOLLOW-UP IN PROGRESS (coordinator note: points 2 and 3 open)
- `arm/Arm/Mem/Axiomatic.lean` + one import line at the end of `arm/Arm.lean`.
  Point (1) done: `dob` repaired to the six published clauses (commit
  `63e0953a`); ISB witnesses committed (`2704b7b0`).
- Point (2) is THIS section (confidence per clause). Point (3) is
  `arm/Arm/Mem/Model.lean` (litmus verdicts MP/SB/LB/2+2W/R/S) — in progress.
- Last full build `./arm-bau`:
  `== exit 0; 0 error line(s) in the COMPLETE output`.
- Commits: `2870a5eb` skeleton, `4f152bda` coherence relations,
  `54fe478c` dob/axioms, `9d742351` witnesses/theorems, `cfb8c57c` model
  complete, `63e0953a` dob-ISB repair, `2704b7b0` ISB witnesses.

## Definitions (all in `namespace Arm`)
- `OrderingParts` — structure with `aob : Rel; bob : Rel` (plug-in for agents
  09/10); `noParts` (empty plug-in for the witnesses).
- Endpoint helpers: `isReadEv`, `isWriteEv`, `sameCorePair`, `sameLocPair`,
  `acc`, `Rel.union`, `Rel.inter`, `targetIs` (the `;[S]` restriction).
- Derived relations: `fr` (`rf^-1;co`), `rfi`/`rfe` (same-/cross-core `rf`),
  `fre` (cross-core `fr`), `coe` (cross-core `co`), `po_loc` (same-address
  `po`), `dob` (six clauses: `addr|data`, `ctrl;[W]`,
  `(ctrl|addr;po);[ISB];po;[R]`, `addr;po;[W]`, `(addr|data);rfi`), `obs`
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
- One judgment call, repaired on coordinator order: the first version had a
  `(ctrl|addr);po;[W]` clause, which is STRONGER than the published model
  (`ctrl` already spans all `po`-later events, so the extra `;po` over-orders).
  Removed; `dob` is now exactly the six clauses the coordinator stated.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. All theorems are closed
  `Bool` equations (no `Prop`-typed premises, no unused premises). Toolchain
  notes: dot notation on `let`-bound lists needs a `: Rel` annotation (else
  `List.union` is sought); `|>.union` after a union chain mis-parses — both
  fixed with explicit `Rel.union`.
- Frozen files `Basic.lean`/`Event.lean` untouched. Only `Arm.lean` (import
  line) and the new file were edited.

## Confidence per clause (point 2 of the follow-up; reviewer guidance)

Reproduced from memory of the published `aarch64.cat` / Arm ARM B2.3 — NOT a
measured copy (no Arm ARM text, no `.cat` file on this machine). Where to look:

HIGH confidence (headline structure, stable across all published versions):
- `fr = rf^-1;co`; the int/ext splits `rfi`/`rfe`/`coe` (and `fre = fr & ext`).
- `obs = rfe | fre | coe`; `ob = obs | dob | aob | bob` (plug-in shape).
- `internal`: `acyclic (po-loc | co | rf | fr)`.
- `external`: `acyclic ob`.
- `atomic`: `empty (rmw & (fre;coe))`.
- `dob` clauses `addr | data`, `ctrl;[W]`, `addr;po;[W]`.

MEDIUM confidence (present in the published model, exact scope less certain):
- `dob` clause `(addr|data);rfi` (dependency feeding an internally-observed
  write; direction and restriction could differ in detail).
- The ISB clause `(ctrl|addr;po);[ISB];po;[R]` (transcribed from the
  coordinator's statement, which this agent accepts as authoritative; the
  agent's own prior memory of this clause was the gap that caused point 1).
- `po_loc` as "same-address `po`" (ignores the same-cacheline vs same-byte
  and mixed-size subtleties — mixed-size is declared NOT modelled).
- Litmus names R/S/2+2W in `Model.lean` (canonical for MP/SB/LB; R/S/2+2W
  are standard coherence readings but exact historical variants may differ —
  each shape is fully explicit in the file, so the verdicts stand regardless).

LOW confidence / known gaps (reviewer: check here first):
- Whether the six `dob` clauses are COMPLETE (no seventh clause, e.g. around
  explicit `CAS`/exclusive success ordering — that belongs to `aob`/agent 09).
- `sameLocPair` by exact `BitVec 64` address equality (no aliasing, no
  translation, no size/overlap handling).
- Anything about `aob`/`bob` contents (agents 09/10) and `Exec`
  well-formedness (agent 06): `consistent` is deliberately independent of both.

## CUTS (honest)
- NOT modelled: mixed-size accesses, address translation, instruction-side
  effects, `aob`/`bob` contents (agents 09/10 own them).
- `consistent` assumes nothing about `Exec` well-formedness (agent 06 owns it).
- `dob` clause fidelity rests on knowledge, not on a measured copy (see above).
