# Agent 12 report — Sequential Sail Arm: loads, stores and addressing

## Status

Skeleton of `arm/Arm/Isa/Addr.lean` is green.

## What was done

- Read the frozen vocabulary (`arm/Arm/Basic.lean`, `arm/Arm/Isa/Monad.lean`)
  and the Sail sources for the memory accessors and the load/store `execute`
  clauses (`v8_base.sail`: `CheckSPAlignment`, `AArch64_UnalignedAccessFaults`,
  `Mem_read`/`Mem_set`; `instrs64.sail`: literal, post-index, ordered,
  exclusive-single, pair, unsigned-immediate, register-offset and
  signed-offset-normal execute functions).
- Created `arm/Arm/Isa/Addr.lean` (skeleton, 40 lines): `isAligned`
  (Sail `v8_base.sail:28178`), `addOff` (Sail `instrs64.sail:39785`),
  fixture `addrEx1`, theorems `addrEx1_aligned4`, `addrEx1_misaligned3`,
  `addrEx1_addOff`, all proved by `decide`. Ends with CUTS block and
  `#print axioms Arm.addrEx1_aligned4` (no axioms).
- Warmed the build once with `./arm-bau` (needed so `./arm-probe` resolves
  the `Arm.*` imports of a not-yet-imported new file).

## Last build result

`./arm-probe arm/Arm/Isa/Addr.lean` → `== 0 error(s) in the COMPLETE output;
exit 0`; `'Arm.addrEx1_aligned4' does not depend on any axioms`.

## Open

- `Addr.lean`: register extension (`ExtendReg`), SP/base helpers with
  `CheckSPAlignment`, `MemCfg` fault oracle, `memReadEff`/`memWriteEff`
  accessors with alignment and fault exceptions, the `Eff` interpreter
  fixture with `decide` examples and planted wrong cases.
- `LoadStore.lean`: all instruction semantics (loads, stores, pairs,
  ordered, exclusives) with per-family examples and wrong cases.
- `arm/Arm.lean`: the two `import` lines.
- Apparatus note: `./arm-probe` on a new file fails with
  `unknown module prefix 'Arm'` until `./arm-bau` has built the imported
  modules once; also `#print axioms` needs the fully qualified theorem name.

## CUTS (honest)

- Only the alignment test and offset addition exist; no instruction semantics
  yet, no register extension, no SP check, no memory accessor, no fault path.
- `isAligned`/`addOff` are pure functions; their agreement with Sail is by
  citation and ground examples, not by a simulation theorem (that theorem
  belongs to a later integration step, not to this lane).
