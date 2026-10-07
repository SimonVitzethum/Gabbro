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
- Extended `Addr.lean`: `ExtendKind` (Sail `v8_base.sail:35744`),
  `extendKindParams` and `extendReg` (Sail `v8_base.sail:35780`, including
  the `Min(len, N - shift)` clamp and the signerc/zero extension), with
  `decide` theorems `extendReg_uxtx_id`, `extendReg_sxtw_sign`,
  `extendReg_uxth_shift` and the planted wrong case
  `extendReg_sxtw_notZero`.
- Extended `Addr.lean`: `rdBase`/`wrBase` (register 31 is SP),
  `checkSP` (Sail `v8_base.sail:22782`), `needsAlign` (Sail
  `v8_base.sail:22799`), the `MemCfg` translation-fault oracle,
  `memReadEff`/`memWriteEff` (Sail `v8_base.sail:28178`/`28260`) with
  `decide` theorems `needsAlign_plain`, `needsAlign_acquire`,
  `needsAlign_excl`.
- Extended `Addr.lean`: the tiny sequential fixture `Regs`/`State`,
  little-endian `loadNat`/`storeNat` (Sail `v8_base.sail:28178`/`28260`),
  the fuel-bounded interpreter `runEff` (`raise` is `none`,
  `rdSys`/`wrSys` refuse, barriers step over), fixtures `s0`,
  `cfgNoFault`, `cfgFault`, and the helper `upd` (`Function.update` does
  not exist in this toolchain).
- Extended `Addr.lean`: accessor-level `decide` examples `exRoundtrip_ok`,
  the planted endianness wrong case `exRoundtrip_notBE`,
  `exUnalignedPlain_ok` (misaligned plain reads proceed bytewise),
  `exUnalignedOrdered_refuses`, `exFault_refuses`, `exCheckSP_ok` and
  `exCheckSP_refuses` (fixture `sSP8`).
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
