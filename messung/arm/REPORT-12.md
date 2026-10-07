# Agent 12 report — Sequential Sail Arm: loads, stores and addressing

## Status

Follow-up task in progress: `arm/Arm/Isa/AtomicOps.lean` (exclusive
pairs, LSE atomics, prefetch). DONE is stale until the follow-up lands.

## Follow-up progress

- Coordinator merges landed in this clone: `Arm.Mem.Trace` (agent 11),
  `Arm.Mem.Exec/Dep/Axiomatic`, and `Arm.Mem.Atomics` (agent 09). The
  latter gives the shared vocabulary this lane reuses without
  redefining: `AtomicOp`, `atomicFun`, `casCmp`, `mask`,
  `AtomicAnn`, `atomicReadAcc`/`atomicWriteAcc`, `ExclKind`,
  `exclReadAcc`/`exclWriteAcc`. Its `atomicReadAcc` (read carries
  acquire iff A) and `atomicWriteAcc` (write carries release iff R) with
  `excl := false` settle the ordering/flag mapping; AL variants split
  across the two halves.
- `Arm.Mem.Trace.runEff` collided with the lane-local value
  interpreter, so `Arm.runEff` became `Arm.runEffV` (signature and
  behaviour unchanged) in `Addr.lean` and `LoadStore.lean`.
- Created `arm/Arm/Isa/AtomicOps.lean` (skeleton): `atomCheck` (Sail
  `v8_base.sail:28334`, `:22799`; atomicops fault misaligned at any
  ordering), `prfmImm` (Sail `instrs64.sail:39785`,
  `v8_base.sail:35873`; no SP check, no fault, no event) with `decide`
  theorems `prfmImm_ok`, `prfmImm_noSPcheck`, `atomicFun_add_bytes`.
- Extended `AtomicOps.lean`: `rawRead`/`rawWrite`, `ldxp`/`stxp`
  reusing agent 09's `exclReadAcc`/`exclWriteAcc` (Sail
  `instrs64.sail:28942`; 2x64 and 2x32 forms; load needs half alignment
  for 2x32 and full 16 for 2x64, stores need full size) with `decide`
  theorems `exLdxpStxp_ok`, `exStxpFail_ok`, the planted wrong case
  `exStxpFail_notPass`,   `exLdxp32_ok`, `exLdxp4ok_ok` and
  `exStxp4_refuses` (the asymmetric alignment rule pinned from both
  sides).
- Extended `AtomicOps.lean`: `ldAtom` (Sail `instrs64.sail:25698`,
  `:51771`; SWP/LD*/ST* via `t = 31`), `cas` (Sail
  `instrs64.sail:6382`) and `casp` (Sail `instrs64.sail:6494`), all on
  agent 09's `atomicReadAcc`/`atomicWriteAcc`/`atomicFun`/`casCmp`,
  with `decide` theorems `exLdadd_ok`, `exStadd_ok`, `exSwp_ok`,
  `exCas_ok`, `exCasFail_ok`, `exCasp_ok` and planted wrong cases
  `exLdadd_notNew`, `exSwp_notSwapped`, `exCasFail_notSuccess`.
  (`decide` caught a missing memory preset in the `sCASf` fixture.)
- Extended `AtomicOps.lean`: full LD-op coverage on the `sB` fixture
  (`exLdclr_ok`, `exLdeor_ok`, `exLdset_ok`, `exLdsmax_ok`,
  `exLdsmin_ok`, `exLdumax_ok`, `exLdumin_ok`) with the planted
  signedness wrong case `exLdsmax_notUmax`.

## Earlier work (accepted by the coordinator, 8 jobs green)

## What was done

New files (both imported at the end of `arm/Arm.lean`):

`arm/Arm/Isa/Addr.lean` — address computation and checked accessors:
- `isAligned` (Sail `v8_base.sail:28178`), `addOff` (Sail
  `instrs64.sail:39785`), `ExtendKind`/`extendKindParams` (Sail
  `v8_base.sail:35744`) and `extendReg` with the `Min(len, N - shift)`
  clamp (Sail `v8_base.sail:35780`).
- `rdBase`/`wrBase` (register 31 is SP), `checkSP` (Sail
  `v8_base.sail:22782`), `needsAlign` (Sail `v8_base.sail:22799`),
  `MemCfg` fault oracle, `memReadEff`/`memWriteEff` (Sail
  `v8_base.sail:28178`/`28260`).
- Fixture `Regs`/`State`, little-endian `loadNat`/`storeNat`,
  fuel-bounded interpreter `runEff`, fixtures `s0`, `sSP8`,
  `cfgNoFault`, `cfgFault`, helper `upd` (`Function.update` does not
  exist in this toolchain).
- `decide` theorems: `addrEx1_aligned4`, `addrEx1_misaligned3`,
  `addrEx1_addOff`, `extendReg_uxtx_id`, `extendReg_sxtw_sign`,
  `extendReg_uxth_shift`, `needsAlign_plain`, `needsAlign_acquire`,
  `needsAlign_excl`, `exRoundtrip_ok`, `exUnalignedPlain_ok`,
  `exUnalignedOrdered_refuses`, `exFault_refuses`, `exCheckSP_ok`,
  `exCheckSP_refuses`; planted wrong cases `extendReg_sxtw_notZero`,
  `exRoundtrip_notBE`.

`arm/Arm/Isa/LoadStore.lean` — execute-level semantics
(decoded fields to `Eff Unit`), each with `decide` examples and a
planted wrong case:
- `extVal` + `ldStSingle` (Sail `instrs64.sail:39785`, `:32821`,
  `:37495`): unsigned-offset, pre/post-index, unscaled LDUR/STUR,
  8/16/32/64-bit with sign/zero extension.
- `ldStReg` (Sail `instrs64.sail:35210`): register offset with extend
  and shift.
- `ldrLiteral` (Sail `instrs64.sail:32630`): PC-relative LDR/LDRSW.
- `ldpStp` (Sail `instrs64.sail:30833`, `:31505`): pairs, all modes.
- `ldarStlr` (Sail `instrs64.sail:28426`), `ldapr` (Sail
  `instrs64.sail:27312`).
- `ldxr`/`stxr` (Sail `instrs64.sail:29364`, `v8_base.sail:29075`),
  instruction side only: `stxr` takes the monitor verdict as a `passed`
  premise (owned by agent 09); pass stores + status 0, fail skips the
  store + status 1.

## Last build result

`./arm-bau` → `== exit 0; 0 error line(s) in the COMPLETE output`
(8 jobs). `#print axioms` for every theorem: no axioms or `[propext]`
only (standard). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
anywhere. All theorems are ground equalities proved by `decide` (no
universally quantified premises, so no `_zeuge` witnesses are owed).

## Open (nothing owned by this lane)

- Decoder mapping (agent 15), monitor behaviour (agent 09), SCTLR-gated
  and LSE2-quantified alignment rules plus translation (system agent).

## CUTS (honest)

- `checkSP` always enforced (SCTLR gating not modelled); `needsAlign`
  without SCTLR.A/LSE2 gating; `MemCfg.fault` abstracts translation.
- Prefetch, SIMD/FP (single and pair), nontemporal hint: not modelled.
- Exclusive pairs LDXP/STXP, atomics (CAS et al.): not covered.
- `ConstrainUnpredictable` overlaps take the definite behaviour.
- No MTE/SPE/syndrome state; LSE2 joined pairs are value-identical but
  emit two single events instead of one joined event.
- Value agreement with Sail is by citation plus ground examples, not by
  a simulation theorem (integration step, not this lane).
- Apparatus: `./arm-probe` on a new file needs one `./arm-bau` first to
  resolve `Arm.*` imports; `#print axioms` needs qualified names; a
  newline ends an application unless the continuation is indented past
  the application start (hoist split field values into their own `def`).
