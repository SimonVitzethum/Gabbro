# Agent 12 report — Sequential Sail Arm: loads, stores and addressing

## Status

ALL deliverables done, committed and green. Work stops here.

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
