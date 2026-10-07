# REPORT-09 — Multicore: exclusives and atomics

Agent 09 of 15. Clone `/home/simon/Dokumente/gabbro-arm/work/09`, branch `arm/09`.
File: `arm/Arm/Mem/Atomics.lean` (+ one `import Arm.Mem.Atomics` line at the end of `arm/Arm.lean`).

## Status — ALL DELIVERABLES DONE

- [x] Exclusive monitors (LDXR/LDAXR/STXR/STLXR) as a state machine.
- [x] LSE atomics (CAS, SWP, LDADD, LDCLR, LDEOR, LDSET, LDSMAX/MIN, LDUMAX/MIN + A/R variants).
- [x] `aob : Exec -> Rel` + atomicity axiom statement.
- [x] Spin-lock witness: mutual exclusion on the two-core fixture, planted violation refused.
- [x] Import line in `arm/Arm.lean`, full `./arm-bau` green, `.agent/DONE` created.

## Build (last)

`./arm-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (7 jobs)`.
`./arm-probe arm/Arm/Mem/Atomics.lean`: `== 0 error(s) in the COMPLETE output; exit 0`.

## What was built (exact names)

Instruction side (`Arm` namespace, `arm/Arm/Mem/Atomics.lean`):
- `ExclKind` (`ldxr|ldaxr|stxr|stlxr`), `AtomicAnn` (`acq rel : Bool`), `AtomicOp`
  (`cas|swp|add|clr|eor|set|smax|smin|umax|umin`).
- `exclReadOrd`, `exclWriteOrd`, `exclReadAcc`, `exclWriteAcc` (`excl := true`,
  LDAXR acquires / STLXR releases).
- `atomicReadAcc`, `atomicWriteAcc` (`excl := false`: Sail sets `atomicop`, not
  `exclusive`, hence `AV_atomic_rmw`; A bit -> acquire on the read, R bit -> release
  on the write).
- `mask`, `toSigned`, `atomicFun` (the `MemAtomicOp_*` match; CAS decided by `casCmp`),
  `casCmp` (masked compare; mismatch skips the write, so a failed CAS contributes a
  lone read and no `rmw` pair).

Monitor machine:
- `overlap` (byte-range overlap clearing), `ExclState` (`perCore`, `shared`;
  fields NOT named `local`/`global`: both are reserved words in field position and
  do not parse — measured), `exclInit`, `monGet`, `monSet`.
- `ldxStep` (sets local, and shared when shareable), `storeStep` (clears OTHER
  cores' overlapping reservations; own monitor untouched), `stxPass`,
  `stxOutcomes` (`[0,1]` when set — spurious failure is FREE, `[1]` when not),
  `stxStep` (unconditional own-local clear).

Memory-model part (for agent 07's `OrderingParts.aob`):
- `isAcqRead`, `coreOf?`, `sameCore` (missing event counts as same-core: no
  spurious external edge), `frOf` (`rf.inv.comp co` over frozen `Rel`),
  `freOf`, `coeOf`, `atomicViolations` (`fre;coe` filtered to `rmw`),
  `atomicityHolds` (`violations == []`), `rmwWrites`, `isAcqReadId`, `aob`
  (`rmw` plus the acquire read forwarded from an `rmw` write).

Theorems: `aob_of_rmw`, `ldx_sets`, `stx_fails_unset`, `stx_clears`
(+ helper `find?_never`), `lockGood_holds`, `lockBad_refused`,
`monLock_may_succeed`, `monLock_cleared_by_other`, `monLock_kept_by_self`.
Witnesses on the non-degenerate fixtures: `aob_of_rmw_zeuge`,
`ldx_sets_zeuge`, `stx_fails_unset_zeuge`, `stx_clears_zeuge`.
`#print axioms` per main theorem: all within standard
(`propext`, `Classical.choice`, `Quot.sound`): `aob_of_rmw [propext]`,
`ldx_sets [propext, Classical.choice, Quot.sound]`,
`stx_fails_unset [propext]`, `stx_clears [propext, Quot.sound]`,
`lockGood_holds [propext]`, `lockBad_refused [propext]`.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere.

## Sail sources read (paths relative to `sail-arm/arm-v9.4-a/src`)

- `instrs64.sail:29364` `execute_aarch64_instrs_memory_exclusive_single`
  (status defaults 0b1, `ExclusiveMonitorsStatus()` on pass); pair `:28946`.
- `v8_base.sail:29053` `AArch64_SetExclusiveMonitors`; `:29075`
  `AArch64_ExclusiveMonitorsPass` (unconditional `ClearExclusiveLocal`).
- `v8_base.sail:28087` shareable store clears via `ClearExclusiveByAddress`;
  `stubs.sail:124,128,273,277` mark/clear are no-op stubs (clearing is multicore
  business, defined here); `impdefs.sail:857-858` monitors always pass sequentially,
  `:861` status is `0b0`.
- `v8_base.sail:1627` `MemAtomicOp_*`; `:11917` `CreateAccDescExLDST`; `:11976`
  `CreateAccDescAtomicOp`; `:11993` `CreateAccDescRCW` (A/R to acqsc/relsc);
  `:28334` `MemAtomic` (op table; CAS `cmpfail` skips write); `:28581` `MemAtomicRCW`.
- `instrs64.sail:40042` `execute_aarch64_instrs_memory_rcw_cas`; `:40802` swp.
- `interface.sail:74` `AccessDescriptor_to_Access_kind` (exclusive ->
  `AV_exclusive`, atomicop -> `AV_atomic_rmw`, acqsc/relsc -> `AS_rel_or_acq`).

## Honest CUTS (also in the file)

- Reservation granule modelled as byte-range overlap; the Arm granule is
  IMPLEMENTATION DEFINED and may be coarser. Success-despite-same-granule-store
  executions are NOT covered; every modelled outcome is allowed.
- `aob` excludes LDAPR (`acquirePC`/RCpc): RCpc ordering is agent 10's `lob`, not `aob`.
- Pair forms (LDXP/STXP) and 128-bit CASP have no separate constructors; sizes are
  generic `Nat`, so single-copy atomics of any size are covered but pair shapes
  are not distinguished.
- `Exec` well-formedness is agent 06's; fixtures assume it.

## Commits on `arm/09`

`9d89828e` skeleton; `62bc26e3` access/ALU; `b04172d7` monitor machine;
`8777531a` aob/atomicity; `4af93702` theorems; `1eb348da` spin-lock verdicts;
`1703833e` monitor witness + witnesses + import line. This report: next commit.
