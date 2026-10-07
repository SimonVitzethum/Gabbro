# REPORT-09 — Multicore: exclusives and atomics

Agent 09 of 15. Clone `/home/simon/Dokumente/gabbro-arm/work/09`, branch `arm/09`.
File: `arm/Arm/Mem/Atomics.lean` (+ one `import` line at the end of `arm/Arm.lean`).

## Status

- [x] Skeleton (`ExclKind`, `AtomicAnn`, `AtomicOp`) green via `./arm-probe`.
- [ ] Access constructors + atomic ALU semantics.
- [ ] Exclusive-monitor state machine.
- [ ] `aob : Exec -> Rel` + atomicity axiom statement.
- [ ] Spin-lock witness (mutual exclusion on two-core fixture, planted violation refused).
- [ ] Import line in `arm/Arm.lean`, full `./arm-bau` green, `.agent/DONE`.

## Build

`./arm-bau`: exit 0, 0 errors (baseline before import line; `Atomics.lean` standalone).
`./arm-probe arm/Arm/Mem/Atomics.lean`: 0 errors.

## Sail sources read (all paths relative to `sail-arm/arm-v9.4-a/src`)

- `instrs64.sail:29364` `execute_aarch64_instrs_memory_exclusive_single` (LDXR/STXR/LDAXR/STLXR;
  status defaults 0b1, `ExclusiveMonitorsStatus()` on pass); pair version `:28946`.
- `v8_base.sail:29053` `AArch64_SetExclusiveMonitors`; `:29075` `AArch64_ExclusiveMonitorsPass`
  (unconditional `ClearExclusiveLocal`).
- `v8_base.sail:28087` plain store clears via `ClearExclusiveByAddress` (in
  `AArch64_MemSingle_set__1`); `stubs.sail:124,128,273,277` mark/clear are no-op stubs;
  `impdefs.sail:857-858` monitors always pass, `:861` status is 0b0.
- `v8_base.sail:1627` `MemAtomicOp_*`; `:11917` `CreateAccDescExLDST`; `:11976`
  `CreateAccDescAtomicOp`; `:11993` `CreateAccDescRCW` (A/R bits to acqsc/relsc);
  `:28334` `MemAtomic` (op table; CAS `cmpfail` skips the write); `:28581` `MemAtomicRCW`.
- `instrs64.sail:40042` `execute_aarch64_instrs_memory_rcw_cas`; `:40802` `..._rcws_swp`.
- `interface.sail:74` `AccessDescriptor_to_Access_kind` (exclusive -> `AV_exclusive`,
  atomicop -> `AV_atomic_rmw`; acqsc/relsc -> `AS_rel_or_acq`).

## CUTS (so far)

Skeleton only; monitor machine, `aob`, witnesses open. IMPLEMENTATION DEFINED
reservation-granule coarseness will be documented, not silently fixed.
