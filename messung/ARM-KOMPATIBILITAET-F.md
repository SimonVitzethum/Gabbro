# Findings F1-F4 of agent C: what agent F did (2026-10-07)

*Scope changed mid-run (coordinator, Simon): the emitted C backend is DEPRECATED, the native AArch64
compiler with translation validation is the path. Done: F2 (minimal), the Lean wiring (F4), and
`messung/ARM-NATIV-ABI.md`. Cancelled by that decision: F1 as C-stub templates, F3 as `nolibc` `_start` in
`bau.rs`, the audit of C helpers. Their native counterparts are `SyscallArmPflicht.lean` (duties 1-4).*

## F2 -- page-return helper wrap (legacy C, fixed minimally)

* Cause: `bis = (a + bytes) / seite * seite - a` in `uint64_t` BEFORE the test `von < bis`; for a range inside
  one page `(a+bytes)/seite*seite < a`, the subtraction wraps, the test passes, the helper zeroes far past the
  buffer. Reproduced before the fix: example 175 with a one-page `reset` exits 139 (x86 too).
* Fix (`emit.rs`, `REGION_LEEREN`): round the ABSOLUTE addresses, `lo`/`hi`, test `lo < hi`, form `von`/`bis`
  only inside the branch. Lean (`SchablonenArena.lean` §2): `leeren_teilung` now takes the absolute test as
  its hypothesis; new `leeren_in_einer_seite`, `leeren_alt_bricht` (the old arithmetic mod 2^64 exceeds
  `bytes`), `leeren_ohne_umlauf` (no wrap under the helper's guard). Standard axioms only. NOT done: the
  full `BitVec 64` restatement of the template and any audit of other C helpers (cancelled with the C backend).
* Probes: example 175 gained a one-page reset (still returns 7; `RING[200..300)`); stage 4 of
  `instrumente/pruefe-seiten-zurueck.sh` runs the corrected helper (exit 0, `7`) and a POISON twin made by
  `instrumente/vergifte-leeren.py` (first-version arithmetic put back): **exit 139, caught**; unit test
  `crates/gabbro-check/tests/leeren_seite.rs`. Hosted AArch64 run (`messung/arm-c/run_hosted.sh`, qemu): 175
  `-O0`/`-O2` = 7.

## F4 -- `SysAbiArm` into the generic gate (Lean)

`SyscallPaarung.lean`: `KernelEintragG A`, `UserSyscallG A`, `PaarGut`, `syscall_paarung`,
`paarung_gibt_gutO` generic in the ABI type (the pairing only compares it); `KernelEintrag`/`UserSyscall` are
`abbrev`s at `SysAbi`, so every old statement and witness is unchanged (they still build).
`SyscallAllg.lean` (new): `ArchAbi` class with instances for `SysAbi` and `SysAbiArm`, `ArchAbi.gut`
(`arch_gut_arm`: equals `SysAbiArm.gut`; `arch_gut_x86`: `SysAbi.gut` plus "`rax` is no input"),
`schreib_beide_gut`, `arm_tore_arch_gut` (all nine gates), `CloneAbiG` and `klonTorArm_good` (+ refused
`klonTorArm_schlecht`), `syscall_paarung_arch`, and the witnesses `syscall_paarung_arch_zeuge` /
`syscall_paarung_beide_zeuge` (the toy `write` through `schreibAbiArm`, number 64, non-degenerate).
Machine G never held an ABI (`Deklaration.Ax` has none), so no G definition moved. `CloneHandoff.lean` and
`lean_g.rs` untouched (see ARM-NATIV-ABI.md section 1, item 6).

## F1, F3 -- native counterparts

`SyscallArmPflicht.lean`: `PflichtSvc` (stub), `PflichtEintritt` (`_start`), `PflichtKind`,
`PflichtTrampolin`, each with a canonical block proved for every parameter value and a REFUSED negative
witness. Statement of what is missing: `ARM-NATIV-ABI.md`.

## Measured

* `lean-bau`: 0 errors, 732 jobs. `#print axioms gabbro_ziel` (NachpruefungZiel): `propext, Classical.choice,
  Quot.sound`. New theorems: `propext`/`Quot.sound` only; no `sorry`.
* `instrumente/lean-layout.py --check`: ok (900 Lean files). `instrumente/pruefe-kein-sorry.py`: 738 files,
  0 violations.
* `cargo test -p gabbro-check --no-fail-fast`: **1422 passed, 0 failed** (C: 1420 + 1 failed before regen;
  +1 new test here). Workspace-wide suite not run (`programmlogik/.lake` absent). `pruefe-emission.sh` not run
  (memory; example 175 changed its source, its driver expects 7 and still gets 7 on x86 and AArch64).
* Not touched: new diagnostic codes, gifts, example numbers.
