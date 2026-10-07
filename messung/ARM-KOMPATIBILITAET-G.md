# x86-only assumptions on the native path of the checker (Sonnet G, 2026-10-07)

Scope: `crates/gabbro-check/src`, `crates/gabbro-cli/src`, `crates/gabbro-syntax/src`, excluding the C text of
`emit.rs` and `x86/`. Method: grep for x86 names (`x86`, registers, `lock cmpxchg`, `idt`, `pause`, `4096`,
`red-zone`, TSO) and reading each hit. Prior reports (`ARM-KOMPATIBILITAET-A..F`) covered the C emitter and the
register tables; this one is the remainder.

## Fixed (plain data, with tests)

| Where | What it said | Now |
|---|---|---|
| `syscall.rs` register tables | two hand-kept `const` arrays (x86 / AArch64) held against Lean by a drift test | generated from the Lean records: `abi_tabelle.rs`; guardian `instrumente/erzeuge-abi-tabelle.py --pruefe`; tests `abi_tabelle_ist_frisch`, `die_konventionen_der_erzeugten_tabelle_sind_die_des_pruefers` |
| `tearing.rs` `Shape::RelAcq` price | "x86_64 total store order ... no fence" as the whole price of a release store / acquire load | names both: on aarch64 (weakly ordered) the `stlr`/`ldar` pair IS the ordering and nothing weaker may be substituted; test `die_ordnungspreise_nennen_beide_architekturen` |
| `tearing.rs` `Shape::Cas` price | "carried by a lock-prefixed instruction" | adds `casal` / `ldaxr`-`stlxr` loop for aarch64 (same test) |

## Remain, with the reason they were not changed

| Where | Assumption | Why left | Needed |
|---|---|---|---|
| `gabbro-cli/src/bau.rs:1675` | bare-metal entries are `x86_64` only (`IDT`, `-mno-red-zone`, `METALL_IDT`) | a refusal (stays; weakening is forbidden) and the runtime is x86 | an AArch64 exception-vector profile; then the refusal is lifted per profile |
| `bau.rs:279` | `provision <bytes>` must be a multiple of 4096 | weaker than the AArch64 Linux granules (16 KiB / 64 KiB; `linux-aarch64.gab`: `gabbro_os_seitengroesse`); a multiple of 4096 that is not a granule multiple is accepted | the granule from the target binding, not a literal |
| `manifest.rs:122` `gleitkomma_x86_rechnet_mit_sse2` | assumption named and worded for x86 (x87 double rounding) | holds on AArch64 by construction (no extended-precision unit); renaming changes a guardian-booked register entry | an arch-tagged entry (`arch: Some("aarch64")`, FPCR flush-to-zero / default NaN probe) |
| `manifest.rs:669` `sonde_rdtscp`, `namen.rs` `Has(RDTSCP, ...)` | CPU-feature probe vocabulary is x86 (`CPUID`) | feature names are user data; AArch64 needs `ID_AA64ISAR*` features | a feature-name table per `arch` (data) |
| `kostenledger.rs:630,688`, `bau.rs:3182`, `m1.rs`, `verbund.rs` tests | `arch: "x86_64"` literals | test fixtures only | none |
| `parse.rs:5987` | placeholder `arch x86_64` for a `via` gate | overwritten by the active target (`ziel.rs:136`) before any pass reads it | none |
| `treiber.rs` (`pause`, `aligned(4096)`, `-mno-red-zone`, `hlt`) | generated C drivers | C backend, deprecated | the native backend |
| `saetze.rs:4391` / `schablonen.rs:219` | `tor.kind` alignment stated as `rsp + 8` | proved templates of the C backend; the AArch64 statement is `SyscallArmPflicht.lean` (`PflichtKind`) | transfer from decoded bytes (item 3 of `ARM-NATIV-ABI.md`) |
| `cnamen.rs:989` | libc `pause` signature table | host C names, not architecture | none |
| `namen.rs:2753, 3739` | message text mentions x87 / x86 bus splitting as examples | wording only | none |

Not found: any pass that computes with `rax`/`rsp`/pointer size 8 except as `u64`, any use of
`cfg(target_arch)` in the checker, or any check that reads x86 memory ordering outside the `tearing.rs` price text.
