# What the native AArch64 compiler needs from the Lean model: system call, thread start, entry, stack alignment

*2026-10-07, Sonnet agent F. The emitted C backend is deprecated; the path is source -> model -> AArch64
bytes, checked in Lean. So these duties are stated as PROPOSITIONS over decoded final bytes
(`grammatik/Grammatik/Kern/Semantik/SyscallArmPflicht.lean`), not as C templates. Everything below is
built (`lean-bau` green, 732 jobs) and `gabbro_ziel` is on `propext, Classical.choice, Quot.sound`.*

## 0. How the duties are stated

`Bef` is a MINI instruction type (`mov imm`, `mov reg`, `and sp,x,#-16`, `svc`, `bl`, `blr`, `brk`),
`lauf` a straight-line run recording the registers, every call as `(target, sp at the callee's first
instruction, x0)`, the register file at each `svc`, and whether the trap was reached. `nachSvc` is the
agreed kernel ABI (only `x0` changes). The validator's job per emitted block: decode the final bytes to
`Bef`, then discharge the `Pflicht*` proposition (or show the block equal to the canonical block, for
which the proof below exists for every parameter value).

| # | Duty (Lean def) | Canonical block + theorem | Already in `SyscallArm*.lean` before this change? |
|---|---|---|---|
| 1 | `PflichtSvc abi bs`: the one `svc` sees exactly `ladeAufruf abi vorher args` (number in its register, each argument in its register, the rest as the caller had it); `aus` holds the answer mod 2^64; every other register except the number register, and `sp`, unchanged; no call, no trap | `stubBlock abi = [mov nr; svc]`, `stub_erfuellt` for EVERY `abi` with `abi.aus = x0`, `nummer < 2^64`; `stub_zeuge` (write and clone gates; `[svc]` alone REFUSED) | Data and the ABI function (`ladeAufruf`, `nachSvc`, frame law) yes; the statement about a BLOCK no |
| 2 | `PflichtEintritt bs`: from any `sp0 >= 16`: one call at `sp` 16-aligned, `sp <= sp0 < sp + 16`, `x29 = 0`, then `brk`; no `svc` | `eintrittBlock`, `eintritt_erfuellt`, `eintritt_zeuge` (8-mod-16 `sp`; a block without the alignment REFUSED) | Arithmetic only (`start_nolibc_arm`), no block |
| 3 | `PflichtKind stapelReg bs`: child with `sp = stapelReg = v >= 16`: one call with `x0 = v`, aligned `sp` in `(v-16, v]`, `x29 = 0`, `brk` | `kindBlock`, `kind_erfuellt` (any stack register other than `x9`/`x29`), `kind_zeuge` (misaligned block REFUSED) | Arithmetic only (`kind_region_arm`) |
| 4 | `PflichtTrampolin ra rb bs`: both targets (held in callee-saved `ra`, `rb`) called in order at the same aligned `sp`, then `brk` | `trampolinBlock`, `trampolin_erfuellt` | Arithmetic only (`trampolin_kind_arm`) |

Wiring to the generic gate (`SyscallAllg.lean`, new): `ArchAbi A` is the per-architecture record (register
type, number, number register, input map, answer register, clobbers); `SysAbi` (x86_64, number register
`rax`) and `SysAbiArm` are instances; `KernelEintragG A` / `UserSyscallG A` / `syscall_paarung` /
`paarung_gibt_gutO` are generic in `A` (the old names are the `A := SysAbi` abbreviations, every old
witness untouched); `syscall_paarung_arch` adds the generic well-formedness; `syscall_paarung_arch_zeuge`
pairs the toy `write` through `schreibAbiArm`, `syscall_paarung_beide_zeuge` holds both architectures in
one statement; `klonTorArm_good` is the AArch64 clone gate's handoff shape (`stack x1`) under
`CloneAbiG`.

## 1. What is still missing (each is a precise obligation, none is claimed)

1. **A decoder for AArch64 bytes to `Bef`** (or to whatever the Sail-derived model offers). Each `Pflicht*`
   transfers by one lemma per instruction form relating decoded bytes to `Bef`. This is the single largest
   gap; the encodings (`svc #0` = `d4000001`, `brk #0` = `d4200000`, `and sp,x9,#-16`) are not yet tied to it.
2. **Memory.** `argc`/`argv`/`envp` are loaded from `[sp]` by the entry (`ldr`), the child must not touch the
   parent's stack, `bl` writes `x30`. Needed statement, to be made once memory exists:
   `EintrittArgumente: after the entry block x0 = mem[sp0], x1 = sp0 + 8, x2 = sp0 + 8 + 8*(x0+1)`, and
   `KindRahmen: the child block writes no byte outside [v - stackSize, v)`.
3. **Linux clone semantics as a hypothesis, not a theorem.** `PflichtKind` ASSUMES the child starts with
   `x0 = 0` and `sp = v` (named hardware/OS assumption). The `cbnz x0` that selects the child path is not
   in the block; the obligation `Verzweigung: svc answer = 0 -> child block, otherwise parent continuation
   with x0 = answer` needs `cbnz` in `Bef`.
4. **Flags (NZCV)** are carried by `ArmZustand` but no duty claims they survive `svc` (the agreed ABI is
   silent).
5. **`sp` alignment at the `svc` itself** (Linux faults on a misaligned `sp` only if used as a base):
   `PflichtSvc` states `sp` unchanged, so alignment at `svc` follows from alignment at block entry; the
   caller-side premise `sp % 16 = 0 at every call boundary` (AAPCS64) is a duty of the whole-function
   frame validator, not stated here.
6. **Checker side:** `lean_g.rs` and the Rust register tables are still checked against `SyscallArm*.lean`
   by a drift test (`tests/arm_abi.rs`), not generated from `ArchAbi`. `CloneHandoff.lean` stays on the
   x86 record (it imports machine G); `CloneAbiG` carries only the `N446` shape.
7. **Completeness of `Bef`.** Real blocks will use `movz/movk` sequences, `stp/ldp` for the callee-saved
   `x19..x24`, `adrp/add` for `main`'s address; the canonical blocks above are the SHAPE the validator
   accepts, and an equivalence lemma per variant is needed.

## 2. Verdict per requested duty

| Duty | Stated as a proposition on bytes-level blocks? | Proved for the canonical block? | Open |
|---|---|---|---|
| System-call stub | yes (`PflichtSvc`) | yes, every ABI record | decoder; flags |
| Thread start (clone child) | yes (`PflichtKind`, `PflichtTrampolin`) | yes | child-path selection (`cbnz`), memory frame, clone semantics as named assumption |
| Entry (`_start`) | yes (`PflichtEintritt`) | yes | `argc/argv` loads need memory |
| Stack alignment | inside the three above (16-aligned `sp` at every `bl`/`blr`) | yes | whole-function frame validator |
