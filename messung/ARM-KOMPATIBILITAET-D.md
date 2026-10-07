# AArch64 compatibility, Lean side: where x86 is baked into the syscall ABI and the templates (agent D)

*2026-10-07. Read-only inventory plus the first additive Lean file. Nothing under
`grammatik/Grammatik/X86/` or `crates/gabbro-check/src/x86/` was touched, and
`Zielsatz/Kern/Spec.lean` was not edited.*

Path correction: `CloneHandoff.lean` is at `grammatik/Grammatik/CBackend/Semantik/CloneHandoff.lean`
(not under `Kern/Semantik/`). Line numbers below are in the files as they stand.

## 1. What mentions x86 registers, `rsp`, SysV entry alignment, or syscall numbers

### `Kern/Semantik/Syscall.lean`

| Lines | Definition / theorem | x86 content | Generalisable without changing an x86 statement? |
|---|---|---|---|
| 25-30 | `SysReg` | the 16 x86-64 GPRs; comment "aarch64 stays sealed" (stale) | Yes, by a parameter: `SysAbiG (R : Type)`; `SysReg` stays the x86 instance. Not done here; the new file mirrors instead. |
| 36-45 | `SysAbi` (`nummer`, `ein`, `aus`, `clobber`) | field types are `SysReg`; **no number-register field** (x86 fixes the number in `rax`, the answer register) | Yes, `SysAbi := SysAbiG SysReg` as an `abbrev` keeps every downstream statement. AArch64 needs one extra field (`nummerReg`), so the generic record carries it with default `rax`-for-x86 via an x86 smart constructor. |
| 48-50 | `sysAlleReg` | lists the 16 GPRs | Per instance. |
| 55-59 | `schreibAbi` | `write` = number **1**, `rdi, rsi, rdx`, `rax`, clobbers `rcx, r11` | No (x86 data); AArch64 twin is `Arm.schreibAbiArm`. |
| 63-88 | `SysAbi.gut`, `sysAbiGutB`, `sysAbiGutB_sound`, `schreibAbi_gut` | structure is arch-neutral (Nodup, `aus ∉ clobber`); only the type is x86 | Yes, they only need `DecidableEq R`. |
| 90-427 | `SysAntwort`, `FehlerTabelle`, `dekodiere` and all its laws, `IoFehler`, `schreibFehler` | none. The errno window 1..4095 and the signed-`x0` convention are identical on AArch64 Linux (EBADF 9, EINTR 4, EAGAIN 11 are asm-generic) | Already architecture-neutral. Nothing to do. |

### `Kern/Semantik/SyscallPaarung.lean`

Uses `SysAbi` and `schreibAbi` (lines 26, 39, 95, 242, 256, 285-287, 438, 506) and the call number 1 (`swKbeh`:
`n = 1 ∧ ab = schreibAbi`). Generalisable by the same abbrev; the number 1 and `schreibAbi` are x86 witness data
and would be parameters of an AArch64 witness program.

### `CBackend/Semantik/CloneHandoff.lean`

| Lines | Item | x86 content |
|---|---|---|
| 53-61 | `CloneAbi` | `stack : SysReg` (x86 type only) |
| 66-83 | `CloneAbi.good`, `cloneAbiGoodB`, `cloneAbiGoodB_sound`, `cloneStack_*` | arch-neutral shape, x86 only through `SysReg` |
| 101-135 | `cloneWitnessAbi`, `cloneWitness` (`rdi`, `rsi`, `rax`, `rcx`, `r11`, number 1000), `cloneBadWitness` | x86 witness data. Number 1000 is deliberately no OS number. |
| 150-452+ | `KlonMaschine`, `KlonSchritt`, `klonErreichbar_G`, ..., `klon_ziel`, `kw_*`, `k124_klon_ziel` | none; machine-G level, architecture-neutral |

### `Bausteine/Schablonen/SchablonenFaden.lean`

| Lines | Item | x86 content |
|---|---|---|
| 49-62 | `Regs {rax, rsp, kind, ende}`, `nachSyscall` | named x86 registers; `rax = 0` in the child is the Linux **x86 and AArch64** clone convention (child sees 0), `rsp` is x86 |
| 64-75 | `kindPfad` | `andq $-16,%rsp`, `call` pushes 8: entry `rsp = a - 8` |
| 82-92 | `trampolin_kind` | conclusion `(z.2 + 8) % 16 = 0 ∧ z.2 < spitze ∧ spitze - 24 ≤ z.2` is the SysV entry condition and the x86 `call` push |
| 99-101 | `elternAntwort`, `trampolin_eltern` | arch-neutral |
| 105-195 | `faden_warte_korrekt`, `faden_warte_ohne_eltern` | futex wait protocol, arch-neutral (no register, no stack alignment) |
| 203-243 | `KindRegs {rsp, stapelReg}`, `kindRuf`, `kind_region`, `kind_region_zeuge` | `rspEintritt := rsp - rsp % 16 - 8`, conclusion `(rspEintritt + 8) % 16 = 0 ∧ rspEintritt < v` |

### `Bausteine/Schablonen/SchablonenOhneLibc.lean`

| Lines | Item | x86 content |
|---|---|---|
| 133-134 | `ausrichten` | `and $-16, %rsp` (the operation itself is arch-neutral: round down to 16) |
| 138-148 | `StartLauf`, `startLauf` | `rspEintritt := ausrichten rsp - 8` (the `call` push) |
| 157-175 | `start_nolibc`, `_ud2_wenn_main_zurueckkehrt`, `_zeuge` | `(rspEintritt + 8) % 16 = 0` (SysV x86-64 entry), `rueckAdresse < rsp` (return address on the stack) |
| 188-250 | `startLaufH`, `start_nolibc_haken`, `_ohne_ende` | same, for the widened stub |
| 1-60 comments, 362+ | `syscall` instruction text, `syscall_stumpf` | emitter text, x86 |
| the rest | `tor.nie`, `tor.fehlbar`, `tor.region` cores, `Zeuge174` | operate on `Endblock`/`D.Ax`; architecture-neutral (a `syscall` gate is an `Ax`, the instruction is in the C stub, not in the model) |

### Numbers

Literal syscall numbers appear only as witness data (`schreibAbi` = 1, `cloneWitness` = 1000, and `Arm` adds the
AArch64 table). The Lean model never dispatches on a number: `D.Ax` carries `SysAbi` as data and the kernel is an
oracle with a contract. That is why replacing the register type is enough.

## 2. What can be generalised without changing any x86 statement

1. **`SysReg`/`SysAbi` over a register-type parameter**, `SysAbi := SysAbiG SysReg` as an `abbrev`. Every x86 statement
   in `Syscall.lean`, `SyscallPaarung.lean`, `CloneHandoff.lean` unfolds to the same term. The AArch64 record needs one
   more field (the number register); an x86 instance defaults it to `rax`. This **edits** the three files, so the
   agent did not do it (the task says new definitions in a new file); `Arm.SysAbiArm` is the mirror and can later be
   replaced by `SysAbiG ArmReg`.
2. **`CloneAbi` over the register parameter**, same device; `CloneAbi.good` needs only `DecidableEq`.
3. **The stack-alignment premises** do not generalise by a register swap, because the premise itself differs
   (`rsp + 8` vs `sp`): they need a per-architecture entry-offset constant (x86: the `call` push of 8, AArch64: 0,
   because `bl` writes `x30`). A single theorem parametrised by that offset `c` would have conclusion
   `(spEintritt + c) % 16 = 0`, and the x86 statement is its instance at `c = 8`. Possible without changing the x86
   statement's meaning if the x86 theorems are re-derived as instances; the agent mirrored instead (item below).
4. Unchanged and already neutral: the errno decoder, `faden_warte_korrekt`, machine-G clone model, `tor.nie`,
   `tor.fehlbar`, `tor.region`, `trampolin_eltern`.

## 3. What was added (new file only)

`grammatik/Grammatik/Kern/Semantik/SyscallArm.lean`, namespace `Gabbro.Grammatik.Arm`:

* `ArmReg` (`x0..x30`, `sp`), `Flags` (NZCV), `ArmZustand`;
* `SysAbiArm` (+ `gut`, `Decidable`), `linuxAbi nr k`, `argRegs`, the 14 Linux numbers `nr*` (pairwise distinct,
  `decide`), `argRegs_verschieden`, `argRegs_nicht_x8`, `nummerReg_nicht_ergebnis`, `argRegs_nicht_calleeSaved`,
  `linuxAbi_gut` (every number, every `k ≤ 6`);
* `schreibAbiArm` (+ `schreibAbiArm_wert`, `_gut`), `ladeAufruf`, `nachSvc` (only `x0` changes), `nachSvc_rahmen`,
  `nachSvc_ergebnis`, the witnesses `schreibAufruf_zeuge` (a concrete `write(1, 0x4000, 5)` register assignment),
  `svc_zeuge`, `svc_errno_zeuge`;
* AArch64 counterparts of the alignment premises: `start_nolibc_arm`, `kind_region_arm`, `trampolin_kind_arm`, each
  with a witness (`..._zeuge`) on an 8-aligned-only stack pointer.

Differences from x86, stated in the theorems: entry `sp % 16 = 0` (not `(rsp+8) % 16`), entry `sp ≤` handed top
(not strictly below, `bl` pushes nothing), and no return-address-below-`rsp` clause (it lives in `x30`).

## 4. Stale comment at `Syscall.lean:25`

"`aarch64` stays sealed, so there is no second register file" is a pure comment edit. Edited in a separate commit,
see the git log; the file was rebuilt afterwards. The doc comment on `SysReg` now says it is the x86-64 file and
points at `SyscallArm.lean`.

## 5. Honesty

This models the ABI as data and proves that the model is internally consistent; it proves nothing about AArch64
hardware or the Linux kernel. `nachSvc` is the agreed ABI written as a function. See the CUTS block of the Lean file.
