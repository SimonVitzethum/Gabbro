# Opus agent L — system calls as named variables, bound per target (2026-09-26)

*Task: OFFEN O31 (Simon's request) -- a language form that declares system calls as NAMED
VARIABLES and ONE statement that binds them for a target, so the same gate builds for Linux
and for bare metal; rewrite the hosted-only kernel-gate units of OFFEN O33 onto it; plus the
OFFEN O32 residue: `N561` (entry registers against the dispatch), entry stacks and
error-code vectors if feasible, and the `Spec.lean` assumptions (M8)-(M10).*

## 1. Headline

| measure | result |
|---|---|
| new form | `syscall V;` + `… via V …` at the gate + `target T abi A arch X { V = … }` + `target T;` / `--target T` (SYNTAX.md §12.3, EBNF: `syscalldecl`, `sysbind`, `syscontract`, `syspair`, `targetdecl`, `targetbind`, `errmap` with `= n`) |
| new word | `target` (`ctx`): 244 → 245 (`zaehle-wortschatz.py` ratchet, reason at the entry) |
| new codes | `N561` (entry binding), `N562`-`N567` (target binding), `N568` (link: one kernel) |
| gifts | 1351-1363 (13); examples 163, 164, 165 |
| O33 class (a) kernel gates | **11 → 1**: ten units bind per target and are emitted for `metal` by stage 12 (listed as BOUND FOR THE METAL TARGET with the numbers the image's kernel serves); `beispiele/36` stays (its own `asm` executes `syscall`) |
| QEMU (stage 11) | 18 booted, 8 gifts bite (Opus J: 15 / 5) — new: `metall164`, `metall163`, `metall165`; gifts `metall164-gift`, `metall163-ohne-kern`, `metall165-gift` |
| stage 12 | see §7 (final runs) |
| O32 residue | (7) closed (`N561`), (9) closed (error-code twin stub, measured on #GP), (12) closed (Spec comment hunk), (8) named |

## 2. The design, and why

```gabbro
syscall sys_write;                                   -- the variable
syscall write(fd : u64, buf : u64, len : u64) -> u64 or IoError
    via sys_write requires len <= 1024 ensures result <= len effects { pure } costs <= 8 ops;
target linux_x86_64 abi linux arch x86_64 {
    sys_write = number 1 regs in { rdi = fd, rsi = buf, rdx = len } regs out { rax }
        clobbers { rcx, r11 } errors { EBADF => BadFd } assume linux_write_contract falsifier sonde_write;
}
target metal abi metal arch x86_64 {
    sys_write = number 1 regs in { rdi = fd, rsi = buf, rdx = len } regs out { rax }
        clobbers { } errors { EBADF = 9 => BadFd } assume metal_kernel_contract falsifier sonde_metall_systemruf;
}
target linux_x86_64;
```

| decision | reason |
|---|---|
| the binding carries exactly the target-dependent half (number, registers, `stack`, clobbers, errors, assumption); the gate keeps parameters, answer, channel, contract, effects, costs | the program's contract is the same for every kernel; what a kernel does is its assumption |
| the parser FILLS the gate from the active binding (`gabbro-syntax/src/ziel.rs`) before any pass | every pass, the emitter, the exporter and the certificate read an ordinary gate: no pass had to learn the form, and nothing downstream can see a gate without a kernel. A gate no target binds keeps placeholders, is refused (`N562`/`N563`/`N565`), skipped by the shape rules and refused by the emitter by name |
| active target: `--target`/`GABBRO_TARGET`, else the one selection, else the one block | "ONE statement elsewhere" -- one selection, or nothing to choose |
| EVERY target binds every used variable (`N563`), not only the active one | switching the target must never meet an unbound gate; the inactive bindings are also held to the gate's shape (`N063`-`N068`, `A006`, `N004`/`N005`) |
| two targets never share one assumption for a variable (`N566`) | "a different target means different named assumptions, never silently the same" |
| `progress V` names the variable and resolves to the active binding's assumption; `progress A` over a target-bound assumption falls (`N566`) | 96 and 150 rested their loop's liveness on the Linux contract by name; under `metal` that would have stayed Linux |
| a literal gate beside targets falls (`N567`); a unit without targets keeps the literal form | the corpus's 40+ gate gifts pin the literal form's rules; mixing the two in one unit would leave one gate on a fixed kernel |
| errno numbers explicit per binding (`EBADF = 9 => BadFd`) | the error convention is the kernel's. Finding: `S14` numbered its reason cases 1, 2, 3 and so decoded Linux `EBADF` (9) as nothing and `EPERM` (1) as `BadFd` -- fixed by the explicit numbers |
| `abi metal` = `int $0x80` into the image's kernel entry, nothing but rax + memory destroyed, `-errno` in -4095..-1 | the metal runtime's own entry stub (Opus J) saves every register; the runtime installs a vector-0x80 slot whose C half hands the frame to the IMAGE's `metall_systemruf` (weak -- no kernel means a loud end, status 9, never an invented errno the stub would hand to the compiler as unreachable); a program's own `entry … vector 0x80` takes the slot (the program IS the kernel, `beispiele/164`) |
| linking: `N568` | `GabbroZielVerbund` needs the same `Q`; two targets are two kernels |
| a direct call into a Gabbro kernel function (`kernel <path>`, `N068`) | NOT built: the entry at 0x80 already realises "the program is the kernel" without a second call convention |

## 3. What was rewritten

`beispiele/74`, `90`, `96`, `149`, `150`, `155`, `156`, `160`, `1114`, `messung/schreibprobe/S14`:
`via sys_<gate>` + `target linux_x86_64` (the literal half, unchanged) + `target metal` (same
number and registers, empty clobbers, explicit Linux errno numbers where the errno has one,
`metal_kernel_contract`) + `target linux_x86_64;`. Hosted emitted C against the pre-rewrite
source: identical but for one manifest line (the declared `metal_kernel_contract`) and, in
96/150, the `progress` comment (`sys_write`/`sys_gate_read`); `S14` also differs in the
decoded errno numbers (the finding above). Under `--target metal` all ten emit `int $0x80`
and compile hosted and freestanding. `beispiele/36` is not rewritable: the `syscall` is the
program's own `asm`.

Honest limits of the rewrite: 155/156/160/1114 call number 1000 (a thread start with a handed
stack, not an OS number); no metal kernel in the tree serves it, so under `--target metal`
they link and would end the machine at the call (status 9) -- stage 12 lists the numbers each
unit needs from the image's kernel.

## 4. O32 residue

| item | what |
|---|---|
| (7) `N561` | an entry whose dispatch is a function of the unit: `regs in` = its parameters (count, in order), at most one `regs out` and only for an answering dispatch (`-> never` answers nothing; an answer with no out register is dropped -- the stub guesses nothing), no `or R`. `gabbro build` (`bau.rs`) and stage 12 read the same rule. `beispiele/11` and `probe-emission144-typeof`: their `extern fn behandler()` now takes one `u64` per bound register and answers `u64` (the honest fix: the entry bound registers to a nullary dispatch). Gifts 132, 133, 705, 899 and `race-proben/eintritt-schreibt-ungeschuetzt` fell with `N561` beside their own code; their entries were aligned, each now falls for its own reason alone (pinned codes unchanged) |
| (9) error-code vectors | twin stub `metall_eintritt_gemeinsam_fc` (drops the code before `iretq`), `METALL_EINTRITT_FC` (C half sees `struct metall_rahmen_fc` with the code), `metall_idt_setze_fc` (ONLY those vectors; the plain installer keeps refusing them). `gabbro build` no longer refuses 8/10-14/17/21/29/30 and binds them with the twin (`treiber.rs`, test extended); stage 12 likewise. QEMU: `beispiele/165` (`entry gp vector 13`) -- three non-canonical loads raise #GP(0), the entry runs three times, error code 0, the run goes on; gift: the plain stub on vector 13 never reports |
| (8) entry stacks | NOT built: the runtime has no TSS/IST; the entry runs on the interrupted stack. Named in OFFEN O32 and in (M8) |
| (12) `Spec.lean` | comment-only, delimited hunk "bare-metal entries and targets": (M8) entry stub, (M9) masked lock IF discipline, (M10) arena budget, and the O31 targets (premise (c) names the active binding's assumption; `N566`, `N568`) |

## 5. The falsifier `sonde_metall_systemruf`

The metal bindings rest on ONE new assumption, `metal_kernel_contract` (the image's kernel
entry keeps the Linux x86_64 convention and each gate's contract). Its register half is the
runtime's: to falsify THAT text and not a copy, the common entry stub moved from `start.S`
into `laufzeit/metall/eintritt_asm.h` (unchanged instructions, `leaq sym(%rip)` for the new
kernel-service half so the same text links PIE), assembled into the image by `kern.c` and into
the userland probe. The probe enters it through a hand-built interrupt frame (an `iretq` ring 3
→ ring 3 is legal) 1000 times with random registers: answer in rax (value and `-EBADF` legs),
all 15 other GPRs, rsp and xmm0 preserved; `--kaputt` (the service writes rbx) falls.
Measured: exit 0 / `--kaputt` exit 1. Register row 55 in `SONDENDECKUNG.md`, `MARK_QUOTE`
(21, 54) → (22, 55), the guardian's two count-calibrated teeth recomputed (fifteen newest
probes, stress size 122); its speech test shows the same four NO rows as on master.

## 6. Decisions and findings, short

- **Stack overflow found by the depth guard** (`die_beiden_wachen…`, 2 MB test thread): the
  grown `SyscallDecl` temporary in `item()`'s frame. Fixed the `arena_item` way:
  `syscall_item` builds syscall/variable/target outside the frame.
- **The manifest of a build names the active target's assumptions only**
  (`ziel::fremde_zielannahmen`): an assumption only another target binds is that kernel's,
  and the certificate of the Linux build does not list `metal_kernel_contract` (the emission
  stage's booked certificate of `beispiele/74` -- 1 assumption -- caught the first version,
  which listed both). An `assume` no binding names stays listed.
- **An emitter finding, fixed:** a `void` pure leaf with its `effects` ELIDED got
  `__attribute__((const))` (the derived-effects arm lacked the written arm's `void` guard),
  which GCC refuses under `-Werror=attributes`; `fmt_views` found it on `beispiele/165`
  (`ELIDE moves emission`).
- **Variables and targets are unit-global** (no module scoping) -- named.
- **Caprock**: needs its own trap template; `C182` refuses `abi caprock` by name -- named.
- **`N561` relaxation vs Opus J's stub**: J's build demanded `regs out` count == answer
  count; an answer with no out register is now dropped (build, stage 12, checker agree),
  because two snippet tests (`lockfree_entries_stay_silent`, `arena_zaehler_entry_n522`)
  write exactly that shape and dropping a value guesses nothing.

## 7. Final runs

- `free -g` before the runs: 31 GB total, 12-13 GB available (other agents on the machine).
- `./lean-bau`: **exit 0, 0 error lines**, 355 jobs (the new certificate
  `Zertifikat/G165_gp_eintritt.lean` and the comment-only `Spec.lean` hunk included).
- `./cargo-pruef`: **exit 0, 1408 passed, 0 failed, 1 ignored** (Opus J: 1407; new:
  `zwei_ziele_verbinden_sich_nicht_n568`; the `treiber.rs` metal-driver test extended by
  the #GP entry).
- `./emission-pruef`: **exit 1 at stage 9, for the mark only**: `142 statt 139 emittierende
  Dateien in beispiele/` -- the three new examples 163, 164, 165 (315 of 315 emitting units
  compile, clang agrees on all). **MARKE delta: `MARKE_EMIT` (beispiele/) 139 → 142**, not
  touched here (the merger re-measures it). Everything before stage 9 (the differential
  tests, including 74/90/96 with their booked certificates) passed.
- Stages 11 and 12 run alone with the same binary:
  - **stage 11**: `18 booted on qemu -smp 4, every expectation held, 8 gifts bite` (Opus J:
    15 / 5);
  - **stage 12**: `315 of 315 link without an OS; 12 bound for the metal target; 6
    hosted-only listed by name` (Opus J: 312 of 312; 16 hosted-only). Hosted-only now:
    (a) `beispiele/36` alone; (b) the five C-library bindings, unchanged.
- Probe: `sonde_metall_systemruf` exit 0, `--kaputt` exit 1.
- Guardians: `pruefe-wortschatz.py` 242/242 both readings; `pruefe-syntax.sh` EBNF 187
  rules, 0 open (182 before); `pruefe-saetze.py` 470 codes, 55 without a sentence (the
  mark, unmoved), 0 invented; `pruefe-kennungen.py`, `pruefe-grammatiktafel.py` (0 of 242
  uncovered), `pruefe-konstrukte.py` pass; `pruefe-sondendeckung.py` shows the same teeth
  as master (its four NO rows predate this branch); `pruefe-todo.py` 16 findings as on
  master.
