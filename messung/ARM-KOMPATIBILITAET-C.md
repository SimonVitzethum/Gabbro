# AArch64 readiness of the checker, the emitter, the binding and the Lean ABI model (agent C)

*2026-10-07, Sonnet agent C. Branch of worktree `agent-a344fe50ff7d274f3`, commits
`cd7dd1af` (checker), `17ddbe56` (emitter), the binding commit, `bd52a3e1` (Lean + test), on top of
master `75396dfe` (merged in). Host x86_64; `aarch64-linux-gnu-gcc` 16.1, `qemu-aarch64` user mode.
qemu-user is not silicon and not a memory-model test. Scratch work in
`.claude/muse-arbeit/kratz-c/` (untracked); the reproducible drivers are in `messung/arm-c/`.*

## Summary (measured)

| Question | Before | After |
|---|---|---|
| `gabbro check` / `emit` of the 157 `beispiele/*.gab` | 157 / 157 | 157 / 157 (unchanged; `exit 0` for all) |
| compile for AArch64, `-std=c11 -Wall -Wextra -Werror` (agent A: 136) | 136 of 157 | **152 of 157** |
| run under qemu-aarch64, harness units (agent A: 46 of 52) | 46 of 52 | **51 of 52** (arithmetic, see section 4) |
| x86_64 behaviour | | `check` + `emit` of 1019 files (`beispiele/` + `gift/`) byte-identical, bar the intended diffs below |

The 152: the 17 units that failed on the system-call stub compile once their Linux gates say
`arch aarch64` (16 of 17; `164` is a bare-metal x86 kernel by design). Remaining 5 failures:
`164-eigener-kern` (x86 kernel entry), `36-asm`, `65-port-space`, `67-befehlsebene` (user `asm`
with x86 constraints), `60-annahme-mit-maschine` (x86 mnemonic `mfence`): all declare x86 in their
own text and are not touched by design.

The rewrite of the 17 sources is mechanical (`messung/arm-c/to_aarch64.py`); the corpus itself
was not changed.

## 1. Checker (`crates/gabbro-check/src/syscall.rs`, `clone.rs`, `namen.rs`, `saetze.rs`) - commit cd7dd1af

* `syscall::arch_bekannt` (`syscall.rs:56`) opens `x86_64` and `aarch64`; `A006` (`syscall.rs:437`)
  still refuses every other machine, with a new wording ("only `x86_64` and `aarch64`").
* `syscall::register_fuer` (`syscall.rs:63`): `REGISTER_AARCH64` = `x0`-`x30`; `N066` holds a name
  against the table of the DECLARED machine. An unknown arch reads the x86 table (so `A006`-refused
  gates keep their old `N066` answers). `N446` (stack register, `clone.rs:227`) does the same.
* `A005` (`namen.rs:6121`) now also covers aarch64 syscalls.
* Sentence `syscall.erklaerung` updated (`saetze.rs`); `pruefe-saetze.py`: 205 sentences, 0 invented.
* No x86 refusal weakened: nothing was removed, every x86 table and message is the old text.
* Measured: `check` + `emit` of every `beispiele/*.gab` and `beispiele/gift/*.gab` before/after:
  identical except (a) gift 838 (`-- erwartet: A006`, retargeted from `arch aarch64` to `arch riscv64`
  because aarch64 is now open; its A006 text changed as above), (b) the new gifts 1400 (`N066`),
  1401 (`A005`), 1402 (`C180` on `x8`), 1403 (`C181` on `x1`), (c) gift 938, whose `N280` lists two
  type names in HashMap order: **it differs between runs of the unchanged base binary too**
  (4 runs: `Antwort, Nachricht` three times, `Nachricht, Antwort` once) - a pre-existing
  nondeterminism, unrelated.
* Tests: `cargo test -p gabbro-check --test korpus --test beispiele --test gestalt`: 25 + 6 + 11
  passed. The full-crate run is in section 6.

## 2. Emitter (`crates/gabbro-check/src/emit.rs`) - commit 17ddbe56

* `syscall_befehl` (`emit.rs:9294`): `("linux","aarch64") => "svc #0"`, clobbers `memory` only.
* `syscall_regs` (number reg / answer reg: `x8`/`x0`, x86 `rax`/`rax`) and `syscall_pins` (the pins
  and asm operands shared by the stub, the inline `child` trap and the trampoline). `x0` is both
  the first argument and the answer: `"+r"` when a parameter is bound to it, `"=r"` when none.
  `C180` holds the number register (`x8`), `C181` the answer register (`x0`).
* Child path of the inline trap (`emit.rs:9203`): `svc #0; cbnz x0,1f; mov x0,<stack>; mov x9,sp;
  and sp,x9,#-16; mov x29,xzr; bl gabbro_kind_N; brk #0`. Trampoline (`emit.rs:10107`): same with
  `blr` of two callee-saved registers from `x19..x24`. (`and sp, sp, #imm` is not encodable - the
  assembler said `expected an integer or zero register at operand 2` - hence `x9`.)
* x86 text unchanged: checked by the corpus comparison above (17 files contain the x86 stub).

## 3. Binding (`bibliothek/linux/linux-aarch64.gab`; `messung/arm-c/mk_linux_aarch64.py` records the derivation)

* New file, `linux.gab` untouched. Numbers: mmap 222, mprotect 226, write 64, exit_group 94,
  madvise 233, sched_yield 124, clone 220, exit 93, futex 98 (the agreed list; the other agreed
  numbers - read 63, openat 56, close 57, munmap 215, clock_gettime 113 - are in the file header and
  the Lean model; no gate uses them).
* **Differs from a mechanical x86 translation in three places** (found, not assumed):
  1. `clone`: AArch64's raw `clone(flags, stack, parent_tid, tls, child_tid)` takes the child's tid
     word in **x4**. The x86 gate has it in `r10` (the fourth argument). The AArch64 gate binds
     `x0, x1, x2, x4`, `stack x1`. A naive mapping (`r10` -> `x3`) would hand the kernel the tid word
     as `tls` and the join would hang.
  2. `gabbro_os_seitengroesse` answers **65536**, not 4096: AArch64 Linux runs 4/16/64 KiB base
     pages and the binding cannot ask (it would need `AT_PAGESZ`). A 4 KiB-aligned `mprotect` is
     `EINVAL` on a 16 KiB kernel. (Consequence: finding F2.)
  3. Each assumption names its own falsifier `sonde_os_*_a64`; none exists as a program (the x86
     probes do not falsify an AArch64 claim).
* Measured: `gabbro check` 0 errors; `emit` compiles with `-Wall -Wextra -Werror`.
* `instrumente/pruefe-emission.sh`: `MARKE_EMIT_BIB` 2 -> 3 (the new file emits). **The emission
  check was started but did not complete**: the machine OOM-killed it at stage 9 (the host had 8 GB
  available at the time); stages 1-8 and 22b passed in that run. So `MARKE_EMIT_BIB=3` and the
  freestanding count are NOT re-measured here - the merger must re-measure.

## 4. Running under qemu-aarch64 (`messung/arm-c/units.sh`, `run3.sh`, `run_hosted.sh`)

| Unit | Result |
|---|---|
| `74-syscall-schreiben` (-O0, -O2) | `ok` / `3` = expected; poison (`svc #0` -> `nop`) prints `1` |
| `90-syscall-errno` | `777` = expected |
| `96-buffered-writer` | `hello` / `2` = expected |
| `158-arena-commit` with `linux-aarch64.gab` (mmap/mprotect) | `118` = expected, -O0 and -O2 |
| `159-laufzeit-start` (real `clone` threads, trampoline, futex join) | `64` = expected, -O0 and -O2 |
| `175-puffer-gibt-seiten-zurueck` + binding | **SIGSEGV** with granule 65536; `7` (expected) with a 4096 binding - see F2 |

Agent A's 6 failures (74, 90, 96, 158, 159, 175-gebunden) become 1 (175-gebunden): 46 + 5 = 51 of
52. This is arithmetic over agent A's list plus my six individual runs, not a re-run of the whole
derived harness. Stages 6-8 (UBSan, ASan, certificate, poison) are not run on AArch64, as before.
Not run at all: the inline `child` trap (155, 156, 160, 1114: number 1000 is not an OS number) -
it compiles; the trampoline path IS exercised by 159.

## 5. Lean (`grammatik/Grammatik/Kern/Semantik/SyscallArmLinux.lean`, commit bd52a3e1)

Agent D's `SyscallArm.lean` states the ABI as data but is wired to nothing. Added, building on it:
the nine gates of `linux-aarch64.gab` as `SysAbiArm` values, with `alleTore_gut_und_nummer` (every
gate well-formed, carrying the number the binding declares), `alleTore_nummern_verschieden`,
`alleTore_ergebnis_x0`, `klon_stapelreg_gut`, `klon_ist_nicht_linuxAbi` and `klon_kind_in_x4` (the
x4 fact, as a theorem), and the witness `klon_aufruf_zeuge`. Imported in `Grammatik.lean`.

* **Measured:** the file compiles standalone with `lean` against the warm `.lake` of the main
  checkout; `#print axioms`: only `propext` / `Quot.sound` (no `Classical.choice`, no `sorry`).
* **NOT measured:** a full `lake build` of `grammatik/` (the machine had just been OOM-killed; I
  did not risk a 356-job build), hence **`gabbro_ziel` was not re-printed**. The change adds one
  module that nothing imports but `Grammatik.lean`, and touches no existing definition, so it
  cannot move `gabbro_ziel`'s axioms - but that is a reading, not a measurement.
  `lean-layout.py --check`: OK.
* `crates/gabbro-check/tests/arm_abi.rs` (4 tests, pass): holds the numbers of `SyscallArm.lean`,
  the gates of `linux-aarch64.gab` and `register_fuer("aarch64")` against each other by text.
  This is what "the checker's table agrees with SyscallArm.lean" means today: **a drift test, not a
  derivation** - the Rust table is not generated from the Lean file.

## 6. Test counts

`cargo test -p gabbro-check --no-fail-fast` (CARGO_BUILD_JOBS=2): **1420 passed, 1 failed** on the
first run. The one failure, `zertifikate::jedes_angenommene_programm_ist_zertifiziert_oder_benannt`,
was `grammatik/Grammatik/Zertifikat/REGISTER.txt` out of date: gifts 1402 and 1403 are accepted by
the Lean exporter's front (`UNCERTIFIED LG001`, "a G declaration needs at least one table"). Regenerated with
`GABBRO_ZERTIFIKATE=schreiben cargo test --test zertifikate` (TOTAL 224 -> 226 accepted, 194 -> 196
uncertified), test now passes. The workspace-wide suite (`gabbro-cli`, `gabbro prove` over
`programmlogik/`) was NOT run: `programmlogik/.lake` (mathlib) is absent in this worktree and
`AGENTS.md` records that this hangs `cargo test`.

## 7. Findings (need the coordinator, agent D or a Lean change)

* **F1 Lean templates are x86-only.** The AArch64 stub, inline trap, trampoline and `_start`
  have no template in `schablonen.rs` (the prose at `schablonen.rs:214-222`, `:400-420` names
  `rsp + 8`, `andq`, `ud2`). `SyscallArm.lean` states the AArch64 alignment premises
  (`start_nolibc_arm`, `kind_region_arm`, `trampolin_kind_arm`) but nothing links them to the
  emitted text or to the Rust register (`saetze.rs` says so in `syscall.stub`'s `vorbehalt`).
  The emitter text for aarch64 is therefore **unproved**.
* **F2 Latent defect in the emitted page-return helper, on x86 too.** `gabbro_region_leeren`
  (template `region.leeren`) computes `bis = (a+bytes)/seite*seite - a` in unsigned arithmetic. For
  a range lying inside ONE page `bis` wraps to ~2^64, `von < bis` holds, and the helper then
  zeroes far past the buffer / calls `madvise` with a huge length / segfaults. Reproduced on x86
  with the UNMODIFIED base binary and `linux.gab`: `175` with `reset RING at 10 count 100;`
  exits 139 (`.claude/muse-arbeit/kratz-c/leer/`). It is invisible with 4096-byte alignment and a
  page-aligned range; the 64 KiB granule of the AArch64 binding exposes it in example 175. Fixing
  it changes a proved template (`region.leeren`, `SchablonenArena.lean` §2): needs Lean. I did not
  work around it by lowering the granule to 4096, which would break 16/64 KiB-page kernels.
* **F3 `nolibc` `_start`** (`bau.rs:2847`) is x86 text (`xor %ebp,%ebp; and $-16,%rsp; call`);
  172/173/183 compile for AArch64 with `-ffreestanding` but cannot link/run there. AArch64 text:
  `mov x29, xzr; mov x9, sp; and sp, x9, #-16; bl <entry>; brk #0`. Template `start.nolibc` is
  proved for x86 only (`start_nolibc_arm` exists in Lean). Not done: needs the unit's arch at
  `prozess_start` and a Lean template.
* **F4 `SysAbiArm` is not accepted by `Ax`/machine G** (D's own CUTS). Generalising `SysAbi` over a
  register type edits `Syscall.lean`, `SyscallPaarung.lean`, `CloneHandoff.lean` and the exporter
  `lean_g.rs`. I did not attempt it in this session (no full Lean build possible, see section 5);
  `lean_g.rs` still sees only the x86 register names for `Ax`.
* **F5 Falsifier programs `sonde_os_*_a64` do not exist.** Also `instrumente/pruefe-sondendeckung.py`
  aborts in its own speech test (pre-existing, as its comments say) and its booked mark is stale:
  `aussen` measures 34, `MARK_AUSSEN = 33`, with or without my file.
* **F6 Remaining x86-only Rust**: `abi metal` (no aarch64 row), `entry`/`entrust`/`boot` and
  `device ... at port` refuse non-x86 (`emit.rs:4815`, `18791`, `18900`, `18995`), `bau.rs:1675`
  metal entries, the metal driver strings in `treiber.rs`. Bare metal on AArch64 is a new runtime.
* **F7 Weak CAS / LL-SC bound, volatile MMIO barriers, `-ffp-contract=off`** from agent A's report
  are untouched here.
* **F8** `cargo`-built `qemu` core dumps: the SIGSEGV runs left `qemu_*.core` files in the worktree
  root; deleted, not committed.

## 8. How to reproduce

```
bash messung/arm-c/units.sh target/debug/gabbro $S/u1      # 17 units rewritten to aarch64, check/emit/compile
bash messung/arm-c/run3.sh $S/u1                            # 74/90/96 under qemu + poison
bash messung/arm-c/run_hosted.sh target/debug/gabbro $S/h1  # 158/175/159 with linux-aarch64.gab
cargo test -p gabbro-check --test arm_abi
LEAN_PATH=<warm .lake>/build/lib/lean lean grammatik/Grammatik/Kern/Semantik/SyscallArmLinux.lean
```
