# The LLVM backend: checked Gabbro to a static binary, no C anywhere

*Rewritten 2026-10-17. This is the ONLY backend: the C11 emitter was removed on 2026-10-17
(repository tag `archiv/c-emitter-2026-10-17`, see [`C-SPEICHERMODELL.md`](C-SPEICHERMODELL.md)).
The compiler is UNTRUSTED: the checker runs first, and nothing here is a verified
translation. Final-byte refinement (source -> model -> machine bytes, in Lean) is
planned work, see [`PLAN-UEBERSETZUNGSVALIDIERUNG.md`](PLAN-UEBERSETZUNGSVALIDIERUNG.md).*

## 1. What it is

```
Gabbro --check--> LLVM IR text (.ll) --opt -O3--> llc -O3 --> ld.lld -static -e _start --> binary
```

`crates/gabbro-check/src/llvm.rs` (plus `llvm/stackless.rs`, `llvm/memory.rs`, `llvm/masken.rs`,
`llvm/stapeltor.rs`, `llvm/eintritte.rs`) lowers a
checked tree directly to LLVM IR. No C source, no C compiler, no libc, no linked runtime:
locks, threads, arenas and the entry `_start` are IR the compiler writes, over raw
`syscall`/`svc` gates. `readelf` shows neither `INTERP` nor `NEEDED` (`baue-llvm.sh`,
stage 4). Targets: `x86_64` and `aarch64`, both LP64 little endian, as data
(`ZIEL_X86_64`, `ZIEL_AARCH64`).

| Entry point | What it does |
|---|---|
| `gabbro llvm [--target=x86_64\|aarch64] [--unit] [--testbuild] f.gab…` | IR text to stdout; `--unit` lowers the named files as one translation unit |
| `gabbro llvm-cert [--target=…] [--unit] f.gab…` | the Lean certificate beside the IR, same run, no LLVM inside (section 8) |
| `instrumente/teile/baue-llvm.sh [f.gab…]` (run by `instrumente/pruefe-llvm.py`) | end to end for both targets: check, IR, `opt`+`llc`, `ld.lld`, no-libc check, run (aarch64 under `qemu-aarch64`), compare |
| `crates/gabbro-check/tests/llvm.rs` | IR tests without the LLVM toolchain; `tests/noalias.rs` the `noalias` rule; `tests/beispiele.rs` runs the emitter over the `Y` gift probes |

`gabbro build` (the manifest build, [`BAUSYSTEM.md`](BAUSYSTEM.md)) drives this backend for
`program` and `object` units (checker, IR, `opt -O3`, `llc -O3`, `ld.lld`); kernel-module,
bare-metal and hosted-libc products, and a unit that uses another unit, are refused by name.

The tool set is closed: `gabbro`, `opt`, `llc`, `ld.lld`, `readelf`, and `qemu-aarch64` for
execution only. `clang`, `cc` and `gcc` never run.

## 2. Position on safety: the checker decides, the backend refuses by name

The backend proves nothing. It lowers only what the built passes decided, and every form it
cannot lower is refused **by name** instead of guessed (the rule the removed C emitter called `C001`):

| Code | Refuses | Poison probes |
|---|---|---|
| `Y101` | a type or a declaration without a lowering (bodiless or layout-less records, odd device registers, non-constant table counts, float words outside `f32`/`f64`…) | `beispiele/gift/1427` |
| `Y102` | an item or a gate shape: a lock masking something other than `irqs`, kernel-paired and unbound gates, a stack gate with no `child` region behind the call or whose handed stack is no declared integer, an `asm` body with no 1:1 LLVM form or only for the other machine, a port device on aarch64, `boot`, `entrust`, an `entry` the stub cannot carry (other arch, register without a frame slot, several `regs out`, a dispatch head that is not one `u64` per register, a duplicate vector, a non-constant vector or `ist`, `via` other than `idt`/`irq`; on aarch64 no `vector`, a vector above 15, a `via` that is not the slot's kind), a gate without a body for the target (`arch` mismatch) | `gift/1428` (`masks nmi`) |
| `Y103` | a statement: non-constant bounds in arenas/`retry`/`exchange`, unlowerable tree walks and traversals, pressure probes of the wrong shape, a runtime gate the target lacks (`publish` with payload and shared lock acquisition are lowered, see Locks and Publication) | `gift/196` |
| `Y104` | an expression: alignment probe, library call, bitwise operations on floats, unknown places/registers/functions, contract-only expressions in a body | `gift/1430` |
| `Y106` | a match shape without lowering | `gift/1432` |
| `Y105` | retired (the error channel is fully lowered) | – |

(`gift/1429` and `gift/1431` were retired with the forms that now lower. The list of `Y10x`
sites is in `llvm.rs`, the sentences in `crates/gabbro-check/src/saetze.rs`.)

What the checker settles before a line of IR exists: integer ranges, `narrow` and
conversions (M1, V1-V3); names; loops and `leave`/`next` targets; table indices (M1 + M4);
integer-`match` coverage (`N411`, because the lowered `switch` has no `default`); per-arch gate
registers (`N066`) and length clauses (`N464`). `effects`, `costs` and `contracts` are
erased: checked, not generated. A green run means "no built-pass finding", not "proved".

## 3. How each construct lowers

The authoritative per-member classification is the register of section 7. This table is the
reading aid.

| Model construct | Lowering |
|---|---|
| `int lo hi` | `i8`..`i64` by width; a scalar cell whose proven range is narrower lives narrower (`u32 in 0 .. 200` as `i8`); aggregates never narrow (one layout per named type) |
| `bool` / `never` | `i1` (atomics: an `i8` cell, converted at the edge) / `void` + `unreachable` |
| `opt n`, sums, `grund` | `%gabopt = {i32 tag, [8 x i8]}`; `{i32 tag, [P x i8]}` with `P` the largest case; `i32` |
| `f32`/`f64` | `float`/`double`; finite by construction; literals as hex floats; direct surface lowering (the exporter builds no `Ty.fl`) |
| `fnptr`, `ptr` | `ptr`; `&f` and indirect calls through the declared signature; device spaces as `volatile` |
| bounded strings | layout, literals, `lenof`, index, copy, concat, lexicographic compare |
| tables, slots, `count` | named layouts, GEP indices; `ops insert/remove/relabel` as inlined mutations; counting `count k in …` as a loop |
| globals, atomics | plain cells; atomics with their orderings, arrays included; `publish` (with or without payload) a release store, `await` ONE acquire load; `exchange` bounded |
| `locks` | generated ticket lock (exclusive); `locks shared` a reader/writer lock on the same ticket gate |
| `traverse`, tree walks | slots, elems, queues, ancestors (strict), descendants (post-order, stackless) |
| `retry`, `forever`, `breaking`, `leave`/`next` | counted bound with `bis` and named overrun handler; loops; the body runs; by name |
| `or R` channel | fallible signatures, `let … else` (option-index unpacking), reason values and matches, errno decoding at gates, `return e` propagation |
| devices | `volatile` accesses at declared offsets, bit extraction/insertion, `transition` as read-modify-write; `format` as a packed struct |
| `narrow`, `finite` | checked branch plus `llvm.assume`; float ranges and runtime bounds |
| `accumulates` | one cell (the per-core split is a proof obligation, not a byte) |
| `Inv`, guards, ranks, costs, `geist` | erased (the checker held them) |

`inttoptr` has exactly three sanctioned sites: device bases, region answers, and the arena
runtime base. No int-to-pointer conversion enters the language.

## 4. The generated runtime (Linux profile)

All of it is IR; the only thing underneath is the kernel. The compiler books the raw gate
numbers for `mmap`, `mprotect`, `munmap`, `madvise` and `futex` itself (`laufzeit_tor` in
`llvm.rs`), so **this runtime is a Linux profile, not an OS-neutral one**; arbitrary OS
profiles remain open (see `PLAN-HARDWARE.md`, `DESIGN.md`). User gates (`syscall` items)
lower from direct declarations: explicit `number`, `regs in/out`, clobbers, `abi linux`, a
matching `arch`, plain or errno-decoded. Same-name gates for different `arch` coexist; a call
with no gate for the target is `Y102` naming the architecture. `extern` items still emit
`declare`s but find no symbol at `ld.lld`: that boundary fails loudly at link time.

**Entry.** `_start` is emitted by the backend, calls `main`, and exits through a raw gate.

**Threads.** Every dynamic `start` invocation owns a control word, an inaccessible guard and
an 8 MiB stack. A tiny target-specific assembly trampoline exists only at the stack-pointer
switch (compiler-generated parent code cannot continue with a replaced SP); it calls the
source root on the new stack, then exits without returning. All members of a group start
before the parent joins; the parent waits on an atomic completion read and a shared futex,
retrying interruptions and raced waits. The word is initialised before `clone`;
`CLONE_CHILD_CLEARTID` clears it only after actual child exit, and only then does the parent
unmap the whole region. This reuses `SchablonenFaden.faden_warte_korrekt`'s gate-contract
ordering; kernel behaviour stays user logic, not a new hardware assumption.

**Locks.** (Reader/writer locks: see the paragraph below.) The lock is released at EVERY exit of its block: a `return` inside an `if` releases on
its own path and the fall-through path releases at the block end (before 2026-10-17 a `return`
inside the block emptied the lock stack and the other path kept the lock for ever; measured, a
second call hung), `leave`/`next` release only the locks taken inside their loop, and the value
of a `return e` under `locks` is evaluated BEFORE the release.

**IRQ-masking locks** (`lock L … masks irqs`, `llvm/masken.rs`). Taking the lock first saves the
executing core's interrupt state and masks, then draws the ticket; releasing frees the ticket,
then restores the SAVED state (never an unconditional `sti`: a lock taken under already masked
interrupts gives them back masked, like `raw_spin_lock_irqsave`). The saved word lives in a
stack cell of the function, so every path out (`return`, `leave`, `next`, block end) reloads it
and the stackless continuation lowering carries it across calls.

| target | save + mask | restore |
|---|---|---|
| `x86_64` | `leaq -128(%rsp),%rsp; pushfq; popq r; cli; leaq 128(%rsp),%rsp` | `leaq -128(%rsp),%rsp; pushq r; popfq; leaq 128(%rsp),%rsp` |
| `aarch64` | `mrs r, daif; msr daifset, #3` | `msr daif, r` |

(The `leaq` pair steps over the red zone: `pushfq` writes below `rsp`.) **What is verified and what
is not:** the IR text is tested (`tests/llvm.rs`, exact strings), `llc -filetype=obj` accepts it and
`objdump -d` / `aarch64-linux-gnu-objdump -d` show `pushf; cli; popf` and `mrs daif; msr daifset,#0x3;
msr daif`. **None of it is executed**: `cli`/`popfq` with IF and `msr daif` are privileged or trap
in user mode, so a Linux user-space program that TAKES a masked lock faults; a program that only
DECLARES one (examples 01, 53, ...) emits no instruction and runs as before. A lock that masks a
word other than `irqs` is `Y102` (`gift/1428`).

**Stack gates and `child`** (`llvm/stapeltor.rs`). A gate with `stack r` is the raw clone that
starts a second thread on the stack the program hands over; the kernel sets the child's `sp` from
register `r` and answers zero there. The child shares the parent's REGISTERS but not its frame, so
the `child { … }` region is OUTLINED to `gabbro_kind_N(handed stack)` (the checker's `N451`/`N452`
already restrict it to the handed slot and non-local places), and the gate's instruction itself
jumps there in the child:

```
syscall ; test answer ; jnz 1f ; mov stackreg -> first argument ; clear frame pointer ;
align sp to 16 ; call gabbro_kind_N ; trap ; 1:
```
(`aarch64`: `svc #0; cbnz x0, 1f; mov x0, stackreg; mov x29, xzr; mov x9, sp; and x9, x9, #-16;
mov sp, x9; bl …; brk #0; 1:`). The parent continues at `1:` with the registers the gate declares;
nothing returns into the parent's frame (the region ends in a never-returning call, `N448`/`N449`,
and the trap sits behind it). The `child` statement in the parent (reachable only if the gate answered
zero in the parent, which its contract excludes) calls the same function and ends in `unreachable`.
The call number, registers and flags are the program's own gate data. Executed: `messung/llvm/kind.gab`
(an `mmap`ed stack, clone with `CLONE_VM|FS|FILES|SIGHAND|THREAD|SYSVSEM`, the child runs a function on
the handed stack and ends the process with 42) returns 42 on both targets at `-O0` and `-O3`
(aarch64 under `qemu-aarch64`). The examples 155/156/160/1114 carry an `x86_64` binding only and lower
there (they have no `main` and call the unit's `extern fn ausgang`, so they stop at link time, by design);
on `aarch64` their gate has no body and the call is refused by name.

**Entries** (`entry …`, `llvm/eintritte.rs`; `x86_64` here, `aarch64` below). A vectored or entered `entry` becomes a
stub written as module assembly, a common body per kind, and a generated C-ABI half
`gabbro_eintritt_N_c(frame)`: the stub saves EVERY general register and the full x87/SSE state
(`fxsave`), clears DF, aligns, calls the half, restores and `iretq`s; the half loads the `regs in`
registers from the frame in declaration order, calls the dispatch (one `u64` per register) and stores
its answer into the frame slot of the `regs out` register, which the interrupted code finds after
`iretq` (every other register comes back unchanged: stronger than `preserves`). Exceptions 8, 10-14,
17, 21, 29, 30 push an error code: they get the TWIN stub that drops it before `iretq`.
`@gabbro_eintritt_vektoren : [256 x ptr]` and `@gabbro_eintritt_ist : [256 x i8]` list stub and IST
per declared vector. `entry … via irq` (a foreign kernel's interrupt path) is a plain
`gabbro_eintritt_N()` function head calling the dispatch. A unit with an entry compiles every
function `noredzone` (an interrupt frame on the same stack would destroy a leaf's red zone).
**Not claimed:** the declared `stack S per cpu` / `ist` is not switched to (the stub runs on the stack
the hardware gives; TSS and IDT are the builder's), the frame's space is in no program number, the
vector table is NOT an IDT (selector, privilege and gate type are the environment's), and no device
acknowledgement (LAPIC EOI) is generated: that is the dispatch's logic. Verified: IR tests,
`llc -filetype=obj`, `objdump -d` of stub and twin; **not executed** (the stubs are entered by
hardware; no user-mode run reaches them).

**Entries on `aarch64`** (`entry N vector V [via sync|irq|fiq|serror] arch aarch64`). The vector `V` of the
source IS the slot of the exception table (16 slots of 0x80 bytes, group `V / 4`, kind `V % 4`; a
`via` word is optional and must name the slot's kind, no `vector` means no slot: both refused by
name). The symbol `gabbro_eintritt_vektoren` is the table itself, `.balign 0x800` (a `VBAR_EL1`
value): a `b gabbro_eintritt_N` at each declared slot, `b .` at every other (an undeclared slot parks
the core). The head makes a 0x320-byte frame, saves `x0`/`x1`, hands the C half's address in `x1` to
the common body, which saves `x2`-`x30`, `ELR_EL1`, `SPSR_EL1`, `FPSR`, `FPCR` and ALL of `q0`-`q31`
(the dispatch may use any register), calls `gabbro_eintritt_N_c(frame)` (frame slot of `xN` at
`8*N`, same half as x86), restores everything and `eret`s. **Not claimed:** no `VBAR_EL1` write
and no `isb` (the program's start does it), no GIC acknowledgement, no stack switch (`stack S per
cpu` binds nothing), `EL1` only (`ELR_EL1`/`SPSR_EL1`), DAIF stays masked as the hardware left it,
`regs in/out` only `x0`-`x30`, `ist` and `via idt` refused. **Verified by execution:**
`instrumente/teile/eintritt-a64-qemu.sh` (stage 4 of `pruefe-llvm.py`) runs
`messung/llvm/eintritt-a64.gab` under `qemu-system-aarch64 -M virt` at EL1: a hand-written test
stand (apparatus, not product) sets stacks, `CPACR_EL1` and `VBAR_EL1`, takes an `svc` on slot 4
(`SPx`) and slot 0 (`SP0`), and checks the answer in `x0`, callee-saved `x19`/`x20`, `x30`, `FPSR`
and `SPSel` after the `eret`. Not executed: IRQ/FIQ/SError slots (no source of them in the stand;
the slots share the head and body with the executed ones), EL0 entry groups, any GIC.

**`asm` bodies** (`fn f(…) arch A = asm { … }`, `llvm/assembler.rs`). The body is a function whose
body is ONE `call … asm sideeffect` with the declared frame: `in`/`out` operands become LLVM operands
in the order the declaration lists them (`%[name]` -> `$k`, outputs counted first; `$` -> `$$`; `%eax`
stays), x86 single-letter register constraints `a b c d S D` become `{ax} {bx} {cx} {dx} {si} {di}`
(the operand's type picks `al`/`ax`/`eax`/`rax`), `r q i n` (x86) and `r w i n` (aarch64) pass,
`clobbers` become `~{memory}`/`~{cc}`/`~{reg}`. **Only for the arch the body declares:** a body for the
other machine is skipped when the unit also declares the same function for this target (a second
declaration with the other `arch` is the pair, like a gate's two `syscall` lines) and refused by name
otherwise. Refused by name: a constraint with no 1:1 LLVM form (memory, matching digits, `+`, `&`,
several letters), an operand that is no lowered parameter, an `out` that is not `result`, a result
type and `out { result }` that do not come together, `-> never` with an `out`, an error channel. A
`-> never` body loops after the text (the text is unchecked; `hlt` returns). **Verified:** IR tests,
`llc`, `llvm-objdump` (stage 3 of `pruefe-llvm.py`: `outb`, `syscall`, `invlpg`, `sfence`, `mfence`);
`messung/llvm/assembler.gab` (a per-machine pair of pure arithmetic and a barrier) runs natively and
under `qemu-aarch64` with the same exit code. **Not executed:** the privileged and I/O instructions
of `36`/`60`/`67` (`outb`, `invlpg`: a `#GP` in user space); what the text does on the machine
stays the assumption it is.

**Port space** (`device … at port`, `llvm/portraum.rs`, `x86_64` only). A register is `in`/`out` of
its width (`inb/inw/inl`, `outb/outw/outl`, 8/16/32 bits, port number in `dx`), the number is the
`u16` handle plus the offset in 16 bits, every access `asm sideeffect` with `~{memory}`. A `+=` at a
port register, any address use of one, a 64-bit register and banks/mirrors are refused by name
(`Y102`/`Y103`); the device is refused on `aarch64` (no port space, `gift/1470`, target-selected by
its `// ziel: aarch64` line). **Verified:** IR tests and `objdump -d` (`inb %dx,%al`, `outb %al,%dx`);
not executed (a `#GP` in user space).

**`boot` and `entrust` stay refused by name** on both targets, and the reason is the model's: the
Lean `Syntax.lean` section 14 reads `boot` and `entrust` as FOREIGN bodies (`Ax`) -- the boot steps
are `axiom` calls (`write_cr0`, no instruction in the source), register reads (`bootinfo_retten(ebx)`)
and a stack-pointer assignment, and no form of the source performs an `entrust` or names the
address it transfers to. Lowering either would invent semantics the language and the model do not
state; giving them one is a change of the language and goes into the Lean model first.

**Locks.** Exclusive acquisition is a generated ticket lock (`<L>.naechst`, `<L>.bereit`).
A lock that declares `shared held` (the checker refuses `locks shared` on any other one,
`gift/39`) is a reader/writer lock and carries a third `i32` word `<L>.leser`, the number of
readers inside. No C, no libc, the same IR on both targets (`llvm/leser_schreiber.rs`):

* *writer* (`locks L`): ticket as before, then wait until `leser == 0` (`acquire` load); it
  holds the ticket for the whole section, release is `bereit += 1`;
* *reader* (`locks shared L`): ticket, `leser += 1` (`acq_rel`), `bereit += 1` (the gate is
  open again), section, then `leser -= 1` (`release`).

Invariant: a reader enters only while it owns the ticket, so while a writer owns it no new
reader appears; a reader that entered earlier is counted before the writer's ticket is served
(the gate release is a `seq_cst` RMW the writer's `seq_cst` load of `bereit` observes), and the
writer waits for the matching `release` decrement, so reader sections happen-before the
writer's. The writer's `bereit += 1` publishes its section to the next reader's gate load.
Readers run concurrently with each other; tickets are FIFO, so a queued writer is overtaken by
no later reader (no writer starvation) and all waiting is a spin on a word the other side
changes (no sleep primitive, so no lost wakeup). `return`, `leave` and `next` release exactly
the locks taken inside the construct, per path (a `return` in an `if` inside `locks` releases on
that path; the fall-through path releases at the end of the block). IRQ-masking locks are
refused (`Y102`). Evidence: `messung/llvm/leserschreiber.gab` (two readers, one writer, a torn
pair; exit 42 on both targets; with the writer's drain removed from the IR the same program
fails 9 runs in 10).

**Publication.** `X = v publishes { payload };` is a `store atomic ... release` and
`let f = X awaits { payload };` ONE `load atomic ... acquire` (`llvm/publizieren.rs`): the
payload writes precede the flag store and the payload reads follow the flag load in program
order, and release/acquire keep them on their side on x86_64 (TSO) and aarch64 (`stlr`/`ldar`).
SPRACHE.md §11.1/§11.5: `publishes` forces at least release, `awaits` at least acquire; the
declared ordering is only ever strengthened (`seq` and the default stay `seq_cst`), never
weakened, and a payload on `relaxed` or an undeclared atomic is the checker's `V005`. The
checker's payload rule (N291) still demands the payload carriers be guarded by a lock in a
program with concurrent roots, so a checked concurrent test (`messung/llvm/nachricht.gab`)
guards them as well; the ordering evidence is the emitted IR (`tests/llvm.rs`) plus the
round trip, not a stress test of a bare payload. (Earlier `await` lowered to a spin loop
comparing the flag against the payload places -- a different program; it is one load, as in
the C emitter.)

**Recursion without native stack growth.** Pure tail cycles keep a jump-only fast path.
Every other cyclic direct (or compatible indirect) call component becomes one dispatcher loop
with explicit continuation frames, irrespective of tail position, return type or error
channel. Each frame holds its parent, return destination, resume state, saved allocator
position, arguments, locals and temporaries; branch-edge copies keep phi semantics; locals
whose address escapes to a source call stay at stable addresses while the frame is live.
Indirect calls conservatively add every compatible internal target to the call graph.
Frames live in aligned anonymous chunks (normally 1 MiB; larger frames get a larger mapping),
extent arithmetic is checked before allocation, unwinding restores the allocator position
and releases crossed chunks, and exhaustion traps explicitly (never falls into
`unreachable`). Non-tail recursion still needs memory for its pending work; it no longer grows
the native stack with source depth. Foreign callbacks and a foreign implementation's own stack
use are outside the producer's control. `SchablonenStapel.lean` states the storage and
resource obligations over the actual G frames and proves lossless frame storage and bounded
reservation; it does not certify the Rust lowering.

**Arenas (the heap).** Language semantics, checker rules and the Lean model are in
[`PLAN-DYNAMISCH.md`](PLAN-DYNAMISCH.md). The generated representation:

* five fixed words per arena (40 bytes): `basis`, `belegt`, `bereit`, `frei`, `meta`; BSS does
  not grow with the ceiling (1 GiB ceiling measured at 24 bytes in the first three-word
  version);
* reserve once as address space (no RAM); commit in 1 MiB steps on demand, computed in bytes
  (rounded up to 1 MiB, capped at the ceiling; a ceiling below 1 MiB commits its rest in one
  step); every failure takes the program's `voll` branch;
* the unbounded form `pb P blw B` asks the nullary probe `P` for free bytes before each commit
  (one call per MiB, none on the fast path) and runs the `else` below the threshold `B`;
  reuse of a discarded empty chunk samples before it consumes its free head;
* slot release `free A[i]`: LIFO reuse with free links in a SEPARATE lazily touched metadata
  mapping (8 bytes per freed slot, 8 bytes per ~1 MiB chunk counter), so there is no minimum
  element width and `u8` elements work. Freeing the last live slot of a chunk
  `madvise(DONTNEED)`s its whole interior pages, preserving neighbouring chunks, all free
  links, the mappings, access rights and the committed prefix; residency and virtual commit
  are distinct. Page return is best effort (partial boundary pages stay; small ranges may keep
  everything);
* `reset` clears counts, list and high water and returns used payload pages;
* payload and metadata reservations are checked; a failed metadata reservation releases the
  just-created payload reservation. Element sizes come from the emitted LLVM layouts (struct
  padding, packed formats, conservative access alignment);
* the allocation paths share one result-index cell (before, the free-list path could read the
  high-water path's uninitialised index at `-O0`); failure paths trap explicitly.

**Static range zeroing.** `reset X at i count n` checks the whole interval and zeroes exactly
its bytes (no `memset` import). Declared `gabbro_os_seitengroesse` / `gabbro_os_seiten_zurueck`
bindings (see `bibliothek/linux/linux.gab`) can return whole interior pages, with
overflow-safe absolute-address rounding; without them zeroing still works, and no
anonymous-page rule is applied silently to possibly file-backed static data. Explicit static
alignment is kept.

## 5. Facts handed to the optimiser

The lowering is naive (every `let` an `alloca`, every check a branch) and attaches what the
checker proved. Recorded 2026-10-17, **not re-measured wholesale in this rewrite**: over the 134
clean corpus units (x86_64), 131 `llvm.assume`, 192 `!range`, 1182 `!tbaa` (182 struct-path),
2 `noalias`, 2 `dereferenceable` (before the `noalias` extension below). A spot re-count over
`beispiele/*.gab` with the main checkout's debug binary: 139 of 170 files lower, 89
`llvm.assume`, 192 `!range` lines, 5 `noalias` words (the binary may predate slice 4).

| Checker fact | Becomes |
|---|---|
| a passed `narrow` | `llvm.assume` plus the checked branch |
| `requires` / `ensures` (comparisons) | `llvm.assume` at entry / before `ret` (what cannot lower is dropped silently; never the unit) |
| loop `invariant` | `llvm.assume` at the loop head |
| declared integer range | a narrower cell, and `!range` on loads from it |
| `forall s in slots of T : T.slots[s].f <= K` (also `P => Q`, `P && Q`, either side) | `!range [0, K+1)` on every load of `T.slots[*].f`, intersected with the declared range |
| scalar type | flat TBAA node; named record or table slot: struct-path TBAA `!{!struct, !member, i64 off}` |
| `own` pointer parameter | `noalias` |
| writable pointer parameter of a qualifying internal function | `noalias` (rule below) |
| `requires N <= lenof(p)` | `dereferenceable(N)` |
| `requires aligned(p, N)` | `align N` |

**The `noalias` rule (2026-10-17, `A1-OWN-PAPER.md` slice 4).** `noalias` is a fact about the
whole call, so a writable pointer parameter gets it only when the checker holds the whole call:
the function is not `pub`, has a body, is called from a body of its unit, has its address
nowhere taken, is named by no `entry`/`boot`/`concurrent` item, and its declared `effects` name
nothing but its own pointer parameters (`E008` keeps that list a superset of its callees').
Calls into it are held by `R014`; the one named assumption is `R015` (a `pub` caller with a
pointer pair assumes its parameters distinct). A unit with a function value outside a function
body gets no extension. Not proved in Lean: the LLVM lowering is not a Lean judgment (OFFEN
O27); the model side is `Logik/Vertraege/Objekt*.lean`.

Deliberately not there:

* `!range` on stores (LangRef allows it only on loads, calls, invokes): the store-side carrier is
  the narrowed cell.
* Narrowed aggregates: one layout per named type, so no conversion at a call, return or
  `extern`/gate boundary.
* TBAA on `i8`, `i1` and aggregates: bytes may overlay anything. Struct-path tags only where
  the verifier accepts the exact `(member, offset)`; an element inside an aggregate field falls
  back to the flat scalar node.
* Quantified clauses of other shapes (`reaches`, disjunctions, equality chains): they would need
  loop-level reasoning.
* `llvm.loop` metadata and `!prof` weights: the pipeline's own analyses decide; there is no profile.

**Pipeline.** `opt -O3` (middle end) then `llc -O3`; `llc` alone does not run the middle end
(measured slower than `-O0`). `messung/llvm/summe.gab`: 10 ms at `-O0` against 2 ms at `-O3`
(an earlier run: 20.3 against 3.3 ms), identical on both targets. That is Gabbro against
Gabbro, not against GCC: the 80 % minimum and 110 % target of `ARM-PLAN.md` are unmeasured.

## 6. Evidence

Execution witnesses build and run both targets at `-O0` and `-O3` (aarch64 under `qemu`, which is
no performance measurement): 200,000 non-tail calls on a 128 KiB native stack; multiple
suspensions and stable locals; indirect mutual recursion with aggregate returns and phi
continuations; error propagation; one-byte slot reuse; payload page discard with preserved free
links; checked static range zeroing; allocation layout padding/stride/overflow; repeated thread
groups whose barrier requires all roots to start before any join. They are witnesses, never a
coverage denominator.

```
cargo test -p gabbro-check --lib llvm:: --no-fail-fast      # execution witnesses
cargo test -p gabbro-check --test llvm --no-fail-fast       # IR tests
cargo test -p gabbro-check --test noalias --no-fail-fast
./instrumente/teile/baue-llvm.sh [f.gab…]                    # end to end, both targets (`pruefe-llvm.py` runs it over its programs)
```

## 7. Coverage against the Lean model

The denominator is the Lean model, never examples. `dokumente/llvm-modelldeckung.tsv` is a
checked register: one row per constructor/declaration field of the core syntax, signature,
program, arena and G-continuation families (235 members when measured 2026-10-17; the tool
prints the current count and per-family split), each with a class and an implementation
anchor:

```
python3 instrumente/teile/llvm-modelldeckung.py            # also run by instrumente/pruefe-llvm.py
```

`LOWERED`, `PARTIAL`, `REFUSED`, `ERASED`, `MODEL_ONLY`, `OPEN` are implementation
classifications, not compiler-correctness theorems; partial source-to-G export stays partial
even when a surface form emits IR. The check fails for missing, removed or duplicate members and
for missing anchors; it does not infer semantic correctness from a symbol name. Where the prose
here simplifies a case, the register wins.

## 8. Still open

| Model/surface boundary | Remaining work | Refusal |
|---|---|---|
| `Deklaration.maskiert` | lowered (`llvm/masken.rs`); open: the hardware run (privileged), nesting of masks beyond save/restore per lock | `Y102` for a word other than `irqs` |
| `Deklaration.Reg`, `Stmt.regWrite`, `Block.regRead*` | model-register/export bridge (memory-space surface devices lower through `volatile`; a `device ... at port` register lowers to `in`/`out` on x86_64 (`llvm/portraum.rs`) and is refused `Y102` on aarch64, `gift/1470`, which has no port space) | `Y10x` |
| `Stmt.publish` with payload, `Stmt.locks` shared | lowered (release/acquire; reader/writer lock); the Lean side stays OFFEN O25 for unguarded payloads and the lock primitive is unproved in Lean | – |
| `Deklaration.Ax`, `Block.bindAxiom*` | paired/unbound gates; stack gates and `child` lowered (`llvm/stapeltor.rs`), `aarch64` only where the program binds an `aarch64` gate | `Y102` |
| `Programm.unterbricht` | x86_64 entries and aarch64 vector-table entries lowered (`llvm/eintritte.rs`), asm bodies (`llvm/assembler.rs`); open: stack switch/IST, EOI, the IDT / VBAR write itself, boot/entrust (refused by name: foreign bodies in the model) | `Y102` |
| library call surface | library resolution and payload model | `Y104` |
| static pointer decay | global array-address initialiser | – |
| `ArenaForm` / `DynForm`, `free` | full G exporter and statement bridge (`LG005`) | – |
| module-qualified emitted names | OFFEN O40 remainder: LLVM mangles `m_` only on a collision | – |
| OS profiles | the runtime books Linux gates; OS-neutral bindings and the per-access target-to-GX proof | – |

`TODO.md` section 4 carries these with their IDs.

## 9. The Lean certificate (`gabbro llvm-cert`)

Same checked unit, same lowering run as the IR: one run, two outputs, deterministic
(`BTreeMap` throughout; same source, same bytes, twice). Core Lean syntax only, no import,
**no LLVM** in it. The output elaborates with plain `lean` (a test runs it on three certificates):

* `llvmEinheit`, `llvmZiel`, `llvmLayout`: what, for which target;
* `llvmFunktionen` (name, params, ret, linkage class), `llvmTypen` (named layouts);
* `llvmTore`: name, number, register bindings, out register, clobbers, template;
* `llvmEintritt`: `main` and its width (or `never`);
* `llvmAnnahmen`: the `narrow` successes behind each `llvm.assume`;
* `llvmArenen` (element layout, reservation, bound, ceiling; words `<Name>.basis/.belegt/.bereit/.frei/.meta`),
  `llvmSchloesser` (ticket words), `llvmFaeden` (roots owning guarded per-invocation regions).

It is input to refinement, not a proof: a proved validator would refuse bad output, including
ours; this file never grants it.

## 10. What validating this path would cost

The planned validator (`PLAN-UEBERSETZUNGSVALIDIERUNG.md`) checks the loaded final bytes
against the source-derived model, with the middle end untrusted, reusing W/GX for concurrency
plus a per-access target bridge. An LLVM middle end is one more untrusted byte producer: it adds
no proof architecture, only (a) the raw gate instruction (`syscall`/`svc`) and the entry as two
machine forms, one correspondence lemma per gate shape plus one entry lemma per target, and (b)
the optimiser, priced per property (the bytes must simulate G/GX) and not per pass. The
hardware instruction semantics (Sail Arm model, `ARM-PLAN.md`) are the shared critical path.
Standing falsifier at zero proof cost: the x86-64/aarch64 agreement `baue-llvm.sh` checks.

**Not claimed:** no validated binary exists; the correspondence record (`korrOk`) is C-only; the
per-access target bridge is open; the checker's carried residues (alias analysis, `E010` reach,
cost assumptions, pairing memory-model statement) stay out of the binary-safety argument.
