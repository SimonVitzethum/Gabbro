# The LLVM backend: checked Gabbro to a static binary, no C anywhere

*Rewritten 2026-10-17. This is the current backend. The C11 emitter is deprecated
(2026-10-15) and described in [`C-SPEICHERMODELL.md`](C-SPEICHERMODELL.md).
The compiler is UNTRUSTED: the checker runs first, and nothing here is a verified
translation. Final-byte refinement (source -> model -> machine bytes, in Lean) is
planned work, see [`PLAN-UEBERSETZUNGSVALIDIERUNG.md`](PLAN-UEBERSETZUNGSVALIDIERUNG.md).*

## 1. What it is

```
Gabbro --check--> LLVM IR text (.ll) --opt -O3--> llc -O3 --> ld.lld -static -e _start --> binary
```

`crates/gabbro-check/src/llvm.rs` (plus `llvm/stackless.rs`, `llvm/memory.rs`) lowers a
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

`gabbro build` (the manifest build, [`BAUSYSTEM.md`](BAUSYSTEM.md)) does not drive this
backend; it drives the legacy C path. The LLVM backend is reached through the commands above.

The tool set is closed: `gabbro`, `opt`, `llc`, `ld.lld`, `readelf`, and `qemu-aarch64` for
execution only. `clang`, `cc` and `gcc` never run.

## 2. Position on safety: the checker decides, the backend refuses by name

The backend proves nothing. It lowers only what the built passes decided, and every form it
cannot lower is refused **by name** instead of guessed (the `C001` rule of the C emitter):

| Code | Refuses | Poison probes |
|---|---|---|
| `Y101` | a type or a declaration without a lowering (bodiless or layout-less records, odd device registers, non-constant table counts, float words outside `f32`/`f64`…) | `beispiele/gift/1427` |
| `Y102` | an item or a gate shape: masked locks, stack-carrying, kernel-paired and unbound gates, assembly bodies, a gate without a body for the target (`arch` mismatch) | `gift/1428` |
| `Y103` | a statement: shared lock acquisition, `publish` with payload, non-constant bounds in arenas/`retry`/`exchange`, unlowerable tree walks and traversals, pressure probes of the wrong shape, a runtime gate the target lacks | `gift/1433` |
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
| globals, atomics | plain cells; atomics with their orderings, arrays included; `await`/`exchange` bounded; `publish nothing` a release store |
| `locks` | generated ticket lock (exclusive acquisition) |
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

**Locks.** Exclusive acquisition is a generated ticket lock. Shared acquisition and
IRQ-masking locks are refused (`Y103`, `Y102`).

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
| `Deklaration.maskiert` | IRQ masking and interrupt nesting | `Y102` |
| `Deklaration.Reg`, `Stmt.regSchreib`, `Block.regLies*` | model-register/export bridge (surface devices lower through `volatile`) | `Y10x` |
| `Stmt.publish` with payload | OFFEN O25, not covered by the goal theorem | `Y103` |
| `Stmt.locks` shared | an own primitive, unproved | `Y103` |
| `Deklaration.Ax`, `Block.bindAxiom*` | stack-carrying/paired/unbound gates, `child` (the internal `start` trampoline does not implement that source form) | `Y102` |
| `Programm.unterbricht` | hardware-dispatched entries, boot/entrust/asm lowering | `Y102` |
| library call surface | library resolution and payload model | `Y104` |
| static pointer decay | global array-address initialiser | – |
| `ArenaForm` / `DynForm`, `free` | full G exporter and statement bridge (`LG005`) | – |
| module-qualified emitted names | OFFEN O40 remainder: LLVM mangles `m_` only on a collision | – |
| OS profiles | the runtime books Linux gates; OS-neutral bindings and the per-access target-to-GX proof | – |

`TODO.md` section 4 carries these with their IDs.

## 9. The Lean certificate (`gabbro llvm-cert`)

Same checked unit, same lowering run as the IR: one run, two outputs, deterministic
(`BTreeMap` throughout; same source, same bytes, twice). Core Lean syntax only, no import,
**no LLVM** in it:

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
