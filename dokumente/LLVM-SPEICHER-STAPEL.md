# LLVM memory, stack and recursion

Implementation record, 2026-10-17. The compiler remains untrusted; final-byte
refinement is outside this change. No source checker rule is weakened.

## Recursion

The LLVM producer first keeps the existing jump-only lowering for pure tail
cycles. Every remaining cyclic call component is lowered to explicit frames and
one dispatcher loop. Indirect calls conservatively add all compatible internal
targets to the call graph; matching targets enter the same dispatcher rather
than recursively entering their public ABI wrapper. External code retains its
declared ABI and remains user logic.

Each frame contains its parent, return destination, resume state, saved allocator
position, arguments, local objects and temporary values. Branch-edge copies
preserve phi semantics. Locals whose addresses escape to another source call
remain at stable addresses while their frame is live. Different return types,
aggregate results and error channels use typed return destinations.

Frames are aligned within anonymous chunks (normally 1 MiB; larger individual
frames get a larger mapping). Extent arithmetic is checked before allocation.
Unwinding restores the previous allocator position and releases crossed chunks;
the outer ABI wrapper releases the remaining storage. Exhaustion traps explicitly.
Non-tail recursion still needs memory for pending work; it no longer grows the
native call stack with source call depth. Foreign callbacks and the foreign
implementation's own stack use are outside the producer's control.

`SchablonenStapel.lean` uses the actual `RufRahmenG`/`RufFadenG` representation,
proves lossless frame storage and bounded reservation, and states the unchanged
G-step obligation. It does not prove that Rust's instruction transformation
meets that obligation. `gabbro_ziel` and its statement remain unchanged.

## Thread lifetime

Every dynamic start invocation owns its control word, inaccessible guard and
8 MiB stack. A small target-specific assembly trampoline is needed because
compiler-generated parent code cannot safely continue with a replaced stack
pointer. It calls the source root on the new stack, then exits without returning.

All group members start before the parent joins. The parent waits on an atomic
completion read and a shared futex, retrying interruptions and raced waits. The
word is initialized before clone; `CLONE_CHILD_CLEARTID` clears it only after
actual child exit. Only then may the parent unmap the complete region. This
reuses `SchablonenFaden.faden_warte_korrekt`'s existing gate-contract ordering;
kernel behavior remains binding/user logic, not a new hardware assumption.

The runtime still contains Linux-profile syscall conventions. This change does
not implement arbitrary OS profiles, stack-carrying source gates or `child`.

## Arena and range memory

Free-list links live in a separate lazily touched metadata mapping, with live
counts for groups of approximately 1 MiB payload. There is no minimum element
width for release. Freeing the last live slot returns whole interior pages with
`madvise(DONTNEED)`, preserving the exact LIFO reuse order and neighbouring live
payload. Reset clears live counts/list/high water and returns used payload pages.
The reserve and committed/access-enabled prefix stay intact: residency is not
virtual commit. Partial boundary pages can remain resident; page return is best
effort. Pressure sampling also precedes reuse of a discarded empty chunk.

Metadata costs 8 bytes per touched free link, 8 bytes per chunk counter and one
additional fixed base word. Payload and metadata reservations are checked; failed
metadata reservation releases the just-created payload reservation. Sizes come
from emitted LLVM layouts, including struct padding and packed formats, with conservative access alignment, instead
of the previous fixed-size guess for named arena elements.

`ArenaSeiten.lean` proves that dead-chunk discard preserves live payload and the
next logical allocation of `ArenaDyn.FreiZustand`. It does not prove the producer
or kernel. The source-to-G export of newer arena forms remains partial.

Static `reset X at i count n` checks the complete interval and zeroes exactly
its bytes. Declared `gabbro_os_seitengroesse`/`gabbro_os_seiten_zurueck` bindings
can return whole interior pages, with overflow-safe absolute-address rounding.
Without bindings, zeroing still works. No raw anonymous-page rule is silently
applied to potentially file-backed static data. Explicit static alignment is
preserved. Zeroing avoids introducing an unresolved libc `memset` dependency.

The two allocation paths now initialize one common result-index cell; previously
the free-list path could read the high-water path's uninitialized index at -O0.
Failure paths use explicit traps, not optimizer assumptions.

## Validation and coverage

Run `cargo test -p gabbro-check --lib llvm:: --no-fail-fast` for execution witnesses
and `cargo test -p gabbro-check --test llvm --no-fail-fast` for the existing IR
tests. Execution witnesses cover 200,000 calls with 128 KiB native stacks, multiple
suspensions, stable locals, indirect mutual recursion, aggregate/phi returns,
error propagation, small-slot reuse, dead-page discard and repeated thread groups
whose barrier requires simultaneous roots. They run at -O0/-O3 on x86-64 and
qemu-aarch64. These are falsifiers/witnesses, NEVER coverage denominators.

Coverage is the explicit classification of actual Lean constructors and fields:
`python3 instrumente/pruefe-llvm-modelldeckung.py`, register
`dokumente/llvm-modelldeckung.tsv`. The checker fails for newly unclassified or
removed model members and missing implementation anchors. Classifications remain
reviewed data; the tool does not infer semantic correctness from a symbol name.

Validation record: the full workspace suite passed (1,585 tests, one existing
ignored test); the Lean grammar build passed (404 jobs), and the goal theorem
retains exactly `propext`, `Classical.choice`, `Quot.sound`. The focused LLVM
execution tests additionally cover allocation-layout padding/stride/overflow.
The checked model register currently contains 235 members, with partial/refused
and proof-only cases reported separately and no overall example-based percentage.

Publication gate: the legacy `instrumente/pruefe-emission.sh` aborted with exit 1
at `Differenztest sonde-kick`: the unchanged
`messung/proben/probe-transport-kick-berechneter-versatz.gab` computes an
unbounded `u64` base plus an offset. The checker reports M104/M101 for possible
width overflow before C is emitted. The probe, parser, checker, C emitter, CLI
and emission script are byte-unchanged from `dbda971d`; this task does not alter
the probe or weaken its refusal. Stages after the abort were not measured; ASan
had also reported that it could not start in this environment. The publication gate did not pass, so these commits remain local under the
standing never-push-red rule until the independent gate finding is resolved.
