# Long-range plans: generated-program corpus, `async`, self-hosted compiler

*Moved out of `TODO.md` (Phase C items 10, 11, 12) on 2026-10-20, text unchanged in substance. **None of the three is started:**
Simon asked for no new agents for now (2026-10-18). `TODO.md` keeps the status and the order of work; this file keeps the designs.*

## 1. One-off corpus of ALL generated programs (Simon, 2026-10-18)

**Goal.** Generate ONCE every valid program and every single-fault refusal up to the largest size bound that fits, over the 16
declarations of the family, store them zstd-compressed in a git SUBMODULE (at most 30 GiB on disk), generated one after another with
low RAM, reused until the next language change.

**Facts.**
- The set of all valid programs is infinite, so "all" means all up to a size bound. Skeletons grow ~10x per size (sizes 2..8:
  2/0/8/56/532/5170/56906; 52 500 valid programs at bounds 7/7/5 measured). The bound reaching 30 GiB is estimated at size ~10
  (a guess: ~50-200 bytes per program as a compact G-term encoding, ~30-60 bytes with a trained zstd dictionary; unmeasured).
- **Low RAM:** replace the memoised child tables (size 8 needs 2.3 GB, size 9 does not fit in 16 GB) by COUNTING AND UNRANKING
  (functional enumeration of algebraic types, FEAT): a small table counts the terms per (type, context, size); `unrank n` returns the
  n-th term of a size without storing anything. Index ranges are generated independently (parallel, resumable, deterministic,
  constant memory); completeness stays the proved theorem (every term has an index).
- **Speed:** the current run does ~36 programs/s; 10^8-10^9 programs need 10^4-10^5/s, so a native parallel run (20 threads).
- **Storage:** shards of ~64 MB per (declaration, size, range) with checksums and a manifest. The submodule remote CANNOT be plain
  GitHub (100 MB file limit, ~5 GB advice): use an own server, a local bare repository, or git-annex/LFS with own storage. Keep the
  submodule WITHOUT history (every language version a fresh repository, the main repo holds only its id), otherwise every
  regeneration adds another 30 GiB to history.
- The manifest carries the hash of the Lean model (`Kern/Syntax` and `Akzeptiert`): a changed language makes the guardian report the
  corpus stale.
- Stored are G terms, not source text, until the G-to-source printer exists (the Rust checker and compiler need source text: still
  the blocker for measuring them).
- This leaves Simon's older rule "no regenerable generated files in the repo" on purpose, because generating is expensive; the
  submodule lives outside the main repo.

## 2. `async fn` and `.await` in the Lean model (asked 2026-10-18; decided by the coordinator under "strongest variant")

**Today.** No async exists: `awaits` is the acquire side of `publishes` (message passing on an atomic flag), not a suspension;
`stackless` only removes recursion; "async device step" is out of scope (SYNTAX 16.3).

**Design A, not B.** `async fn` is sugar, a VERIFIED transformation into a state machine (a record with a state field and the locals
that live across a `.await`, plus a `poll` function with `match` over the state), built only from existing forms (sums, `match`,
tables, atomics). Machine G and the text of `Spec.lean` stay untouched (layer approach, as for the interrupt mask and the
reader/writer lock). Option B (a suspension step in machine G) is NOT chosen: a saved `GRest` is not a finite data value in memory, so
a future would have to encode it, which is the transformation of A, and B changes the goal.

**To prove in Lean:**
1. a direct-style small-step semantics of `async fn` with suspension and resumption as the specification;
2. the transformation and its refinement (simulation);
3. the safety rules the checker must enforce at every `.await`: values living across it are fields of the state record (explicit
   save, no pointer into a stack: no Pin problem); NO lock held across a `.await` (or only with a rank rule: deadlock hazard);
   unique ownership across the suspension point; bounded cost and budget per `poll`;
4. drop/cancellation of a future and what happens to its resources (open decision).

**Goal statement.** Progress is NOT claimed (wait bounds and fairness are NOT CLAIMED). An `.await` on a future that is never woken is
a wait stop like a flag stop, not an error.

**Prerequisites for a usable runtime:** the ring buffers and lock-free structures of Phase B item 5 (task queue, wakers).

**Order:** (a) an executor library in Gabbro with hand-written state machines from the existing forms (shows where the forms fall
short); (b) `async fn` in the Lean model (estimate 4 000-8 000 lines, two to four agent runs, a guess); (c) parser, checker rules and
the transformation as a lowering.

## 3. Self-hosted Gabbro compiler (Simon's idea, 2026-10-18)

**Decision of Simon (2026-10-18):** the compiler stays Rust + LLVM (more flexible and faster); no own backend and no Lean compiler
(they would need a CPU model for their refinement; the CPU itself is the model, `PLAN-TRANSLATION-VALIDATION.md` §9c). A self-hosted
compiler therefore keeps LLVM as its back end: only the language of the FRONT END changes, never the back end.

**Bootstrap, as for Lean, TypeScript or Go.**
- Stage 0 is EITHER the existing Rust compiler (it compiles everything already) OR the Lean pipeline compiled natively (parser,
  elaboration, `Akzeptiert`, G to `Code`; its small runtime is C/C++ and counts as trust base only as the start, never inside a
  shipped binary).
- Stage 1 is the Gabbro-written compiler built by stage 0; stage 2 is stage 1 compiling itself; stage 1 == stage 2 is the fixpoint
  test. Also diverse double compilation (stage 0 and a second path compile the same source, results compared) against the
  trusting-trust problem.
- The compiler source is written in a SMALL SUBSET that stage 0 handles (today the Lean pipeline elaborates 22 of 72 surface
  constructs, 73.6 % of the slice); stage 1 handles the whole language and extends itself, as bootstrap compilers do. Track P need
  not be finished first.

**Trust.** The Gabbro-written compiler is an UNTRUSTED producer; the Lean side validates each result (checker verdict against
`Akzeptiert`, generated IR against `Code` per function, the generated-program set and the adequacy theorem as the differential
test). It is memory-safe and race-free by the language itself and the best test of Gabbro's power.

**Missing today:** strings (only bounded strings exist), dynamic containers as libraries (lists, trees, hash chains are proved in the
model, not yet libraries), file IO through declared gates (possible), no generics and no closures (every container copied per type),
loops need static bounds (fixed limits on program size).

**Order:** (1) Track P as far as the compiler source needs; (2) libraries in Gabbro (strings, arena containers, file IO); (3) lexer
and parser in Gabbro with a differential test against the Lean lexer/parser over the generated programs; (4) the checker as Gabbro
functions (the ten components, per function) validated against `Akzeptiert`; (5) lowering and IR emission validated per function,
then the fixpoint.

**Estimate (a guess):** compiler 40 000-100 000 lines of Gabbro, libraries 10 000-20 000, extra Lean 2 000-6 000 (drivers, fixpoint,
per-function validator), plus Track P 5 000-15 000 for the subset used.
