# Long-range plans: generated-program corpus, `async`, self-hosted checker and compiler

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

## 3. Self-hosted checker and compiler, written in Gabbro (Simon, 2026-10-25)

*Supersedes the sketch of 2026-10-18 (in git). The back-end decision of 2026-10-18 stands: LLVM stays the back end, the
self-hosted tools emit LLVM IR. Nothing here is started; the order of work is §3.8.*

### 3.0 The goal, and what may be said at the end

Two Gabbro programs, `gpruef` (the checker) and `gkomp` (the compiler, front end shared with `gpruef`), compiled by
themselves, with an initial Lean runtime as stage 0 and no Rust on the trust path.

* **The checker is proved, not tested.** For every source text `src`, the run of `gpruef` terminates and its verdict is
  the Lean verdict: `pruefSpec src` := the Lean pipeline (`uebersetzeAllg`, `Parser/Elab/UebersetzePipeline.lean`)
  followed by `AkzeptiertX`. Proved with GabbroV against the Lean model (§3.4).
* **The compiler is proved through the test sets M and N.** Its neutrality, termination and determinism are THEOREMS
  about its own G program (§3.5); its agreement with the model is established on the finite adequate set M ∪ N
  (`PLAN-TEST-SET.md`); the adequacy theorem `hinlaenglich` (`CHECKER.md` §16.2) then gives agreement on every
  program. What `CHECKER.md` §16.1 lists as hypotheses H1-H7 about the Rust code become proved properties here.
* **Outside, named:** H8 (LLVM's passes, `llc`, `ld.lld`: translation validation, `PLAN-TRANSLATION-VALIDATION.md`
  §9c), the hardware, and the stage-0 runtime (§3.1).
* **May be said:** "`gpruef` decides `AkzeptiertX`; `gkomp` agrees with the model's lowering on every program, given H8."
  **May not be said:** "the binary is verified" (that is §9c's statement, not this one).

### 3.1 Stage 0: the initial Lean runtime

Machine G is executable in Lean (`execEnd`/`execBlock` are computable functions). Stage 0 is a Lean executable
`gabbro-boot` (a `lake exe`):

1. It reads the source of `gpruef`/`gkomp` and runs the Lean pipeline on it (lex, parse, elaborate, lower onto
   `declOf u`): the result is a G program, checked by the Lean `Akzeptiert`/`AkzeptiertX` -- so the self-hosted tools are
   themselves accepted programs, and `gabbro_ziel` (memory safety, race freedom, contracts) holds for them.
2. It RUNS that G program on machine G inside Lean. The oracle (`Orakel`) implements the program's declared gates --
   open/read/write/exit and the open region's provider -- with Lean `IO`. This oracle is the one piece of the Lean
   runtime that is trusted: its answers must meet the gates' contracts and `GutO`; what can be proved about it is proved
   (`GutO` for the IO oracle is a Lean theorem), the rest is the named assumption *boot oracle*.
3. The run is `gkomp` compiling its own source and `gpruef`'s: LLVM IR, then `opt`/`llc`/`ld.lld` (H8) give the stage-1
   binaries.

Stage 0 is slow (an interpreter of G in Lean) and is used once per bootstrap, never in a shipped binary. Its trust base
is Lean's kernel for the proofs and Lean's compiler/runtime for the evaluation of the stage-0 run.

### 3.2 Stages, fixpoint, diverse double compilation

* **S0 → IR₀:** `gabbro-boot` runs `gkomp` on its own source in Lean.
* **S1 = link(IR₀):** native. S1 compiles the same source → IR₁. **IR₁ = IR₀ byte for byte**: by the determinism
  theorem (§3.5 b) any difference is a bug of the back end or of the boot oracle, never of `gkomp`.
* **S2 = link(IR₁)** compiles again → IR₂ = IR₁ (the fixpoint).
* **Diverse double compilation:** every program of M ∪ N is compiled by the Lean-interpreted `gkomp` and by the native
  S1; the outputs are compared. Against the trusting-trust problem the two paths share no compiled code: one is Lean's
  evaluator over the G semantics, the other LLVM's output.

### 3.3 What the compiler's source needs from the language (Lean model first)

The tools read inputs of unbounded size, so they need the open region and unbounded loops, each modelled in Lean
before use (CLAUDE.md):

| Need | State |
|---|---|
| storage without a ceiling: `table T from p`, `alloc T`, references, ownership of references, refinement to `ArenaStorage.Heap` | done in the Lean model and its Lean front end (PLAN-DYNAMIC 14) |
| release of region cells (a provider-side `free`, grants for references) | open |
| bounded strings `string max N` in G; byte buffers in the open region | strings exist outside G; to be brought into G |
| file IO as declared `syscall` gates with contracts (open, read, write, exit) | gates exist; contracts for a file interface to write |
| loops and recursion over input-sized data with a termination measure (`Logik/Terminierung`: `Klasse`, `Mass`) | model exists; the checker's acceptance of measure-based loops to extend |
| containers as Gabbro libraries over the open region (vector, hash map, tree), with GabbroV contracts | open |
| no generics: one container instance per element type, written once by a generator in Lean (not a macro in the language) | decided by design |

### 3.4 `gpruef`, verified with GabbroV and the Lean model

* **Shape:** `gpruef` mirrors the Lean functions one to one -- lexer = `lex`, parser = `parseTopTief`, elaborator =
  `elabU` + lowering, the ten components of `AkzeptiertX` = `komp`. Every Gabbro function carries the contract "returns
  what its Lean counterpart returns" (`ensures result == ⟦counterpart⟧(args)`), stated through GabbroV's `Body` model,
  which is computed from the source by the generic bridge (`GABBROV.md` §14). The proof is then one simulation lemma per
  function, not one argument about the whole checker.
* **Theorem `gpruef_korrekt`:** ∀ `src`, the run of `gpruef` on `src` (any boot oracle meeting the gates' contracts)
  ends within an explicit budget and returns `pruefSpec src`. Termination is part of it (§3.5 a, same method).
* **Refusals:** the verdict is the Bool; the reported component is `NurAn c` of the refused cell. Diagnostic texts are
  outside the theorem.
* **Twin check:** the proved checker also runs over M ∪ N and over R (`PLAN-TEST-SET.md`); a disagreement there is a
  proof gap (it cannot happen if the proof is complete) and is recorded as a finding.

### 3.5 `gkomp`: neutrality, termination, determinism -- proved

Let `komp_g src` be the output of the run of `gkomp`'s G program on input `src` (machine G, the boot oracle for IO),
and `kompSpec p` the model's lowering of the elaborated program `p` (`Code/Lower`, validated by `Code/Refine`).

**(a) Termination.** ∀ `src`, the run returns (not by budget exhaustion) within `passes ≤ c · |src|^k`: every loop and
recursion of `gkomp` has a measure (`Logik/Terminierung/Mass`), and the budget bound is a theorem, not a measurement.

**(b) Determinism.** The output is a function of the input bytes:
* two oracles that give the same answers at the input gates give the same output (the other gates -- output, exit --
  return nothing the program branches on);
* **address neutrality:** the provider may answer any fresh cell; the output is invariant under every renaming of
  region cells (the program never orders or prints references -- a noninterference statement over the reference values,
  `Nichtinterferenz/`);
* `gkomp` is single-threaded in its first version (no `concurrent`); a parallel version later needs schedule
  independence, from race freedom plus deterministic joins.

**(c) Neutrality, H1-H7 of `CHECKER.md` §16.1 as theorems.**
* **H1 (syntax-directed, finite state):** `gkomp`'s core is a fold over the elaborated tree, `node : Ctor → List St →
  St` with a FINITE state type `St`; theorem: there is an `Automat` (`Adaequanz/Baum.lean`) whose run equals `komp_g` on
  every tree, with the state bound `m = |St|` explicit. With the fine cells: `gkomp` is an instance of `NeutralF`
  (`Gen/Fein/Neutral.lean`, `compiler_fein`).
* **H2 (names):** renaming identifiers renames the output's symbols and nothing else.
* **H3 (data):** constants reach the control only through their range class; otherwise they are copied into the IR --
  a noninterference statement with the class as the public part.
* **H4 (order):** reordering independent items permutes the output's items.
* **H5** is (b). **H6** (bounded mark multiplicity) and **H7** (whole-program conditions as bounded patterns: a
  function's code depends on its own body and the signatures it calls, `WRAP`) are theorems about the fold.

**(d) The finite agreement.** M ∪ N must cover every cell (`deckung`, `CHECKER.md` §16; today 459 component cells and
4267 fine cells, 876 fine cells open since the search of 2026-10-23): the open cells are closed by witnesses or proved
unreachable first. For every test program `p` the agreement `komp_g (print p) ≈ kompSpec p` is checked by the Lean
validator of `Code/Refine` (kernel), on the output the stage-0 run computed (§3.6).

**Theorem `gkomp_korrekt`:** from (a)-(d) and `hinlaenglich`: ∀ `p` accepted by `AkzeptiertX`, `komp_g (print p)`
refines `kompSpec p`; with H8, the binary refines the model.

### 3.6 Where the evaluation is trusted

The proofs (§3.4, §3.5 a-c, the validator in d) are kernel-checked. The OUTPUTS of the test runs in (d) are computed by
running `gkomp` -- on machine G in Lean, by Lean's compiled evaluator (the stage-0 runtime), because unfolding an
interpreter run per test program in the kernel does not fit the memory budget (`UebersetzePipeline.lean`, O13). So (d)
rests on Lean's evaluator for the run and on the kernel for the comparison. `native_decide` stays forbidden in
`grammatik/`; the bootstrap tree records the evaluated outputs as data the kernel then validates.

### 3.7 What is deleted

When S2 reaches parity with the Rust checker and compiler on M ∪ N ∪ R and on the corpus, the Rust checker, the Rust
compiler and their tests are removed (CLAUDE.md: no legacy); the guardians `pruefe-pruefer.py` and `pruefe-llvm.py` then
measure `gpruef` and `gkomp`.

### 3.8 Order of work, estimates, critical path

| | Step | Gate |
|---|---|---|
| S1 | the language prerequisites of §3.3 in the Lean model (region release, strings in G, file-gate contracts, measure-based loops) | full Lean build, `gabbro_ziel` on the standard axioms |
| S2 | `gabbro-boot`: machine G in Lean as an executable with the IO oracle; `GutO` of the IO oracle proved; GRegion-sized programs run | the run of a probe program equals its Lean semantics |
| S3 | libraries in Gabbro (bytes, strings, vector, hash map over the open region) with GabbroV contracts | GabbroV GREEN |
| S4 | `gpruef` in Gabbro and `gpruef_korrekt` | kernel |
| S5 | `gkomp` in Gabbro (front end shared) and the theorems (a)-(c) | kernel |
| S6 | bootstrap S0 → S1 → S2, fixpoint, DDC; M ∪ N complete and agreed; `gkomp_korrekt` | kernel + fixpoint |
| S7 | Rust removed (§3.7) | the four guardians on the self-hosted tools |

**Estimates (ranges, a guess):** Gabbro code 50 000-120 000 lines (front end shared by both tools); libraries 10 000-25 000;
Lean 25 000-60 000 (GabbroV simulation lemmas for `gpruef`, the neutrality and determinism theorems, `gabbro-boot`).
**Critical path:** the language prerequisites (S1) → the libraries (S3) → the proof of `gpruef` (S4, the largest single
piece); the neutrality proofs (S5 c) are the least charted part.

**Decisions for Simon:** (1) the trust of §3.6 (the stage-0 evaluator computes the test outputs) -- accepted, or the test
set is cut until kernel evaluation fits; (2) the first `gkomp` single-threaded (recommended); (3) the Rust removal at
parity (§3.7), as the no-legacy rule says.
