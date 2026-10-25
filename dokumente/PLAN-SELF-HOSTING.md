# PLAN-SELF-HOSTING — checker and compiler written in Gabbro, computing in Gabbro

*Simon, 2026-10-25. Nothing here is started. It supersedes `PLAN-LONG-RANGE.md` §3 (the versions of 2026-10-18 and of the
morning of 2026-10-25 are in git). The back-end decision of 2026-10-18 stands: LLVM stays the back end; the self-hosted
compiler emits LLVM IR.*

## 0. The rule of this plan

**Lean specifies and proves; Gabbro computes.**

* **Lean** holds the model (machine G, `AkzeptiertX`, the lowering `Code/Lower`, the generator's definitions, the
  adequacy theory of `CHECKER.md` §16) and the proofs. Its kernel checks proofs. Lean evaluates nothing on the trust
  path: no `#eval`, no `lake exe` driver, no kernel evaluation of a test run. The one exception is stage 0 of the
  bootstrap (§2), used to start and to cross-check, never to produce a result that a theorem rests on alone.
* **Gabbro** does every computation: checking, compiling, generating the test sets M, N and R, running them, comparing,
  counting coverage, searching witnesses for open cells, validating IR. Each of these is a Gabbro program, accepted by
  the checker, and proved against its Lean specification with GabbroV.
* The Lean drivers that compute today (`gen-abdeckung`, `gen-zellen`, `gen-fein`, the Lean pipeline as a driver, the
  `Code` validator as an executable) are replaced by Gabbro programs and deleted when those reach parity
  (CLAUDE.md: no legacy).

## 1. The programs

| Program | Computes | Proved against (Lean spec) |
|---|---|---|
| `gpruef` | the checker: lex, parse, elaborate, the ten components of `AkzeptiertX` | `pruefSpec src` := the Lean pipeline (`uebersetzeAllg`) then `AkzeptiertX` |
| `gkomp` | the compiler: the front end shared with `gpruef`, then LLVM IR | `kompSpec p` := `Code/Lower` of the elaborated program, refinement `Code/Refine` |
| `ggen` | the test sets: M (valid, `Gutes`), N (refused by exactly component `c`, `Schlechtes c`), R (text-level refusals), by exact size, and their printed texts | the Lean generators `genGueltig`, `genBad c` with their soundness and completeness theorems (`Gen/Erzeuger/Gueltig.lean`), the printer `Gen/Druck` |
| `gabdeck` | coverage: the cells (`Gen/Abdeckung/Zellen`) and fine cells (`Gen/Fein`) each program covers, the open cells, the greedy cover, the witness search | `zellenStimmen`, `feinZellen_uF`, `deckung` |
| `glauf` | the campaign: runs `gpruef`/`gkomp` over M ∪ N ∪ R, compares each verdict with the label and each IR with `gvalid`, writes the ledger | the comparison predicates of §4 |
| `gvalid` | per-program IR validation: the IR `gkomp` produced against the lowering of the model | the `Code/Refine` decision procedure |

Every one of them is an ordinary Gabbro program: accepted by `AkzeptiertX` (so `gabbro_ziel` gives memory safety, race
freedom, contracts), proved terminating, deterministic and correct with GabbroV.

## 2. Bootstrap: an initial Lean runtime, used once

* **Stage 0** (`gabbro-boot`, a Lean executable): the Lean pipeline turns the Gabbro source of `gkomp` into a G program
  (the Lean `AkzeptiertX` accepts it), and machine G -- executable in Lean -- runs it on its own source. The program's
  declared gates (open, read, write, exit, the open region's provider) are answered by an oracle over Lean `IO`; its
  `GutO` and the gates' contracts are proved where possible, the rest is the named assumption *boot oracle*. Output:
  LLVM IR₀; `opt`/`llc`/`ld.lld` (H8) give stage 1.
* **Stage 1** compiles the same source → IR₁; **IR₁ = IR₀ byte for byte** (determinism, §3.2, makes any difference a
  bug of the back end or of the boot oracle). **Stage 2** = link(IR₁) compiles again: IR₂ = IR₁, the fixpoint.
* **Diverse double compilation:** a sample of M ∪ N (and the tools themselves) is compiled once by stage 0 (machine G
  in Lean) and once natively; the outputs must agree. The two paths share no compiled code.
* After stage 2, Lean computes nothing more: every later run is a Gabbro binary.

**State of stage 0 (2026-10-25, `grammatik/Grammatik/Boot/`).** `gabbro-boot` exists as a Lean executable
(`lake build gabbro-boot`): `Boot.boot` runs the stages of `uebersetzeAllg`, refuses what `AkzeptiertX` refuses
(`akzeptiertU`), refuses the forms whose meaning is a machine answer (foreign bodies, registers, atomics) and the open
region (its provider is not yet fresh in the model: two `alloc T` in one world answer the same cell for every oracle),
builds the declared initial memory (`sp0Of`) and runs `main` with `rufAt`. There are no gates yet: input and output are
ordinary Gabbro, a table `io` with the fields `ein`/`aus` and the statics `ein_len`/`aus_len`. `boot_ist_maschine`:
every output is the end world of `rufAt` on the pipeline's program; witness `Boot/Zeuge.lean` (call, branch, narrowing,
loop; the kernel runs it). Measured: 0.55 s fixed cost, 4 KiB in 1.6 s, 16 KiB in 31 s -- quadratic, because a world
slot is a chain of closures. Before stage 0 can run `gkomp` on its own source it needs (a) a world with array-backed
slots, proved equal to the closure world, (b) the gates of the boot oracle over Lean `IO`, (c) the provider freshness
repair of the open region in the model.

## 3. What is proved, for each tool

For a tool `T`, `run_T x` is the output of its G program on input `x` (machine G, any oracle that meets the gates'
contracts).

### 3.1 Termination

∀ `x`, `run_T x` returns (never by budget exhaustion) within `passes ≤ c · |x|^k`. Every loop and recursion carries a
measure (`Logik/Terminierung/Mass`, `Klasse`); the bound is a theorem.

### 3.2 Determinism

* The output is a function of the input bytes: two oracles that agree at the input gates give the same output; output
  and exit gates return nothing the program branches on.
* **Address neutrality:** the provider may answer any fresh cell; the output is invariant under every renaming of
  region cells (no reference is ordered, hashed by address or printed) -- a noninterference statement over reference
  values (`Nichtinterferenz/`).
* The first versions are single-threaded (no `concurrent`). A parallel version later owes schedule independence: race
  freedom from `gabbro_ziel` plus deterministic joins.

### 3.3 Neutrality: H1-H7 of `CHECKER.md` §16.1 as theorems

Today H1-H8 are ASSUMPTIONS about the Rust code, checked by audit and metamorphic tests. For `gpruef` and `gkomp` they
are proved:

* **H1, syntax-directed with finite state:** the core of the tool is a fold `node : Ctor → List St → St` over the
  elaborated tree with a FINITE state type `St`. Theorem: an `Automat` (`Adaequanz/Baum.lean`) with `m = |St|` states
  computes the same as the tool on every tree; at the fine level, the tool is an instance of `NeutralF`
  (`Gen/Fein/Neutral.lean`: `pruefer_fein`, `compiler_fein`).
* **H2, names:** renaming identifiers renames the output's symbols and changes nothing else.
* **H3, data:** constants reach the control only through their range class, otherwise they are copied
  (noninterference with the class as the public part).
* **H4, order:** reordering independent items permutes the output's items.
* **H5** is §3.2. **H6** (bounded mark multiplicity) and **H7** (whole-program conditions are bounded patterns: a
  function's verdict and code depend on its body and the signatures it uses, `WRAP`) are theorems about the fold.
* **H8** (LLVM's passes, `llc`, `ld.lld`) stays outside: translation validation, `PLAN-TRANSLATION-VALIDATION.md` §9c.

### 3.4 Logic proofs where the test route does not reach

* **The checker, `gpruef`:** besides §3.1-§3.3, GabbroV proves the parts the test sets do not decide: the lexer and the
  parser against `lex`/`parseTopTief` (text-level behaviour, R), the elaborator against `elabU`, and the refusal
  REPORT (`NurAn c` of the refused cell). The ten components are written as the fold of §3.3, so their correctness
  comes from the test route, not from ten functional proofs.
* **The compiler, `gkomp`:** the IR printer and the symbol handling (outside the fold) are proved against their Lean
  counterparts.
* **The helpers:** `ggen` against the Lean generator (it emits exactly M, N, R with the right labels: soundness and
  completeness by exact size), `gabdeck` against the cell functions, `gvalid` against the `Code/Refine` decision, `glauf`
  against the comparison predicates. These are functional GabbroV proofs; the helpers are small and loop over data, so
  the proofs are simulations, one per function.

## 4. Correct on every program: M, N and the adequacy theorem

* **Coverage first:** M ∪ N must cover every cell (`deckung`): today 459 component cells and 4267 fine cells, 876 fine
  cells open since the search of 2026-10-23 (`CHECKER.md` §16.8). `gabdeck` closes them by witnesses, or a Lean theorem
  proves a cell unreachable.
* **The campaign:** `glauf` runs `gpruef` on every program of M ∪ N (label: accept, or refuse by exactly `c`) and of R
  (refuse at the text level), and `gkomp` on every program of M with `gvalid` on the result; it writes a ledger.
* **The theorems:**
  * `gpruef_korrekt`: ∀ `src`, `run_gpruef src = pruefSpec src` -- from §3.1-§3.4 and `hinlaenglich` (`CHECKER.md` §16.2)
    over the agreement on M ∪ N, plus the GabbroV proofs for R.
  * `gkomp_korrekt`: ∀ `p` with `AkzeptiertX p`, `run_gkomp (print p)` refines `kompSpec p` -- from §3.1-§3.4 and
    `hinlaenglich` over the agreement on M; with H8, the binary refines the model.
* **Where the computation enters the proof.** The agreement on M ∪ N is a COMPUTED fact: the verified `glauf` ran on a
  native binary. It enters the theorems as the named premise *campaign*, with the ledger as its record. It is not
  circular in the dangerous way: the campaign's binaries are produced by the fixpoint compiler, and the diverse double
  compilation of §2 re-runs a sample on machine G in Lean. Where a kernel-sized certificate exists for a test (the
  verdict of a small program), the premise is replaced by a kernel check. `native_decide` stays forbidden in
  `grammatik/`.

## 5. What the language needs first (Lean model first)

The tools read inputs of unbounded size; each need is modelled in Lean before it is used (CLAUDE.md):

| Need | State |
|---|---|
| storage without a ceiling: `table T from p`, `alloc T`, references, their ownership rule, the refinement to `ArenaStorage.Heap` | done in the Lean model and its Lean front end (`PLAN-DYNAMIC.md` §14) |
| release of region cells (a provider-side `free`, grants for references) | open |
| bounded strings `string max N` and byte buffers in G | strings exist outside G |
| file IO as declared `syscall` gates with contracts (open, read, write, exit) | gates exist; contracts to write |
| loops and recursion over input-sized data with a measure accepted by the checker | model exists; checker side to extend |
| containers as Gabbro libraries over the open region (vector, hash map, tree), with GabbroV contracts | open |
| no generics: one container instance per element type, produced by a Gabbro generator (not a macro in the language) | by design |

## 6. What is deleted

* At parity of `gpruef`/`gkomp` with the Rust checker and compiler on M ∪ N ∪ R and the corpus: the Rust checker, the
  Rust compiler and their tests. The guardians `pruefe-pruefer.py` and `pruefe-llvm.py` then measure the Gabbro tools.
* At parity of `ggen`/`gabdeck`/`gvalid` with the Lean drivers: the Lean drivers (`gen-abdeckung`, `gen-zellen`,
  `gen-fein`, the executable pipeline and validator). The Lean DEFINITIONS stay: they are the specifications.

## 7. Targets: a new ISA is a profile, not a port (Simon, 2026-10-25)

**Requirement:** moving the tools and their output to another 64-bit ISA is easy: a target is a checked profile plus a
binding library, never a change of the front end, the checker or the compiler's core. **Built:** x86-64 and AArch64
(AArch64 hardware is available, Simon 2026-10-25). **Kept easy, not built:** RISC-V -- the design must make it items 1-4
below and nothing else; no RISC-V profile, binding, proof or measurement belongs to this plan's deliverables.

* **One target-independent core.** `gpruef` knows no ISA at all. `gkomp` lowers to target-independent LLVM IR; the ISA
  enters only through the **target profile** `Ziel`, a Gabbro data item: triple, data layout, calling convention and
  aggregate ABI, the register and stack conventions of `entry`/`asm` stubs, the width classes of atomics, and the
  mapping of `acquire`/`release`/`seq`/fences to the target's memory model.
* **What is per target, and only that:**
  1. the profile `Ziel` (data);
  2. the binding library of the environment (syscall numbers, entry stubs) -- Gabbro code with user-logic contracts,
     never in the compiler (AGENTS.md §3: the OS is user logic);
  3. the memory-model mapping of the profile, proved in Lean against the target's model (AArch64: `ARM-PLAN.md`;
     x86-64 TSO is frozen; a later RISC-V owes RVWMO modelled the same way);
  4. a QEMU stage in `pruefe-llvm.py` and, for performance (§8), real hardware.
* **Theorem `ziel_neutral`:** `run_gkomp (p, z)` = `abi z (kern p)`: the output is the target-independent core `kern p`
  followed by a function of the profile alone; the core never reads the profile. So the proofs of §3 and §4 are made
  ONCE and hold for every profile; a new target owes only items 1-4.
* **Measure of "easy":** a new 64-bit target with an existing LLVM back end is items 1-4; the gate is the four guardians
  plus the QEMU stage on the new target. Estimate (a guess): days for 1, 2 and 4; the memory-model proof (3) is the
  long item, and it is shared by every program.
* **Hardware model and translation validation** (H8, `PLAN-TRANSLATION-VALIDATION.md` §9c) stay per ISA; `Code` is
  ISA-neutral by design (§9a there), so a new ISA adds its CPU model, not a new IR.

## 8. Performance: at least `gcc -O3` and `clang -O3` (Simon, 2026-10-25)

**Requirement:** the code `gkomp` produces is at least as fast as equivalent C compiled with `gcc -O3` or `clang -O3`,
on x86-64 and AArch64 (both measured on real hardware). This raises the minimum of AGENTS.md §11 (80 %) to 100 %. A
later RISC-V target owes the same minimum when it is built.

* **Score:** per workload `100 · t_C / t_Gabbro` (fixed work) or `100 · throughput_Gabbro / throughput_C`, against the
  FASTER of `gcc -O3` and `clang -O3` (same machine, same ISA extensions, `-march`/`-mcpu` matched, same semantics,
  no `-ffast-math` on either side). **Minimum 100 % on every workload class; ambitious above 110 %.**
* **Why it is reachable:** `gkomp` hands LLVM's `-O3` pipeline IR that carries what the proofs know and C cannot say:
  * no bounds checks, no overflow checks where M1 proves the range (they are not emitted, not optimised away);
  * `!range` from every integer type's bounds, `nsw`/`nuw` where the range proves no wrap, `inbounds` GEPs;
  * `noalias` from ownership (`own`, the ledger) and from distinct carriers, `!tbaa`-style disjointness per table and
    field, `nonnull`/`dereferenceable` for references into regions;
  * loop trip counts from the loop bounds, `llvm.assume` from narrowed facts;
  * the open region's allocator: a bump/free-list fast path inline, the provider called per chunk, not per cell (OOM is
    user logic, so no refusal path on the fast path);
  * whole-program optimisation across units (LTO) where linking allows (`GabbroZielVerbund`).
  Every such fact is justified by a proof and checked by translation validation (`PLAN-TRANSLATION-VALIDATION.md` §8,
  §8.6): a validated optimised image or a refusal, never "optimised but unchecked".
* **Measurement:** a benchmark suite of workload classes (compute kernels, pointer-chasing over regions, parsing and
  string work, the tools themselves as a workload); each Gabbro program beside a C version written to the same
  algorithm; a performance stage in `pruefe-llvm.py` (no fifth guardian) that records the scores per ISA and fails below
  100 %. x86-64 runs here, AArch64 on the available AArch64 machine (QEMU timings are no measurement).
* **The compiler itself** is a Gabbro program compiled by itself at `-O3`, so its own speed follows the same requirement;
  compile latency (checking, optimisation, validation) is measured beside it.

## 9. Order of work, estimates, critical path

| | Step | Gate |
|---|---|---|
| S1 | the language needs of §5 in the Lean model | full Lean build, `gabbro_ziel` on the standard axioms |
| S2 | `gabbro-boot` (machine G in Lean with the IO oracle; `GutO` of the oracle proved) | a probe program's run equals its Lean semantics |
| S3 | libraries in Gabbro (bytes, strings, vector, hash map over the open region), GabbroV contracts | GabbroV GREEN |
| S4 | the shared front end in Gabbro, proved against `lex`/`parseTopTief`/`elabU` | kernel |
| S5 | `ggen` and `gabdeck` in Gabbro, proved against the Lean generator and cells; the open cells closed | kernel; coverage complete |
| S6 | `gpruef` (the fold) with §3.1-§3.3, the campaign on M ∪ N ∪ R, `gpruef_korrekt` | kernel + ledger |
| S7 | `gkomp` and `gvalid` with §3.1-§3.4, bootstrap S0 → S1 → S2, fixpoint, double compilation, `gkomp_korrekt` | kernel + fixpoint + ledger |
| S8 | deletions of §6 | the four guardians on the Gabbro tools |
| S9 | targets (§7): the profile `Ziel` and `ziel_neutral`; the x86-64 and AArch64 profiles, bindings, memory-model proofs; the RISC-V path checked as "profile only" by a design review, not built | QEMU and hardware stage on AArch64 |
| S10 | performance (§8): the proof-derived IR facts, the benchmark suite, the performance stage | 100 % of the faster of `gcc -O3`/`clang -O3` per workload class, on x86-64 and AArch64 |

**New lines of code (ranges, a guess; measured bases 2026-10-25 in brackets).** Gabbro is denser in ceremony than Rust
(contracts, effects, costs, no generics: one instance per element type), so a Gabbro tool is costed at 1.5-2.5x its
Rust counterpart and 2-3x its Lean definition.

| Part | Base today | New lines |
|---|---|---|
| **Gabbro, written by hand** | | |
| libraries: bytes, strings, vector, hash map, tree, file IO, formatting | -- | 8 000-15 000 |
| shared front end: lexer, parser | Rust syntax 11 200; Lean parser without proofs ≈ 8 100 | 15 000-30 000 |
| shared front end: elaborator to G | Lean `Elab` 10 200 | 15 000-35 000 |
| `gpruef`: the ten components of `AkzeptiertX` as a fold, refusal reports | Rust checker 110 900 (with diagnostics, passes, tools) | 20 000-45 000 |
| `gkomp`: lowering, IR facts of §8, IR printer, profile handling | Rust LLVM 12 900; Lean `Code` 17 900 | 20 000-45 000 |
| `ggen`, `gabdeck`, `glauf`, `gvalid` | Lean `Gen` 22 000 (with proofs) | 24 000-48 000 |
| target profiles and bindings: x86-64, AArch64 | -- | 2 500-6 000 |
| benchmark suite: Gabbro side | -- | 8 000-20 000 |
| **Gabbro total** | | **112 000-244 000** |
| generated container instances (not written by hand) | -- | 10 000-30 000 |
| **Lean, specification and proof** | | |
| language needs of §5 (region release, strings in G, file-gate contracts, measure-based loops) | region in G ≈ 5 000 | 8 000-20 000 |
| `gabbro-boot`, IO oracle, its `GutO` | -- | 1 500-4 000 |
| GabbroV: libraries' contracts | GabbroV today 115 000 | 8 000-20 000 |
| GabbroV: front end against `lex`/`parseTopTief`/`elabU` | | 30 000-70 000 |
| GabbroV: helpers, IR printer, refusal reports | | 15 000-35 000 |
| §3.1-§3.3: termination, determinism (address neutrality), neutrality H1-H7, the fold as `Automat` | Nichtinterferenz 4 300, Terminierung 2 400, Adaequanz 1 600 | 15 000-40 000 |
| §7: `ziel_neutral`, profile semantics, AArch64 memory-model mapping | `ARM-PLAN.md` parts | 7 000-20 000 |
| §8: soundness of the IR facts (ranges, `nsw`/`nuw`, `noalias`, disjointness) in translation validation | | 8 000-20 000 |
| closing the open cells (witness support, unreachability proofs) | 876 fine cells open | 3 000-10 000 |
| **Lean total** | | **96 000-239 000** |
| **Other:** C side of the benchmark suite | -- | 5 000-12 000 |
| guardian stages (performance, AArch64 hardware), scripts | -- | 500-1 500 |
| **All new lines** | | **≈ 210 000-490 000** |
| **Deleted at parity (§6)** | Rust checker, compiler, syntax ≈ 122 000 plus their tests; Lean drivers 3 000-6 000 | |

The ranges are wide because the two largest items -- the front end's GabbroV proof and the neutrality theorems -- have
no precedent in the tree; the low ends assume the fold structure of §3.3 removes most of the per-component proofs.

**Critical path:** S1 → S3 → S4 → S6. The least charted parts are §3.3 (neutrality as theorems), above all H1 for a
real implementation, and the AArch64 memory-model mapping of §7. The performance minimum (§8) is decided by the IR facts:
they must be designed into `gkomp` from S7 on, not added afterwards.

## 10. Decisions (Simon, 2026-10-25)

All decided:
1. The premise *campaign* (§4) is accepted: the agreement on M ∪ N, computed by the verified `glauf` on the native
   binary, enters the correctness theorems as a named premise; where a kernel certificate fits, it replaces the premise.
2. The first `gpruef`/`gkomp` are single-threaded.
3. The Rust tools and the Lean drivers are deleted at parity (§6).
4. AArch64 hardware is available: x86-64 and AArch64 are built and measured; RISC-V only stays easy to add (§7).

First step (Simon, 2026-10-25): complete GabbroV so that full logic proofs of Gabbro programs are possible -- it is what
§3.4 and §4 rest on.
