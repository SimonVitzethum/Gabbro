# AGENTS.md — how work on Gabbro is run

This is the operating manual for everyone who works in this repository, human or model. `CLAUDE.md` holds the
working rules that are loaded into every session; this file states the goal, the standing rules, the procedures
and the pitfalls. The current work list is `TODO.md`. History (who decided what, when, and how earlier rounds
were organised) is in `git log`, not here.

---

## 1. The goal

> **A Gabbro user proves only their own logic plus named hardware assumptions.** Memory safety, race freedom,
> contracts where claimed — in concurrent runs too — and time are carried by the language.

The end sequence:

1. **The goal theorem** over the Lean model (`gabbro_ziel`, §2) — proved.
2. **Transfer into the checker and the compiler**: everything the model proves becomes the Rust checker
   (`crates/gabbro-check`) and the compiler, in the order of §3 (Lean model first).
3. **Translation validation**: source → model → final machine bytes, checked in Lean, with W / GX reused for
   concurrency.

**Acceptance of a change to the model** (also a change of the goal statement): the full Lean build is green and
the core theorems are proved — `gabbro_ziel` with exactly `propext`, `Classical.choice`, `Quot.sound`, no
`sorry`, and the witnesses of the new theorems. A change that moves the meaning of `Spec.lean` is described in
the commit and in the relevant plan section.

**What may be said:** "The goal theorem is proved over the model, with a witness and non-degeneracy."
**What may NOT be said:** "Gabbro is verified." The checker inside the statement is the Lean Bool `Akzeptiert`,
not the Rust checker, and no bridge to any binary is built. The
[proof-status section](README.md#5-proved-and-not-proved) says exactly this; keep it that way.

## 2. The goal theorem — what a newcomer must know

- **Shape:**
  ```
  ∀ checker C, declaration D, unit E : Einheit D, enumerations …,
    C.akzeptiert E … = true      (a) the checker Bool, components in Zielsatz/Akzeptiert.lean
    → NutzerPflicht E            (b) user logic: LogikPflicht + StartPflicht, for every budget
    → HardwareAnnahmen O E.Q     (c) named hardware assumptions (oracle O answers the axiom ensures Q)
    → Laufzeit E sp init         (d) the runtime: declared starts, idle root (P.mitRuhe)
    → every reachable machine M satisfies Ziel
  ```
- **What `Ziel` contains:**
  - `SpurInv`;
  - `RennfreiBis` (every carrier except atomics);
  - `VertragAmOrtG`, `SperrInvG`, `InvAmOrtG`, `InvAmGrundG`;
  - `InvRuheG`, `InvSichtG`, `SperrWechselG`, `SperrSichtG`: invariants beyond the returns — wherever no writer
    runs, at every lock move, and observed by the holder alone;
  - `StartEndeG`, `KeinStartGrundG`, `KeinLogikHaltG`;
  - no deadlock, `KeinWarteZyklus`, and `KernHaltE`: no same-core interrupt deadlock for the handlers the
    program declares (`Programm.unterbricht`, `via idt`), under a named core schedule, for every core assignment;
  - `FortschrittG`, whose stop kinds are hardware, flag, budget and `nieZurueck`;
  - `ZeitAb`;
  - `FolgeG`: the order of calls in every thread's call log;
  - `speicherAdressen`: every cell a run changes lies in its extent and, under every correct layout, in the
    region of its table (addresses are pairs (space, byte); an open region has a space of its own).
- **The atomic rely:** (a) is a `PrueferX` (sound against `AkzeptiertSpecX`; the footprint rule admits a shared
  atomic in no contract; concrete checker `akzeptiertX_pruefer`), (b) is `NutzerPflichtA` (every body against
  every value a shared atomic read may return), and the conclusion is `ZielFX`/`ZielX` on the thread machine over
  GX (G whose shared-atomic reads the weak memory answers). The sequentially consistent statement is
  `GabbroZielSC`, derived by `gabbro_ziel_sc_aus`. Proof files: `Zielsatz/Atomar/BeweisAtomar.lean`
  (`gabbro_ziel`), `Zielsatz/Kern/Beweis.lean` (`gabbro_ziel_sc`).
- **Axioms:** `#print axioms gabbro_ziel` must be exactly `propext`, `Classical.choice`, `Quot.sound`. Every
  change that touches `grammatik/` keeps it so.
- **The header of `Spec.lean`** is the ONE list of named assumptions and the NOT CLAIMED list: termination and
  waiting bounds, stack depth, the hardware, weak memory beyond DRF-SC, unguarded publish/await payloads, floats
  beyond the kernel IEEE model, starvation freedom, invariants inside a running writer or a held section, a start
  declared once running on several threads. Linking of separately compiled units is a second statement,
  `GabbroZielVerbund`. Probabilistic statements are out of scope. Every extension of the goal is a diff of
  `Spec.lean` (or of the definitions it uses) and is described as such.

## 3. Standing rules

**Language and model**
- **The Lean model is the single source for language and syntax.** Any change to a construct, a clause, a type
  rule or a rule that accepts or refuses a form goes into the Lean model FIRST (machine G, `Akzeptiert`,
  `gabbro_ziel` on the standard axioms), then into the checker, the compiler and `SYNTAX.md`/`LANGUAGE.md`. A form
  the checker accepts and the model lacks is a checker bug. A pure lowering of an existing form does not change
  the language.
- **Everything new is modelled in Lean before it is merged**: semantics in machine G, the checker side with
  `gabbro_ziel` still proved, the front end and exporter, GabbroV's `Body` model with the bridge simulation, and
  for the selected target the correspondence through the final machine bytes. Without its Lean part a feature
  stays unmerged (`NEEDS LEAN`).
- **Guarantees come from generic theorems only.** Nothing in the compiler, checker or printers exists for
  particular programs; GabbroV is proved right for every program, with its statements computed in Lean from the
  source. Per-program Lean files are witnesses only, off the trust path.
- **Safety is never traded for features.** No change weakens a guarantee — memory safety, race freedom,
  contracts, costs, lock discipline — to make a check go green. A wall that only yields by weakening is recorded
  as a finding.
- **Simplicity without losing a guarantee** (`dokumente/CHECKER.md`): ceremony count down AND pass register
  constant. Never derive `ensures`, never turn a refusal into a warning.
- **Where the model has no rule yet, refuse** — never accept by default.

**Compiler, checker, parser**
- **No legacy**: only the newest state. What is replaced is deleted (history stays in git): no compatibility
  layers, deprecated paths, old names or flag aliases, retired-but-kept codes.
- **LLVM is the only backend** (`llvm.rs`, `llvm/`); `gabbro build` drives it (checker, IR, `opt`, `llc`,
  `ld.lld`). A form LLVM cannot lower is refused by name (`Y1xx`). The removed C emitter is in the tag
  `archiv/c-emitter-2026-10-17`.
- **Target direction: AArch64** (Armv9-A) on the Sail Arm model, with the multicore memory model added in Lean
  (`ARM-PLAN.md`). The x86-64 hardware model is archived (branch `archive`); the one exception is the verified
  stage-0 runner (`PLAN-SELF-HOSTING.md` §2.2, Simon 2026-10-28), which revives the x86-64 instruction subset it uses.
- **Target portability**: source semantics, IR, optimisation and validation stay generic; ABI, image and entry
  requirements are described in checked profiles; environment services are Gabbro bindings with user-logic proof
  obligations. No implicit Linux/POSIX/libc/ELF dependency; freestanding has no mandatory host runtime.
- **Vendor neutrality**: the hardware model holds on all CPUs of an architecture. What a vendor calls undefined or
  model-specific stays FREE (all allowed results, never one observed value).
- **Optimisations** follow `dokumente/PLAN-TRANSLATION-VALIDATION.md` §8 (including §8.6, the techniques taken
  over from Goose): a validated optimised image or a refusal, never "optimised but unchecked".

**Operating system, memory, data**
- **The operating system is user logic, never an assumption, and nothing is OS-specific.** A system or kernel
  call is a generic call whose contract the program or its binding library declares in Gabbro. Only hardware
  behaviour is a named assumption.
- **No handwritten C in a finished Gabbro binary, as far as possible.** Runtimes and binding libraries are
  written in Gabbro; OS access goes through Gabbro `syscall` items; hardware access through Gabbro's
  register/port forms. Handwritten C or assembly stays only where Gabbro cannot express the thing, each piece
  with its written reason, booked as a wall and counted. Code moved from C into Gabbro is checked like user code.
- **Memory from outside comes as a REGION, never from a number.** A `syscall`/`extern` item may answer a region
  (or a reference into one) whose contract says it is fresh and disjoint; no int→ptr or int→fn-ptr conversion.
- **Dynamic data structures are in scope**: heap regions with a declared ceiling and refuse-on-full (the
  default), and OPEN regions without a ceiling (`Deklaration.offen`, PLAN-DYNAMIC 14) whose cells come only from
  the program's provider. **OOM is user logic**: an allocation needs no source OOM path; that the provider has
  memory to give is the program's own obligation. An arena's `else` at its declared ceiling is a capacity bound,
  not OOM.
- **Floats are in scope** (IEEE kernel model). Probabilistic statements are out of scope.

**Lean layout**
- Every folder holds at most **20 entries**, and every Lean file lives in a sensible folder. The placement rules
  are `instrumente/teile/lean-layout-rules.py`; `python3 instrumente/teile/lean-layout.py --check` runs inside
  the Lean guardian, `--apply` moves new modules into place and rewrites imports.

**Repository**
- **Language:** everything in the repository is English — documents (every `.md` and its file name), comments,
  commit messages, diagnostics, `TODO.md`. The conversation with the project owner is in German.
- **At most 30 `.md` files** in the repository. Reports, verdicts and interim states belong in git, not in the
  tree.
- **Commit messages** only through `arbeitsprotokoll/.commitmsg` + `./commit.sh`, which commits STAGED changes
  only (`git add` first).
- **Commit every building step.** Work that builds is committed at once.
- **Caprock** (the OS this language exists for) lies read-only in `../caprock-messbasis`: never commit into it.
- **Tag milestones** at the push that reaches them.

**Security**
- Never write API keys or passwords into the repository, memory or logs.
- When the permission classifier blocks something, do not work around it; ask.

## 4. Where things run

Everything runs locally, in this checkout or in worktrees beside it: Lean builds, `cargo` runs, acceptance
runs and QEMU stages. There is no build server and no `ssh` step.

- **GitHub:** push is `git@github.com:SimonVitzethum/Gabbro.git` with key `~/.ssh/id_ed25519_github`; fetch
  goes over https.
- **One heavy run at a time per tree**, with `free -g` beside it. Heavy are `cargo build`, `cargo test`,
  `lake build` and the acceptance run. Every heavy run goes under a memory scope (`systemd-run --user --scope -p
  MemoryHigh=… -p MemoryMax=… -p MemorySwapMax=0`); the soft limit lets the kernel reclaim before the hard limit
  kills. An abort for lack of memory is not a finding.
- **`cargo test` and a Lean run must not run at the same time in ONE tree:** `cargo test` calls `gabbro prove`,
  which rebuilds with `lake` and replaces `.olean` files that running `lean` processes read.
- `rustc`/`cargo` live in `~/.cargo/bin`; Lean through `elan` (`ELAN_TOOLCHAIN` must not be set).

## 5. Procedure: branch, build, merge, push

- **Large changes run on a branch in a worktree beside the checkout** (`git worktree add -b NAME ../dir
  master`), with the warm `grammatik/.lake` copied in, so that master stays buildable for everyone else. Build,
  commit there; merge when the acceptance of §1 holds.
- **After every merge:** build `grammatik/` (also after a clean merge: a new structure field or a changed arity
  only shows in the build), run the layout check, then the guardians.
- **The push gate is the four guardians** (`./instrumente/abnahme.py`):

  | Guardian | Subject | What it checks |
  |---|---|---|
  | `instrumente/pruefe-lean.py` | the Lean model and stage 0 (`stage0/`) | `lake build` of both, `gabbro_ziel` on the standard axioms only, no `sorry`/`admit`/`native_decide`/`axiom`, layout |
  | `instrumente/pruefe-llvm.py` | the LLVM compiler | `cargo test --test llvm`, the reference programs as binaries on x86_64 and aarch64 with the same result |
  | `instrumente/pruefe-pruefer.py` | the Rust checker | `cargo test --workspace --no-fail-fast`, sentence register, identifiers assigned once |
  | `instrumente/pruefe-gabbrov.py` | GabbroV | `lake build`, proofs without `sorry`, `gabbro prove` GREEN, no GREEN without Lean |

  Exit code `0` measured and green, `1` measured and red, `2` nothing or not everything measured — that is not a
  green. A fifth guardian is not built: a new check becomes a test in `cargo test`, a Lean theorem, or a stage
  in one of the four.
- **Push master after checked merges**, without asking: first grep the outgoing diff for keys; never push red;
  never force-push; if origin moved, merge first and check again. No new branches on GitHub.
- **Delete worktrees and clones right after their merge.**

## 6. Parallel work

- **Every parallel worker (another session, a subagent) gets its OWN worktree** and scratch directory, never
  this checkout; its tree is on `master` before it starts. Two runs in one tree measure a mixture.
- Copy both `grammatik/.lake` and `programmlogik/.lake` (warm, Mathlib) into a new tree; with no cache
  `gabbro prove` goes off to clone Mathlib and hangs; a stale `.lake` is worse than none.
- Before starting work in an area, check whether another session already works there (worktrees, recent file
  times) and do not duplicate it.
- Reviews and assessments are done directly, not delegated.

## 7. Number ranges and counters (free from here)

| Kind | Next free |
|---|---|
| Diagnostic codes | **N594** (N459, N460, N295 and N297 are retired and not reused). Alias rules: next `R016` |
| Gift (poison-probe) numbers | **1488** (1448-1469 stay unused; 1149, 1150, 956, 957 and 958 retired) |
| Example numbers | **1172** |

Re-measure instead of trusting this table: `grep -rho '\bN[0-9]\{3\}\b' crates/ | sort -u | tail`,
`ls beispiele beispiele/gift | tail`. The highest number in the tree does not drift; a ledger does.

- Next free is always above the highest number in use.
- The test `keine_zwei_korpusdateien_teilen_eine_nummer` catches collisions.
- **Every new refusal code comes with its sentence** in `saetze.rs` in the same commit (the sentence register
  in `pruefe-pruefer.py`), and with a poison probe.

## 8. Files that matter

| What | Where |
|---|---|
| The goal statement | `grammatik/Grammatik/Zielsatz/Kern/Spec.lean`, `Beweis.lean`, `Akzeptiert.lean`, `Proben*.lean`, `SpecProben.lean`; `Zielsatz/Atomar/BeweisAtomar.lean` |
| Model | `Kern/` (syntax, machine G, semantics), `Nebenlaeufigkeit/`, `Speichermodell/`, `Logik/`, `Bausteine/` (arenas, regions, ownership, floats) |
| Code model and lowering | `grammatik/Grammatik/Code/` (`Model`, `Lower`, `Refine`, `Conc`, `Gate`) |
| Test sets M and N | `grammatik/Grammatik/Gen/` (generator, coverage cells, fine cells), runs under `messung/fein/`, driver `instrumente/fein-suche.sh` |
| Plans | `dokumente/PROOF.md`, `dokumente/PLAN-TRANSLATION-VALIDATION.md`, `dokumente/PLAN-DYNAMIC.md`, `dokumente/CHECKER.md`, `ARM-PLAN.md`, `FLOATING-POINT.md` |
| Theorem map | `dokumente/THEOREM-MAP.md` (new sections at the end) |
| Known absences | `TODO.md` |
| Guardians | `instrumente/abnahme.py` and the four `instrumente/pruefe-*.py` (`dokumente/TOOLBOX.md`) |
| Rust tools | `gabbro lean-g` (exporter), `gabbro obligations --g`, `gabbro counterexample`, `gabbro certificate`, `gabbro pruefe --fix`, `gabbro abgeleitet`, `gabbro zeremonie`, `gabbro paesse` |

## 9. Pitfalls that cost real time (each happened)

**Tools**
- **`rsync -a` + `cargo` build a mixture**, because `cargo` trusts mtimes. Copy trees that cargo builds with
  `-rlpgoD`.
- **`pgrep -f` / `pkill -f` match their own command line.** Kill by PID; wait by polling a file or `ps -C`.
- **A guardian that aborts reads like one that passed.** Look for the numbers it no longer prints; measure the
  base in a throwaway worktree before guessing. `cargo test` always with `--no-fail-fast` (also `set -e` in
  scripts stops counting at the first hit).
- **Mechanical edits over many files:** a regex that matches a pattern alternative can strip its prefix or
  indentation; patterns with non-ASCII characters (`t₂`, `σ`) need a UTF-8 aware tool. Rebuild after every
  mechanical edit and read what it changed.

**Merging**
- Recurring conflicts: `Grammatik.lean` imports (take the union); duplicate THEOREM-MAP section numbers
  (renumber); two branches defining the same Lean name (rename one); duplicate sentence insertions in
  `saetze.rs` (keep both).
- **Semantic merge breaks** show up only in the build: a new structure field needs its value at every
  positional literal; an arity change needs every caller updated. Always build after a merge.
- **A new constructor of `Expr` or `Stmt`** belongs at the END of its inductive: the fine cells and the generator
  number constructors by position, and the cached runs keep their names only then. Recursors of auxiliary
  inductives (`StmtOhneRuf`, `BlattG`, …) take their premises in THEIR constructor order.
- **Sorry is mechanically refused**: the Lean guardian fails on `sorry`/`admit`/`native_decide`/`sorryAx`/`unsafe`
  in `grammatik/` and on any `axiom` not in `instrumente/teile/kein-sorry-allowlist.txt`.

**Machines**
- **A leaked `ELAN_TOOLCHAIN` rebuilds everything under the wrong Lean.** After a toolchain incident replace a
  poisoned `.lake` with the warm master cache.
- **Low memory kills jobs silently**, and there is no swap. Twenty parallel `lean` processes of a full rebuild
  exceed a 15 GB hard scope; use a soft limit (`MemoryHigh`) under the hard one.
- **`/tmp` is RAM.** Work in real folders; scratch files go to a scratch directory inside the tree that is not
  committed, and are deleted after use.

## 10. Talking to the project owner

- **German, direct, concrete.** Say what was done, what is open and what is uncertain. Never claim more than was
  measured.
- **Estimates:** give ranges and name the critical path.
- The owner follows from other devices: short status lines while long jobs run are welcome.
- A decision that is the owner's (a change of the goal statement's meaning, a rule of the language) is asked,
  with a recommendation; everything else is decided by the strongest variant (maximum safety and power,
  effort is no argument).

## 11. Direct compiler: goals that still stand

The hardware model and the full Gabbro-to-final-binary pipeline are completed in Lean without a persistent SSA
IR or a second source interpreter: the typed source plus checked target blocks and bytes, recomputed
certificates, and Rust producing untrusted candidates that a Lean validator checks (source-derived unit, all
reachable support, entry and binding bytes, linking and relocation, the final mapping). Source safety, G/GX
concurrency, IEEE, contracts, call logs and budget guarantees remain; OS and freestanding profiles stay generic.

Performance against equivalent C built with `gcc -O3` or `clang -O3` (the faster of the two): minimum 100 % on every workload
class and ISA (Simon, 2026-10-25; was 80 %), ambitious above 110 %.
Fixed-work score `100 * Ctime / Gabbrotime`, throughput score `100 * Gabbrothroughput / Cthroughput`, per
workload and class, on full validated direct binaries with matched hardware, ISA, semantics and settings.
Compile latency includes checking, optimisation, production, validation and Lean kernel checking. Targets are
OPEN until measured; no universal speed claim. Central record: `dokumente/PLAN-TRANSLATION-VALIDATION.md`.

## 12. Working with Lean here

- **Toolchain truth, not training memory.** `grammatik/` pins Lean v4.35.0 with Mathlib at the matching tag;
  `split` (never `split_ifs`); `omega`/`decide`/`simp` available. Mathlib is allowed everywhere; `gabbro_ziel`
  stays on the standard axioms (Mathlib adds none).
- **Names are read, not guessed.** Every lemma name is grepped from the tree or the toolchain before use;
  `unknown identifier` means a wrong name. Canonical definitions are reused, never duplicated.
- **Witnesses:** every theorem with a ∀-over-syntax premise gets a `_zeuge` on a non-degenerate fixture that
  satisfies all premises jointly.
- **Silicon over proof shape.** A green proof of a wrong hardware definition is a finding, not a result.
- **Commit the green skeleton early**, one definition per check, and never stop with work pending.
