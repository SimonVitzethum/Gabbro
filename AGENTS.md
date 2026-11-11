# AGENTS.md — how work on Gabbro is run

This is the operating manual for everyone who works in this repository, human or model (`CLAUDE.md` is a
symlink to it, so Claude Code loads the same text); it states the goal, the standing rules, the procedures and
the pitfalls. There is no work-list file in the repository (owner, 2026-11-11): open work and findings are not
recorded in a tracked document; a lead keeps them in a gitignored scratch file. History (who decided what, when, and how earlier rounds
were organised) is in `git log`, not here.

---

## Current work: Stage 0 and the C packages (state of 2026-11-02)

This section is the ONE valid staffing and build order; it replaces every earlier one (earlier orders are in
`git log`). Lane checkpoints, the fourteen work packages and the C-package designs are in
[IR-COMPILATION-LANES.md](dokumente/IR-COMPILATION-LANES.md); staffing statements there are history, not orders.
The Lean module-system migration and the split of every Lean file below 500 lines are merged (2026-11-02).

### Team

- **One lead** (the root session) runs the C packages and Stage 0 with **four GPT Sol 6.1** (codex `gpt-6.1-sol`),
  **four Muse** (OpenCode Muse Spark 1.3 Contributor, only through the Go access: model
  `opencode-go/muse-spark-1.3-contributor`; never `opencode/…`) and **any number of Mercury 3** (opencode
  `inception/mercury-3`, limited only by API rate limits), all started through T3 `delegate_task`. Sol and Muse
  slots are occupied at all times: when an agent finishes, its branch goes into the integration branch and it gets
  its next task at once.
  - **Muse** takes proof and design work, also hard tasks.
  - **Sol** takes mechanical migrations with exact grep targets, one coherent migration per task ("do not stop
    after preparation"); it tends to give up on open-ended proofs.
  - **Mercury** takes only very light tasks: lint and layout passes, splitting a file that nears the size limit,
    small mechanical edits.
- **Work** is the C packages in their three rounds (Scope below) and the Stage-0 side (`stage0/`, the runner,
  probes): the IR lanes and the Stage-0 lowering of every form the C packages add.
- **Only the lead builds.** Sub-agents and their sub-agents never build or check Lean, and their worktrees carry no
  `.lake` (no Mathlib, no build cache). A lead checks its sub-agents' work in its own tree.
- **One integration branch.** The lead merges the branches of all its agents and its own work
  into ONE integration branch and builds/checks that branch only; never one build per agent.
- **No `.py` helper scripts for agents**: none are written, kept or used. Agents work with git, `lake`, `lean` and
  the shell. The two guardians stay root's tools.
- Root owns form-based coverage measurement and reviews; agents implement.

### Scope: every userspace Gabbro form to Stage-0 IR

The active implementation task is to compile every existing Gabbro language form needed by userspace
programs into Stage-0 IR and build the connected translation pipeline, formally verified, **and, from 2026-11-03
(owner), to implement [LOW-LEVEL-SYNTAX-PLAN.md](dokumente/LOW-LEVEL-SYNTAX-PLAN.md) completely**: source ASM bodies,
boot code, privileged instructions, address/context/view types with the raw-address syntax, device-register
reads/writes/fallible reads/register transitions, and the proof boundary of that plan (ASM/boot behaviour is user
logic with explicit proof obligations, never silently a hardware assumption). The low-level work starts only AFTER the C packages are finished and does NOT touch the assembly IR runner or Stage 0
(owner, 2026-11-03): its scope is the Lean model, checker and parser/exporter. It follows the plan's
own order (canonical Lean model first, then generic refinement and bridge, then parser/exporter/checker/lowering);
the recommended answers to its four owner questions are approved, EXCEPT that the proposed diff of `Spec.lean`
(question 2: splitting the software foreign assumptions into user obligations) is shown to the owner before it is
merged. Hard rules of that work (owner, 2026-11-03): there is NO `unsafe` anywhere (all low-level access is checked
authority); boot code is user code, written in Gabbro and verified by the user under the generic theorems; the one
exception is the x86-64 target binding, which offers a bundled, once-proved boot-stub ASM item (16→32→64-bit mode
switch, Gabbro cannot express it) that the user includes by name; it is a checked target binding with a generic
contract, not per-program compiler logic. Existing safe region/reference userspace memory stays in scope as before.
Work is prioritized by completed, connected source-to-IR cases, not by the number of helper lemmas, commits or added
lines. Cover the whole language rather than repeatedly expanding infrastructure for a small subset.

- **The assembly IR runner is the execution backend.** Reuse it; change it only for a concrete missing or
  incorrect capability needed by source-to-IR compilation. Do not start an adjacent runner or hardware project.
- **The former Gabbro runtime implemented in Lean is retired and must be removed.** Do not develop, extend,
  optimize or retain it as a fallback/reference execution path. Stage 0 compiles; the assembly runner executes.
  The canonical language model, IR semantics and lowering correctness proofs remain required; they are not
  the retired executable source interpreter.
- **Native CPU floating point (owner, 2026-11-04):** all Stage-0 runtime operations execute in the assembly
  runner; Lean only compiles and proves the IR. Replace Gabbro's software IEEE arithmetic with the toolchain's
  native `Float`/`Float32` primitives in the model and physical CPU operations in the runner. Full-range UInt64
  conversion uses a portable native instruction sequence. Retain finite/range duties and all other guarantees.
  This decision supersedes the older references to Gabbro's kernel IEEE framework below.
- First inventory every existing language form across the Lean model, source front end, IR emitter and
  connected correctness theorem; distinguish missing model support from missing translation or proof.
- **Every Gabbro-to-IR lowering must be formally verified.** Implement it in the actual compiler path,
  connect its generic correctness proof through the whole translation pipeline, and compile that pipeline.
  Tests, per-program witnesses, isolated emitters and detached proof fragments do not replace the generic
  lowering theorem and do not make a language case complete.
- Do not start separate generic instruction-cost, timing, hardware or proof-infrastructure projects.
  Proof changes are limited to what is necessary to connect the actual source-to-IR implementation while
  preserving existing guarantees. Do not weaken checks or semantics to enable a case.
- Test emitted IR with the assembly runner when needed. Never add another Gabbro interpreter or restore the
  retired Lean execution path.
- **`grammatik/`** is changed only under these owner rules of 2026-11-01; outside them it is not touched for this
  task (reuse its compiled artifacts, run affected Stage-0 checks directly):
  - **Exports:** pure source-to-G exports in `grammatik/Grammatik/Parser/Elab/*` for forms whose canonical model
    rule already exists may be added, batched into ONE change by ONE agent with one grammar rebuild,
    `gabbro_ziel` still on the standard axioms and the Lean guardian afterwards.
  - **Model extension:** wherever the Lean model or machine G is not strong or complete enough for an existing
    source form, extend it there (syntax, G semantics, `Akzeptiert`, proofs) instead of dropping the form. Every
    extension keeps `gabbro_ziel` on the standard axioms, never weakens a guarantee, describes any change of
    meaning of `Spec.lean` in its commit, and is followed by the Lean guardian. Several agents may change
    `grammatik/` at the same time, each in its own worktree; root merges them one after the other.
  - **C packages:** all 18 C packages may change `grammatik/` and machine G as designed in
    `dokumente/IR-COMPILATION-LANES.md`, with the recommended answer to every owner question there, provided
    `gabbro_ziel` stays proved on the standard axioms. They are done in three full `grammatik/` build rounds:
    round 1 C13, C17, C05, C04, C03; round 2 C01, C06, C07, C08, C09, C11, C18; round 3 C10, C02, C12, C14, C15,
    C16. Between rounds only single changed modules are checked.
  - `axiom`-`ensures` stays a named hardware assumption (`AxVertragO`); it is not turned into a runtime check.

Report which language cases actually compile, which remain refused, and what was measured. The broader roadmap
below is not authorization to start adjacent projects.

### Builds, memory and CPU

The machine has 20 threads and 31 GB and no swap; the caps below follow the OOM/CPU overload of 2026-11-01.

- **At most two Lean builds or direct Lean checks run globally**, across all worktrees, including audits,
  witnesses and `lean --run` compiler invocations. Each holds a slot lock
  `/home/simon/.cache/gabbro-stage0-build.slot-N.lock` (N = 1, 2) and releases it after each module/check. Never
  run two checks in one worktree or mutate artifacts another check reads (use isolated artifact overlays); never
  interrupt another worker's running proof.
- **Scopes** (`systemd-run --user --scope …`):

  | Run | Locks | Scope |
  |---|---|---|
  | full `grammatik/` build (only one globally) | both | `-p AllowedCPUs=0-11 -p CPUQuota=1200% -p MemoryMax=<min(MemAvailable-6G, 14G)> -p MemoryHigh=<2G below> -p MemorySwapMax=0` |
  | Stage-0/runner `lake build` | both | `LEAN_NUM_THREADS=2`, `-p MemoryMax=<min(MemAvailable-4G, 16G)> -p MemoryHigh=<1G below> -p MemorySwapMax=0` |
  | single-module check | one | `-p AllowedCPUs=0-11 -p CPUQuota=400% -p MemoryMax=5G -p MemoryHigh=4G -p MemorySwapMax=0` |

- **Rebuild single modules only (owner, 2026-11-02).** Check the changed modules and the modules that import
  them, one module at a time in dependency order (`lake build <Module>` or `lean` on the file inside a
  single-module scope); the module system keeps dependents unbuilt when no interface moved. A full package build
  (`grammatik/`, `stage0/`) runs only when single-module checks cannot settle a question, at most once per C round,
  and the lead says why in its report.
- **Inside a single-module slot exactly ONE `lean` process runs**, with `-j4 -DElab.async=true -M4608`
  (asynchronous elaboration is the standard; the threads of one process share its imports), module by module in
  dependency order. Never run a `lake build` of `stage0/` inside such a slot: it spawns one `lean -M16384` per
  module and thrashes inside the 5G scope.
- **No swap for ANY run:** every process that can use real memory (`lean`, `lake`, the runner and
  regression loops, guardians, Python measurement scripts) runs inside a scope with `-p MemorySwapMax=0` and a
  MemoryMax/MemoryHigh. No exceptions.
- **Nothing heavy starts** when the load average is above 16 or less than 8 GiB are available (`free -g` before
  every heavy step); wait instead.
- **Heavy witness modules are not rebuilt during work.** Probe files that run the parser/elaborator in the kernel
  (`Grammatik/Parser/Elab/Proben/**`, `*Proben*.lean`) need 7–12 GB each; they are checked only in the final
  integration build of a round, never in single-module checks.
- **Build less, keep working:** batch several finished edits into one check of the affected modules. While a check
  runs or waits for memory or a slot, keep writing the next proofs and code; never stop a run because a check is
  pending, and never end a run while a build it started still runs.
- **One Mathlib for all trees:** the read-only store is `grammatik/.lake/packages` of the root checkout. A lead
  tree links it with `cp -al <root>/grammatik/.lake/packages <tree>/grammatik/.lake/packages` and copies only its
  own build part (`rsync -rlpgoD --exclude packages …`); nobody copies or rebuilds Mathlib.
- **At most 50 GB for all worktrees together.** Root deletes every worktree right after its merge.
- **Nothing in `/tmp`:** it is RAM. Scratch goes to `.scratch-*` inside the own worktree (`TMPDIR` points there);
  everything in `/tmp` together stays under 100 MB, and root removes leftovers no process holds open.

### Small files and the Lean module system (fixed rules)

**Keep every file small (owner, 2026-11-02).** Below 500 lines is the hard limit for every Lean file; aim for
200–300 lines, split a file into cohesive modules as soon as it nears the limit (pure moves, no change of a
statement or a name), and keep functions and proofs short. Small files are what makes single-module rebuilds
cheap and keep build memory low.


All Lean in the repository (`grammatik/`, `stage0/`, `runner/`, `programmlogik/`, `passlogik/`, `bruecke/` and
every other Lean package) is migrated completely to the Lean module system (`module`, `public import`/`import`,
explicit `public`/`@[expose]` visibility), and every new or changed Lean file must be a module that uses it: expose
only what dependents must unfold, keep proof bodies and helpers private, so a change that does not move an
interface does not rebuild dependents. A non-module Lean file is a layout finding.

## 1. The goal

> **A Gabbro user proves only their own logic plus named hardware assumptions.** Memory safety, race freedom,
> contracts where claimed — in concurrent runs too — and time are carried by the language.

The end sequence:

1. **The goal theorem** over the Lean model (`gabbro_ziel`, §2) — proved.
2. **Transfer into the checker and the compiler**: everything the model proves becomes the verified checker
   and compiler written in Lean (Stage 0 first), in the order of §3 (Lean model first).
3. **Translation validation**: source → model → final machine bytes, checked in Lean, with W / GX reused for
   concurrency.

**Acceptance of a change to the model** (also a change of the goal statement): the full Lean build is green and
the core theorems are proved — `gabbro_ziel` with exactly `propext`, `Classical.choice`, `Quot.sound`, no
`sorry`, and the witnesses of the new theorems. A change that moves the meaning of `Spec.lean` is described in
the commit and in the relevant plan section.

**What may be said:** "The goal theorem is proved over the model, with a witness and non-degeneracy."
**What may NOT be said:** "Gabbro is verified." The checker inside the statement is the Lean Bool `Akzeptiert`,
not a deployed checker, and no bridge to any binary is built. The
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
- **Simplicity without losing a guarantee**: ceremony count down AND pass register
  constant. Never derive `ensures`, never turn a refusal into a warning.
- **Where the model has no rule yet, refuse** — never accept by default.

**Compiler, checker, parser**
- **No legacy**: only the newest state. What is replaced is deleted (history stays in git): no compatibility
  layers, deprecated paths, old names or flag aliases, retired-but-kept codes.
- **No Rust and no handwritten C in the repository (owner, 2026-11-10).** The Rust checker, CLI and LLVM
  emitter (`crates/`) and the C probes were deleted; they are in git history before `254a5cc5c`, the older C
  emitter in the tag `archiv/c-emitter-2026-10-17`. The compiler is the Lean Stage-0 path; the assembly runner
  (`runner/runner.s`) executes. Nothing is rebuilt in Rust or C.
- **Target direction: AArch64** (Armv9-A); the former Lean model of it (`arm/`) was removed on 2026-11-01 and lives
  in git history. The x86-64 hardware model is archived (branch `archive`); the one exception is the verified
  stage-0 runner (`PLAN-SELF-HOSTING.md` §2.2, Simon 2026-10-28), whose x86-64 instruction subset is written anew and tested against the CPU.
- **Target portability**: source semantics, IR, optimisation and validation stay generic; ABI, image and entry
  requirements are described in checked profiles; environment services are Gabbro bindings with user-logic proof
  obligations. No implicit Linux/POSIX/libc/ELF dependency; freestanding has no mandatory host runtime.
- **Vendor neutrality**: the hardware model holds on all CPUs of an architecture. What a vendor calls undefined or
  model-specific stays FREE (all allowed results, never one observed value).
- **Optimisations**: a validated optimised image or a refusal, never "optimised but unchecked".

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
  default), and OPEN regions without a ceiling (`Deklaration.offen`) whose cells come only from
  the program's provider. **OOM is user logic**: an allocation needs no source OOM path; that the provider has
  memory to give is the program's own obligation. An arena's `else` at its declared ceiling is a capacity bound,
  not OOM.
- **Floats are in scope** (IEEE kernel model). Probabilistic statements are out of scope.

**Lean layout**
- **Every Lean file has fewer than 500 lines** (owner, 2026-11-01): also every OLD file — the 235 files above
  the limit (largest `Uebersetze.lean`, 6455 lines) are split into cohesive modules, pure moves without changing
  a statement or a name. Large files also cost most of the build memory.
- Every folder holds at most **20 entries**, and every Lean file lives in a sensible folder. The placement rules
  are `instrumente/teile/lean-layout-rules.py`; `python3 instrumente/teile/lean-layout.py --check` runs inside
  the Lean guardian, `--apply` moves new modules into place and rewrites imports.

**Repository**
- **Language:** everything in the repository is English — documents (every `.md` and its file name), comments,
  commit messages, diagnostics. The conversation with the project owner is in German.
- **At most 30 `.md` files** in the repository. Reports, verdicts and interim states belong in git, not in the
  tree.
- **Commits** are plain `git commit` with a Conventional Commits subject (`type(scope): summary`, types `feat`,
  `fix`, `refactor`, `perf`, `test`, `docs`, `build`, `ci`, `chore`); no helper script, no extra trailers beyond
  the model's `Co-Authored-By`. Write the message to a file outside the tree and commit with `git commit -F <file>`.
- **Squash before pushing**: work that belongs together (e.g. a feature and its follow-up fix) becomes ONE commit
  before it is pushed (`git reset --soft <base>` and recommit, or `git commit --fixup` + autosquash). Pushed
  history is never rewritten (no force-push), so squash only what is not yet pushed.
- **Commit every building step.** Work that builds is committed at once.
- **Caprock** (the OS this language exists for) lies read-only in `../caprock-messbasis`: never commit into it.
- **Tag milestones** at the push that reaches them.

**Security**
- Never write API keys or passwords into the repository, memory or logs.
- When the permission classifier blocks something, do not work around it; ask.

## 4. Where things run

Everything runs locally, in this checkout or in worktrees beside it: Lean builds, acceptance
runs and QEMU stages. There is no build server. One exception (Simon, 2026-10-28): the differential tests of the
x86-64 runner model against the CPU run on Simon's x86-64 machine (`PLAN-SELF-HOSTING.md` §2.2).

- **GitHub:** push is `git@github.com:SimonVitzethum/Gabbro.git` with key `~/.ssh/id_ed25519_github`; fetch
  goes over https.
- **One heavy run at a time per tree**, with `free -g` beside it. Heavy are `lake build`, direct `lean` checks and
  the acceptance run. Every heavy run goes under a memory scope (`systemd-run --user --scope -p
  MemoryHigh=… -p MemoryMax=… -p MemorySwapMax=0`); the soft limit lets the kernel reclaim before the hard limit
  kills. An abort for lack of memory is not a finding.
- Lean comes through `elan` (`ELAN_TOOLCHAIN` must not be set).

## 5. Procedure: branch, build, merge, push

- **Large changes run on a branch in a worktree beside the checkout** (`git worktree add -b NAME ../dir
  master`), with the warm build cache set up as in "One Mathlib for all trees" (lead trees only), so that master
  stays buildable for everyone else. Build,
  commit there; merge when the acceptance of §1 holds.
- **After every merge:** build `grammatik/` (also after a clean merge: a new structure field or a changed arity
  only shows in the build), run the layout check, then the guardians.
- **The push gate is the two guardians** (`./instrumente/abnahme.py`):

  | Guardian | Subject | What it checks |
  |---|---|---|
  | `instrumente/pruefe-lean.py` | the Lean model and stage 0 (`stage0/`) | `lake build` of both, `gabbro_ziel` on the standard axioms only, no `sorry`/`admit`/`native_decide`/`axiom`, layout |
  | `instrumente/pruefe-gabbrov.py` | GabbroV | `lake build`, proofs without `sorry`, the bridge `bruecke/` built on the standard axioms over the tracked duty files |

  Exit code `0` measured and green, `1` measured and red, `2` nothing or not everything measured — that is not a
  green. A third guardian is not built: a new check becomes a Lean theorem or a stage in one of the two.
- **Push master after checked merges**, without asking: first grep the outgoing diff for keys; never push red;
  never force-push; if origin moved, merge first and check again. No new branches on GitHub.
- **Delete worktrees and clones right after their merge.**

## 6. Parallel work

- **Every parallel worker (another session, a subagent) gets its OWN worktree** and scratch directory, never
  this checkout; its tree is on `master` before it starts. Two runs in one tree measure a mixture.
- A lead tree gets its warm caches (`grammatik/.lake`, `programmlogik/.lake`) as in "One Mathlib for all trees":
  Mathlib hard-linked, never copied; with no cache `lake` goes off to clone Mathlib and hangs, and a stale
  `.lake` is worse than none. Sub-agent trees carry no `.lake`.
- Before starting work in an area, check whether another session already works there (worktrees, recent file
  times) and do not duplicate it.
- Reviews and assessments are done directly, not delegated.

## 7. Number ranges and counters (free from here)

| Kind | Next free |
|---|---|
| Gift (poison-probe) numbers | **1488** (1448-1469 stay unused; 1149, 1150, 956, 957 and 958 retired) |
| Example numbers | **1172** |

Re-measure instead of trusting this table: `ls beispiele beispiele/gift | tail`. The highest number in the tree
does not drift; a ledger does. Next free is always above the highest number in use. (The diagnostic-code range
and the sentence register went with the Rust checker.)

## 8. Files that matter

| What | Where |
|---|---|
| The goal statement | `grammatik/Grammatik/Zielsatz/Kern/Spec.lean`, `Beweis.lean`, `Akzeptiert.lean`, `Proben*.lean`, `SpecProben.lean`; `Zielsatz/Atomar/BeweisAtomar.lean` |
| Model | `Kern/` (syntax, machine G, semantics), `Nebenlaeufigkeit/`, `Speichermodell/`, `Logik/`, `Bausteine/` (arenas, regions, ownership, floats) |
| Code model and lowering | `grammatik/Grammatik/Code/` (`Model`, `Lower`, `Refine`, `Conc`, `Gate`) |
| Test sets M and N | `grammatik/Grammatik/Gen/` (generator, coverage cells, fine cells) |
| Plans | `dokumente/IR-COMPILATION-LANES.md`, `dokumente/MACHINE-IR-PLAN.md`, `dokumente/PLAN-SELF-HOSTING.md`, `dokumente/PLAN-LONG-RANGE.md`, `dokumente/LOW-LEVEL-SYNTAX-PLAN.md`, `dokumente/ABSTRACTION-SYNTAX-PLAN.md` |
| Theorem map | `dokumente/THEOREM-MAP.md` (new sections at the end) |
| Guardians | `instrumente/abnahme.py` and the two `instrumente/pruefe-*.py` (`dokumente/TOOLBOX.md`) |

## 9. Pitfalls that cost real time (each happened)

**Tools**
- **`pgrep -f` / `pkill -f` match their own command line.** Kill by PID; wait by polling a file or `ps -C`.
- **A guardian that aborts reads like one that passed.** Look for the numbers it no longer prints; measure the
  base in a throwaway worktree before guessing. `set -e` in scripts stops counting at the first hit.
- **Mechanical edits over many files:** a regex that matches a pattern alternative can strip its prefix or
  indentation; patterns with non-ASCII characters (`t₂`, `σ`) need a UTF-8 aware tool. Rebuild after every
  mechanical edit and read what it changed.

**Merging**
- Recurring conflicts: `Grammatik.lean` imports (take the union); duplicate THEOREM-MAP section numbers
  (renumber); two branches defining the same Lean name (rename one).
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

The full compiler is written in Gabbro and formally verified, without refinement and without translation
validation (owner, 2026-11-10): nothing is checked per compilation and refused. Its design is
[MACHINE-IR-PLAN.md](dokumente/MACHINE-IR-PLAN.md): one architecture-neutral SSA IR (GIR) of micro-operations;
every optimisation, register allocation and scheduling included, has a logic proof with GabbroV; real
instructions are assigned to neutral cells of GIR by a per-target table; the test set M over the cells proves the
emitted machine code and is the evidence of the one named hardware assumption. GabbroV is independent of M and N.
Order: Stage 0 first, then GabbroV written in Gabbro with an initial Lean proof, then the compiler. Source safety,
G/GX concurrency, floats, contracts, call logs and budget guarantees remain; OS and freestanding profiles stay
generic.

Performance against equivalent C built with `gcc -O3` or `clang -O3` (the faster of the two): minimum 100 % on every workload
class and ISA (Simon, 2026-10-25; was 80 %), ambitious above 110 %.
Fixed-work score `100 * Ctime / Gabbrotime`, throughput score `100 * Gabbrothroughput / Cthroughput`, per
workload and class, on full validated direct binaries with matched hardware, ISA, semantics and settings.
Compile latency includes checking, optimisation, production, validation and Lean kernel checking. Targets are
OPEN until measured; no universal speed claim. 

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
