# AGENTS.md — rules for working on Gabbro

This file holds the standing rules and recommendations for everyone who works in this repository, human or model
(`CLAUDE.md` is a symlink to it). It contains no current work and no site details:

- what is being worked on now, and in which order, is in the plans under `dokumente/`
  ([PLAN-COMPILER-READY.md](dokumente/PLAN-COMPILER-READY.md) first);
- the concrete workflow of a site (build hosts, slot scripts, memory caps, agent line-up, credentials) lives in an
  untracked `CLAUDE.local.md` / `AGENTS.local.md` that instantiates these rules and is never pushed;
- history (who decided what, when) is in `git log`.

---

## 1. The goal

**A Gabbro user proves only the logic of their own program and chooses named assumptions about hardware and
environment. Everything else is carried by the language**: memory safety, race freedom, lock discipline, contracts
and invariants where declared, time and memory bounds, isolation, information flow — in concurrent runs too, on
every supported target. The direction of every change is to move work from the user onto the language model, never
the other way.

The end sequence is:

1. **The goal theorem** over the Lean model (`gabbro_ziel`, §3) — the language's promise, proved.
2. **A verified checker and compiler** that carry that promise down to machine bytes: Stage 0 first, then the
   compiler written in Gabbro and proved with GabbroV.
3. **A system built on it**: the compiler compiles itself, and an operating-system kernel written in Gabbro runs on
   it — with no assembly anywhere and no unverified runtime underneath.

Three targets from the start: x86-64, AArch64 and RISC-V 64 are reached by adding a target table and a binding,
never by changing sources, IR, passes or proofs. Performance target: at least the faster of `gcc -O3`/`clang -O3` on
equivalent C, per workload class and ISA; claims only where measured.

**What may be said:** "The goal theorem is proved over the model, with its non-degeneracy proved." **What may NOT
be said:** "Gabbro is verified" — until the checker and the compiler in the statement are the deployed ones and the
bridge to the bytes is built.

## 2. Where things belong

Every piece of work belongs to exactly one layer. Putting it in the wrong layer is a design error, not a shortcut.

| Layer | Holds | Never holds |
|---|---|---|
| **Lean model** (machine G, GX, `Akzeptiert`, `Spec.lean`) | the ONE definition of the language: syntax, semantics, typing and acceptance rules, the goal theorem | anything a particular program needs |
| **Checker** | the language's rules, decided: types, authority, ownership, locks, flows, and every property a program declares *optionally* for it to decide (contracts and invariants in the decidable fragment, `decreases`, bounds, levels). It decides or refuses. | program logic beyond a decidable fragment; warnings in place of refusals |
| **Compiler** (Stage 0, later the Gabbro compiler) | lowering and optimisation, each proved once for every program | per-program checks, translation validation, unproved fast paths |
| **GabbroProve** | program logic: what is specific to one program and no language rule can carry — functional correctness of an algorithm, a driver following its device protocol, probability or cost bounds outside the decidable fragment. The user proves it in Lean over the generic model. | anything the language could carry generically |
| **Named assumptions** (the list in the `Spec.lean` header) | what nobody can prove: that hardware behaves like its model (per target-table row), environment software outside the verified image (firmware, a host OS) with a declared contract, random sources, hardness of cryptographic primitives | assumptions that hide a missing proof of the language |
| **The user** | their own program logic (through GabbroProve) and the choice of assumptions | anything else |

Consequences:

- **The model comes first.** A construct, clause, type rule or acceptance rule changes in the Lean model first
  (machine G, `Akzeptiert`, `gabbro_ziel` still proved), then in the checker, the compiler and
  `SYNTAX.md`/`LANGUAGE.md`. A form the checker accepts and the model lacks is a checker bug. Where the model has no
  rule yet, refuse.
- **Guarantees come from generic theorems only.** Nothing in the compiler, checker or printers exists for
  particular programs. There are no per-program Lean files and no witnesses (owner, 2026-11-19).
- **A decidable declared property is a capability of the language**, not user logic; once the checker decides it,
  the user no longer owes it.
- **Hardware enters only as named per-row or per-envelope assumptions** (a target-table row, a speculation
  envelope, a persistence envelope); every statement above the table is hardware-independent.
- **Software inside the verified image is user logic; software outside it is a named environment assumption with a
  declared contract.** Nothing is OS-specific: a system or kernel call is a generic call whose contract the program
  or its binding library declares.
- **No assembly anywhere.** Privileged operations are target-binding calls over linear `context<P>`; their meaning
  is a neutral IR cell, their bytes are target-table rows; entry and exit code is generated from `entry`
  declarations. Boot code is user code in Gabbro.
- **No `unsafe`.** All low-level access is checked authority; memory from outside comes as a region, never from a
  number; no int→pointer conversion.
- **Memory:** regions with a ceiling refuse when full; open regions without a ceiling stay admitted (the provider's
  contract carries freshness); running out of memory is the program's own logic.

## 3. The goal theorem

- **Shape:** for every checker `C`, declaration `D`, unit `E` and enumerations: (a) the checker accepts →
  (b) the user's duties hold → (c) the named hardware assumptions hold → (d) the runtime starts what is declared →
  every reachable machine satisfies `Ziel`. The legs of `Ziel`, the atomic rely and the derived statements are
  listed in `Spec.lean`; the proof files are `Zielsatz/Atomar/BeweisAtomar.lean` and `Zielsatz/Kern/Beweis.lean`.
- **Axioms:** `#print axioms gabbro_ziel` is exactly `propext`, `Classical.choice`, `Quot.sound`. No change may move
  it.
- **The header of `Spec.lean` is the ONE list** of named assumptions and of what is NOT claimed. Every extension of
  the goal is a diff of `Spec.lean` (or of what it uses) and is described as such in the commit.
- **A change of meaning of the goal statement is the owner's decision**; it is shown as a concrete diff, with a
  recommendation, before it is merged. Strengthening the language's promise is the default direction.
- **Extensions stand beside the goal, not inside it,** when they are a different kind of statement (linking,
  liveness, waiting, information flow, probability, …): a separate statement that reuses the safety legs.
- **Acceptance of a model change:** the full Lean build is green, `gabbro_ziel` is on the standard axioms, no
  `sorry`. **No witnesses anywhere (owner, 2026-11-19):** no `_zeuge` theorems, no witness modules, no fixtures
  evaluated to show a statement; prefer proofs. Where a ∀-over-syntax premise could be contradictory, its
  satisfiability is a proved lemma (`NAME_erfuellbar`: the premises hold jointly), one per premise bundle shared
  by all theorems over that bundle, checked in seconds, never a run of the compiler on a source text. **Every new
  language form gets such a lemma** (owner, 2026-11-19): an instance in which the form occurs and the premises of
  the theorems that cover it hold jointly.

## 4. Rules for the code

- **Safety is never traded for features.** No change weakens a guarantee, a check or a semantics to make a build
  green; a wall that only yields by weakening is recorded as a finding.
- **Simplicity without losing a guarantee:** fewer ceremonies for the user, the same set of checks. Never derive
  `ensures`, never turn a refusal into a warning.
- **No legacy:** only the newest state. What is replaced is deleted; no compatibility layers, deprecated paths, old
  names or flag aliases. History is in git.
- **No Rust, no handwritten C, no assembly** in the repository; runtimes and binding libraries are written in
  Gabbro. The compiler path is Lean (Stage 0) and the assembly IR runner executes its output; nothing else
  interprets Gabbro.
- **Target portability:** source semantics, IR, optimisation and proofs stay generic; ABI, image and entry
  requirements are checked profiles; whatever is specific to one architecture lives in its table or binding only.
- **Vendor neutrality:** the hardware model holds on all CPUs of an architecture; what a vendor leaves undefined
  stays free (all results allowed).
- **Optimisations:** a proved optimised image or none — never "optimised but unchecked".
- **Every lowering is formally verified** in the actual compiler path and connected through the whole pipeline;
  tests and per-program witnesses do not replace the generic theorem.
- **Work is measured in finished, connected cases**, not in helper lemmas, commits or added lines. Do not start
  adjacent infrastructure, timing or hardware projects that the plan does not ask for.

## 5. Rules for Lean

- **Module system everywhere** (`module`, `public import`/`import`, `@[expose]`): expose only what dependents must
  unfold; a non-module file is a layout finding. Do not put `private` helpers under `@[expose] public section` when
  exposed definitions use them.
- **Small files:** every Lean file below 500 lines, aim for 200–300; split into cohesive modules by pure moves. At
  most 20 entries per folder; the layout tool places new modules. Reason: Lean elaborates one file on one thread
  and Lake parallelises over files, so a large file is a serial bottleneck (files of ~15 000 lines checked very
  slowly) and holds its whole environment in memory. A split cuts along topics (one definition family with its
  lemmas per module), not at a line count: a file near the limit is split where its theory divides.
- **Toolchain truth, not training memory:** the pinned Lean and Mathlib decide; every lemma name is grepped from
  the tree or the toolchain before use.
- **Forbidden:** `sorry`, `admit`, `native_decide`, `axiom` (outside the allow-list), `unsafe`.
- **Fast proofs only:** a module checks in well under two minutes, no declaration takes more than a few seconds. No
  kernel evaluation (`decide +kernel`, kernel `rfl`) over strings, whole programs or images on the compiler path;
  prove from general theorems with small explicit premises. A module checks in at most 2 GiB, and every build, check
  and probe runs under a `timeout`. Stage 0 carries no per-program witnesses that run the compiler on a source text:
  that its output satisfies the goal is the image theorem's job (B6). A slow module is a finding and is fixed.
- **Proof tactics that hold up:** `split` (not `split_ifs`); `simp only [...]` with named lemmas where possible;
  destructure `Except`/`Option` results with `cases h : … with` instead of splitting `do` blocks; after
  `cases h : x`, prove leftovers with `first | exact h | rfl | simp_all`; use `match`/`termination_by` instead of
  `cases` for recursion; a function matching an indexed family on a FIXED index is not structural — generalise the
  index if it must reduce by `rfl`.
- **New constructors go at the END of their inductive** (`Expr`, `Stmt`, `Block`, …): generators and cell tables
  number them by position.
- **Silicon over proof shape:** a green proof of a wrong hardware definition is a finding, not a result.

## 6. Builds and machines

- **Every heavy run is bounded**: `lake build`, `lean`, witnesses, guardians, the runner and measurement scripts run
  inside a memory-limited scope (a hard limit with a soft limit below it) and never in swap.
- **Every `lake build` sets `LEAN_NUM_THREADS`**, chosen so that threads × the largest module's memory fits the
  scope; a build whose job counter stands still is stopped by its own PIDs and restarted with fewer threads.
- **Cap concurrent builds by memory**, hold a lock per build slot, never run two builds in one tree, never mutate
  artifacts another build reads, never interrupt another worker's proof; start nothing heavy when memory or load
  is already tight.
- **Build single modules** during work (changed modules and their importers, in dependency order); the full
  package build runs before a push. Heavy probe modules are built in the integration build, not during work.
- **One build per wave:** merge the finished branches, build once, repair or drop what fails, build again.
- **Keep writing while a build runs**, in a second tree; never edit a tree a build reads; never end a run while a
  build it started still runs.
- **One Mathlib for all trees** by hard links to one read-only package store; build output is never shared by hard
  links (Lean rewrites it in place).
- **Disk is a budget:** delete worktrees and clones right after their merge or their agent's report; clean logs.
- **Scripts that running jobs execute are replaced atomically** (write a new file, rename), never edited in place.
- **No scratch in RAM-backed temp directories**; use a `.scratch-*` directory in the own tree and delete it.
- `ELAN_TOOLCHAIN` is never set; Lean comes through `elan`.

## 7. Working with agents

- **One lead** decides, merges, builds the integration branch and pushes; it asks the owner only about a change of
  the goal's meaning, a rule of the language, or a decision a plan lists as open — with a recommendation — and
  decides everything else by the strongest variant (maximum safety and power; effort is no argument).
- **Model choice by measured record**, not by fixed role: keep a record per finished task of how well each model
  proves and how often it errs, and assign by it.
- **Reviews read statements, not proofs:** does it say what its name and comment claim, can its premises hold
  together (proved, not by a fixture), is it vacuous. Reviews are tasks too; the lead checks every finding before acting on it.
- **Every worker gets its own worktree** and scratch directory, never the lead's checkout; before starting in an
  area, check that nobody else already works there.
- **Agents build what they changed before they report**, in an isolated build slot where the site offers one
  (single modules, never whole packages or heavy probes); a report names the green runs. The lead's integration
  build stays the acceptance.
- **Every brief ends with: report fully before stopping.** A brief is self-contained: goal, branch base, files,
  rules, what is already known, what to deliver.
- **One integration branch;** agent commits are merged as they are (no group commit over a wave); fold only a
  not-yet-pushed fixup into its commit.
- **Do not accumulate unmerged work:** merge and build in small waves; an unbuilt subsystem is never integrated.
- No `.py` helper scripts for agents; agents use git, `lake`, `lean` and the shell.

## 8. Repository

- **English** everywhere in the repository (documents and their file names, comments, commit messages,
  diagnostics). At most 30 `.md` files; reports and interim states belong in git history, not in the tree. No
  tracked work list: open work and findings live in plans or in a gitignored scratch file.
- **Commits:** Conventional Commits (`type(scope): summary`), message from a file (`git commit -F`), the model's
  `Co-Authored-By` line and no other trailers. Commit every building step. In a shared checkout commit by path.
- **Branches:** the integration branch is pushed to `dev` without a build gate — `dev` may be red. `master` only
  advances to a `dev` commit whose full builds of every package and both guardians are green (owner, 2026-11-19).
- **Master gate: the two guardians** (`./instrumente/abnahme.py`): `instrumente/pruefe-lean.py` (Lean model and
  Stage 0: builds, `gabbro_ziel` on the standard axioms, no forbidden tokens, layout, every Lean file reached from a
  package root) and
  `instrumente/pruefe-gabbrov.py` (GabbroV and the bridge). Exit `0` is green, `1` red, `2` not everything measured
  — not a green. A new check becomes a Lean theorem or a stage of one of the two, never a third guardian.
- **Push** without asking: grep the outgoing diff for keys, addresses and other site data; never push red to
  `master`; never force-push or rewrite pushed history; if the remote moved, merge and check again. No new branches on
  the upstream remote. Tag milestones at the push to `master` that reaches them.
- **Security:** never write keys or passwords into the repository, memory or logs; credentials are site
  configuration. When a permission check blocks something, do not work around it; ask.
- **Number ranges** (poison probes, examples): the next free number is one above the highest in use — measure it
  (`ls beispiele beispiele/gift | tail`), never keep a ledger.
- External reference material (e.g. the Caprock OS) is read-only: never commit into it.

## 9. Pitfalls that cost real time

- `pgrep -f` / `pkill -f` match their own command line: kill by PID.
- A guardian that aborts reads like one that passed: look for the numbers it no longer prints.
- Mechanical edits over many files: a regex can strip prefixes or indentation; non-ASCII names (`σ`, `t₂`) need a
  UTF-8 aware tool; rebuild and read the diff after every mechanical edit.
- A clean merge can still break: new structure fields and changed arities show only in the build. Recurring
  conflicts: aggregate import files (take the union), duplicate section numbers in the theorem map (renumber), two
  branches defining the same name (rename one).
- A leaked `ELAN_TOOLCHAIN` rebuilds everything under the wrong Lean.
- A build without `LEAN_NUM_THREADS` thrashes instead of failing.
- Overwriting a script that a running shell executes corrupts the running job.
- A "green" package build may have built only part of the package: compare the job count with a full build.
- A module that no package root imports is never compiled, by the build or by a guardian; it rots unseen
  (measured 2026-11-19: 103 such modules, several broken, one false claim). Register every new module in a root.
- A theorem stated over a dependent `match` written inline twice creates two different matcher constants; name the
  function instead.

## 10. Talking to the owner

- In the owner's language; direct and concrete: what was done, what is open, what is uncertain. Never claim more
  than was measured.
- Estimates as ranges, with the critical path named.
- Short status lines while long jobs run.
- A decision that is the owner's is asked once, with a recommendation and the concrete diff.

## 11. Files that matter

| What | Where |
|---|---|
| The goal statement | `grammatik/Grammatik/Zielsatz/Kern/Spec.lean`, `Beweis.lean`, `Akzeptiert.lean`; `Zielsatz/Atomar/BeweisAtomar.lean` |
| The model | `grammatik/Grammatik/Kern/` (syntax, machine G, semantics), `Nebenlaeufigkeit/`, `Speichermodell/`, `Logik/`, `Bausteine/`, `Niedrig/` |
| Test sets M and N | `grammatik/Grammatik/Gen/` |
| Stage 0 and the runner | `stage0/`, `runner/` |
| GabbroV and the bridge | `programmlogik/`, `bruecke/` |
| Plans | `dokumente/PLAN-COMPILER-READY.md` and the plans it names |
| Theorem map | `dokumente/THEOREM-MAP.md` (new sections at the end) |
| Guardians | `instrumente/abnahme.py`, `instrumente/pruefe-*.py` |
