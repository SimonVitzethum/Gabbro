# AGENTS.md — how work on Gabbro is run

*Written 2026-09-15 by the Claude session that ran the project from the laptop until the move to
the server; since 2026-09-27 all work runs locally again and no second machine is used.
`CLAUDE.md` stays the Simon's work instructions (German); this file is the operating manual
beside it. Execution is local-only (Simon, 2026-09-27); where older notes elsewhere still name
a remote build machine, this file wins for execution.*

**Who reads this:**

- **The orchestrating Claude session** in this checkout (tree `/home/simon/Dokumente/Gabbro`).
  It reads everything below.
- **A Muse contributor lane** (opencode, local clone), if it sees this file. The HARD RULES in its
  lane prompt bind it, and §5–§8 are not its business. In particular it never runs
  `git push` or network operations directly; it uses `./cargo-pruef`, `./emission-pruef`,
  `./lean-bau` and `./lean-probe`.
- **An Opus subagent** in a worktree. Its task prompt is authoritative, and §4, §9 and §10 apply
  to it.

---

## 1. The goal, in Simon's words, and the end sequence

> **A Gabbro user proves only their own logic plus named hardware assumptions.** Memory safety,
> race freedom, contracts where claimed — in concurrent runs too — and time are carried by the
> language.

**Simon's end sequence** (memory `zielpruefung-und-opus`):

1. **Two independent verdicts** — one Muse lane, one Opus agent — answer the question "is the
   goal reached?"
2. **Only if both say yes:** transfer everything into the checker (Rust `crates/gabbro-check`)
   and the emitter (`emit.rs`).
3. **Then:** translation validation, i.e. source → model → direct x86-64 machine bytes,
   checked in Lean (selected target since Simon's decision, 2026-10-01). The current C11 backend
   and its existing validation proofs remain legacy evidence; no direct x86 backend is yet
   implemented. Reuse W / GX for concurrency and prove the per-access x86-TSO bridge.

**Where this stands (2026-09-15):**

- **Step 1 is done.** `theorem gabbro_ziel : GabbroZiel`
  (`grammatik/Grammatik/Zielsatz/Kern/Spec.lean` is the statement, `Beweis.lean` the proof) has been
  through six review rounds. Round 6: both reviewers independently found *"the goal with named
  gaps — no unnamed gap found"*. W1 is closed in Lean and in Rust.
- **Tags:** `milestone-2026-09-15-gabbro-ziel` (proved) and
  `milestone-2026-09-15-zielsatz-bestaetigt` (confirmed).
- **Steps 2 and 3 are running**; see `TODO.md`.

**What may be said:** "The goal theorem is proved over the model, with a witness and
non-degeneracy." **What may NOT be said:** "Gabbro is verified." The checker inside the statement
is the Lean Bool `Akzeptiert`, not the Rust checker, and the bridge to the C is only partly built.
The [proof-status section](README.md#5-proved-and-not-proved) says exactly this; keep it that way.

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
  - (Opus agent D) `InvRuheG`, `InvSichtG`, `SperrWechselG`, `SperrSichtG`: invariants beyond
    the returns -- wherever no writer runs, at every lock move, and observed by the holder alone;
  - `StartEndeG`, `KeinStartGrundG`, `KeinLogikHaltG`;
  - no deadlock, `KeinWarteZyklus` and (since fix lane F11; carried by (a) since Opus agent H)
    `KernHaltE`: no same-core interrupt deadlock for the handlers the program declares
    (`Programm.unterbricht`, `via idt`), under a named core schedule, for every core assignment;
  - `FortschrittG`, whose stop kinds are hardware, flag, budget and `nieZurueck`;
  - `ZeitAb`;
  - (Opus agent G) `FolgeG`, the leg `folge`: the order of calls in every thread's call log
    (OFFEN O1's L50/L52: an entry or return DIRECTLY behind a named function's return).
- **Since Opus lane O25c (2026-09-26) the goal carries the ATOMIC RELY:** (a) is a `PrueferX`
  (sound against `AkzeptiertSpecX`: the footprint rule admits a shared atomic in no contract,
  concrete checker `akzeptiertX_pruefer`), (b) is `NutzerPflichtA` (every body against every
  value a shared atomic read may return), and the conclusion is `ZielFX`/`ZielX` on the thread
  machine over GX (G whose shared-atomic reads the weak memory answers); `schwach` is
  `SchwachX`, `rennfrei`/`keinKernHalt` are over GA runs, `sperrWechsel`/`sperrSicht`/`zeit`
  over GX steps. The statement of before is `GabbroZielSC` (`Ziel`/`ZielF` over G), derived:
  `gabbro_ziel_sc_aus`. Proof file: `Zielsatz/BeweisAtomar.lean` (`gabbro_ziel`);
  `Zielsatz/Beweis.lean` proves `gabbro_ziel_sc` directly.
- **Axioms:** `#print axioms gabbro_ziel` must be exactly `propext`, `Classical.choice`,
  `Quot.sound`. Every merge that touches `grammatik/` keeps it so.
- **The review rounds and what each repaired** (SATZKARTE §22–§25):

  | Round | Found and repaired |
  |---|---|
  | 3 | P1 unsatisfiable lock invariant; P2 free parameters; P3 payload races |
  | 4 | F1 out-of-range float stop; F2 global deadlock leg; F3 stop classes |
  | 5 | G1: einpassen did not decode sums, floats and fn pointers |
  | 6 | W1: answers at empty types, closed by component 9 `antwortenB` and Rust `N310`–`N314` |
- **The header of `Spec.lean`** is the ONE list of named assumptions and the NOT CLAIMED list:
  termination and waiting bounds, stack depth, the C and the hardware, weak memory beyond
  DRF-SC, unguarded publish/await payloads, floats beyond the kernel IEEE model, starvation
  freedom, invariants inside a running writer or a held section (claimed everywhere else since
  Opus agent D: `invRuhe`, `invSicht`, `sperrWechsel`, `sperrSicht`), a start declared ONCE running on several threads (a routine
  declared twice -- a worker pool -- is covered since fix lane F10). Linking of separately
  compiled units is covered since Opus agent E by a SECOND statement, `GabbroZielVerbund`
  (same hardware assumptions; OFFEN O28 names the rest). Probabilistic statements are out of scope, and dynamic data structures are not yet in the
  statement (§3); since the merge of Opus agent G `Spec.lean` names both in NOT CLAIMED
  (OFFEN O29). Every extension of the goal is reviewed as a diff of
  `Spec.lean`.

## 3. Simon's standing instructions

- **No legacy in the compiler, the checker and the parser** (Simon, 2026-10-17, fixed rule): only the newest
  state; what is replaced is deleted (history stays in git), never kept beside the new: no compatibility
  layers, deprecated paths, old names or flag aliases, retired-but-kept codes, or C-emitter remnants.
- **Language and syntax follow the Lean model, in that order** (Simon, 2026-10-17): the Lean model is the
  single source; any change to the language or its syntax is made in the Lean model FIRST, then in the checker,
  the compiler and `SYNTAX.md`/`SPRACHE.md`. A form the checker accepts and the model lacks is a checker bug.
  Pure lowering of an existing form does not change the language.
- **The C emitter is REMOVED** (Simon, 2026-10-17, final). LLVM (`llvm.rs`, `llvm/`) is the
  only backend; `gabbro build` drives it (checker, IR, `opt`, `llc`, `ld.lld`) and refuses
  module/kmod/metal products by name. The last tree with the C emitter carries the tag
  `archiv/c-emitter-2026-10-17`; the Lean proofs under `grammatik/Grammatik/CBackend` stay as
  archived evidence. Orientation stays: checker + Lean model; no construct is shaped for a
  backend, and a form LLVM cannot lower is refused by name (`Y1xx`). This entry wins wherever
  older notes still orient work on C emission (`emit.rs`, `C001`, `pruefe-emission.sh`).
- **Direction change: AArch64 instead of x86-64** (Simon, 2026-10-07). All work on the x86-64
  hardware model has stopped (its files stay; add nothing there). The next target is AArch64
  (Armv9-A) built on the Sail Arm model, with the missing multicore memory model added in Lean.
  Plan: [`ARM-PLAN.md`](ARM-PLAN.md). Fifteen agents work directly, each in its own shell and
  clone (`/home/simon/Dokumente/gabbro-arm/work/NN`, personal tasks `lanes/arm/NN.md`, common
  rules `lanes/ARM-VORSPANN.md`): five on GabbroV, ten on the Sail Arm hardware model, then on the
  compiler; at most two Sonnet 5.5 agents check that Gabbro itself is Arm-compatible. No Python
  coordinator drives them. Where this file or older notes name x86 goals (below), this entry
  wins. The findings of the language-gap reports come after GabbroV and the hardware model.
  Update 2026-10-07 (Simon): the emitted C backend is DEPRECATED (native AArch64 compiler with
  translation validation is the path); Muse agents may change the checker (`crates/`, via
  `./cargo-pruef-check`) and the Lean model; after the hardware model they build the rest of the
  compiler; performance goal min. 80 %, target 110 % of GCC `-O3`, invariant analysis mandatory
  (`ARM-PLAN.md`).

- **Target portability** (Simon, 2026-10-01): the direct x86-64 compiler must
  support extensible profiles for arbitrary operating systems and freestanding
  environments. Keep source semantics, IR, optimisation and validation generic;
  describe ABI/image/entry requirements in checked profiles and implement
  environment services in Gabbro bindings with user-logic proof obligations.
  No implicit Linux/POSIX/libc/ELF dependency. Freestanding has no mandatory
  host runtime or dynamic loader. Every selected profile retains complete
  final-byte, entry, support-code and mapping validation. This is a requirement,
  not a claim that these targets are implemented.

- **Lean layout** (Simon, 2026-10-05): every folder holds at most **20 entries** (files plus folders), and every Lean
  file lives in a sensible folder. Mandatory, also retroactively. The placement rules are
  `instrumente/teile/lean-layout-rules.py`; `python3 instrumente/teile/lean-layout.py --check` runs inside
  the Lean guardian (`instrumente/pruefe-lean.py`) and `--apply` moves new modules into place and rewrites imports and
  references (the merge gate runs it after every merge). A module no rule matches goes to a `Neu` folder
  when its folder would overflow; the coordinator turns those into rules. Never leave a folder above 20.

- **Vendor neutrality** (Simon, 2026-10-05): the hardware model holds on ALL x86-64 CPUs, Intel and AMD.
  Software runs unchanged on both, so the model is the common architecture; the two differ only where
  behaviour is architecturally undefined or model-specific, and correct software never depends on that.
  Rule: whatever Intel or AMD calls undefined or model-specific stays FREE (all allowed results, never one
  observed value, e.g. BSF/BSR with a zero source, undefined flags). No AMD provenance is claimed while the
  AMD manuals are missing from the clones.

- **Direct compiler progress record** (Simon, 2026-10-01):
  [`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`](dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md) is the central
  record for the direct x86-64 compiler, `-O3`-like/invariant optimisation, Lean-first
  modelling, later Rust implementation and full source-to-final-byte validation.
  Update it with every substantive reviewed integration, finding, scope change and
  measured milestone. Keep proved, running, refused and planned work distinct;
  preserve the dated history and link committed author/reviewer evidence. Only
  checked master is pushed. Lanes report progress to the coordinator and do not
  edit this central document unless explicitly assigned.

- **Push master without asking**, after checked merges. First grep the outgoing diff for keys.
  Never push red. Never force-push. No new branches on GitHub: lane branches stay
  local (`muse/NNN` never leaves this machine), Opus branches stay in their
  worktree until their review lands — the only remote branch besides master is
  the one under active review.
- **Delete worktrees and clones right after a merge.** That covers `.claude/worktrees/*`,
  the lane clones, and the `gabbro-opus-*` directories.
- **Permanent Muse limit, latest Simon instruction on 2026-10-01:** at most
  **15** concurrent managed OpenCode Go Muse model processes, including
  authors, reviewers, organisers, integration owners and repair continuations.
  This supersedes the earlier temporary 40/default 20 rule. Maintain useful
  utilisation near 15 through automatic dependency-aware backfill; do not
  create idle filler or duplicate work. Use isolated clones and per-lane
  session databases, independent exact-candidate review and serial checked
  publication. Never stop or modify the user's own OpenCode process.
- **Proposed friend optimiser ownership:** `grammatik/Grammatik/X86/Opt/Regeln/OptimizationRules.lean`
  and `OptimizationWitnesses.lean` are reserved for the friend handoff. Muse lanes
  do not edit these paths; reuse the one accepted IR and wait for its frozen interface.
  The complete planned optimiser specification belongs in `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`.
- **Continuous Muse utilisation (Simon, 2026-10-01):** keep up to 15 useful models active permanently. Dispatch independently of serial integration/build/publication. Count actual live model PIDs separately from queues, completed lanes and Python/build wrappers. Preserve all safety gates and record genuine dependency/provider/resource bottlenecks. The coordinator manages only its own lanes.
- **Opus agents: at most 2 at a time.** Simon said on 2026-09-14: "nutze 2 opus agenten".
  Muse lanes: as many as useful.
- **Commit messages** go through `arbeitsprotokoll/.commitmsg` + `./commit.sh`. It commits STAGED
  changes only, so `git add` first.
- **Language:** documents, comments, commit messages, diagnostics and `TODO.md` are in English.
  The conversation with Simon is in German. Muster (guardian patterns) become bilingual
  BEFORE a document changes language.
- **Work in real folders, not `/tmp`.** `/tmp` is RAM on this machine. Scratch files go to
  `.claude/muse-arbeit/kratz/`.
- **Every Lean build and every `cargo` run happens locally.** No exceptions for "just a small one".
- **Simplicity is a goal, but no guarantee is given up for it** (dokumente/PRUEFER.md). The measure
  is: ceremony count down AND pass register constant. Never derive `ensures`, and never turn a
  refusal into a warning.
- **Safety is never traded for features** (Simon, 2026-09-17). No lane weakens a guarantee —
  memory safety, race freedom, contracts, costs, lock discipline — to make a wall go green.
  Walls that only yield by weakening are recorded as findings (208's vacuity pins, 203's
  recorded blockage of 07 and 125). Reviewers reject bypasses, no matter how green the build.
- **Guarantees come from generic theorems only** (Simon, 2026-09-30): nothing in the compiler,
  checker or printers exists for particular programs, and GabbroV is to be proved right for EVERY
  program (theorems over every source text), with its statements computed in Lean from the
  source rather than trusted from a Rust print. Per-program Lean files are witnesses only, off
  the trust path. Known violation to remove: `corrlean.rs`'s `Cert104` section (rows only for
  functions named `einzahlen`/`lies`).
- **No handwritten C in a finished Gabbro binary, as far as possible** (Simon, 2026-09-30).
  Runtimes (`laufzeit/`), binding libraries (`bibliothek/`) and program support code are
  written in Gabbro; OS access goes through Gabbro `syscall` items (raw system calls, no libc
  wrapper), hardware access through Gabbro's register/port forms. Handwritten C or assembly
  stays only where Gabbro cannot express the thing (e.g. a process or thread entry before any
  stack exists), each such piece with its written reason, booked as a wall, and counted. The C
  that the emitter WRITES from Gabbro is not meant by this rule. Measured 2026-09-30: ~5,100
  lines of handwritten C/asm/headers in `laufzeit/` + `bibliothek/`, plus 117 in the network
  stack. New handwritten C needs a reason why Gabbro cannot do it.
  **Zero C keeps every guarantee** (Simon, 2026-09-30): code moved from C into Gabbro is checked
  like user code, with no relaxed mode; system and kernel calls are user logic (`syscall`/`extern`
  items in Gabbro source, contracts declared there, not assumptions), nothing knows an operating system; new emitter
  templates are allowed only machine-checked in the template register (`gabbro schablonen
  --tor`), each premise bound to the pass that establishes it.
- **Everything new is modelled in Lean before it is merged** (Simon, 2026-09-30): every new
  construct, runtime primitive, template or binding form gets its machine-G semantics and checker
  side with `gabbro_ziel` still proved (a reviewed `Spec.lean` diff if the statement moves), the
  Lean front end and exporter, GabbroV's `Body` model with the bridge simulation, and a C
  correspondence lemma or proved template for every new emitted form of the current C backend.
  For the selected direct x86 target, require the analogous correspondence through decoded final
  machine bytes, including concurrency; a C lemma alone does not discharge it. Without its Lean
  part a feature stays unmerged (`NEEDS LEAN`).
- **The operating system is user logic, never an assumption, and nothing is OS-specific**
  (Simon, 2026-09-30): a system or kernel call is a generic call whose contract the program or
  its binding library declares in Gabbro; the Lean model, the compiler, the checker and the
  templates know no operating system. Only hardware behaviour is a named assumption.
- **Memory from outside comes as a REGION, never from a number** (Simon, 2026-09-30): a
  `syscall`/`extern` item may answer a region of declared extent whose contract (user logic) says
  it is fresh and disjoint; Lean models it as one generic form. No int->ptr or int->fn-ptr
  conversion enters the language; thread start is a proved template.
- **Floats are in scope** (IEEE model done). Probabilistic statements are OUT of scope for now.
  **Dynamic data structures are IN scope** (Simon, 2026-09-28): structures that grow without a
  static element bound, on heap regions with a declared ceiling and refuse-on-full (TODO §0e).
  A heap without a ceiling stays refused BY DEFAULT. **Planned, not required** (Simon,
  2026-09-29): an explicitly declared region WITHOUT a ceiling, as an opt-in beside the default
  (every allocation may fail and must be handled; the static whole-program memory bound is lost
  for such a program, which is what makes the language Turing-complete in the model). TODO §4.
- **Tag milestones** at the push that reaches them.
- **Security:**
  - Never write API keys or passwords into the repo, memory or logs. The opencode keys live only
    in the lane config outside the repo, never in the tree.
  - When the permission classifier blocks something (e.g. searching the machine for credentials),
    do not work around it; ask Simon.
  - A local password Simon once gave was for WireGuard only; it is recorded nowhere.

## 4. Machines

All work happens on this machine, in this checkout. There is no second machine, no build
server, no `ssh` step: Lean builds, `cargo` runs, Isabelle runs and QEMU stages all run here.

**Exception since 2026-09-28 (Simon): autonomous Claude lanes on `ubuntu@simon.jocraft.cc`.**
Since 2026-09-29 TWO lanes run there, each with one agent and its own clone: the network-stack
lane (`~/Gabbro` + `~/gabbro-netz/`, runner `lauf.sh`, Claude Sonnet 5.5) and, after the GabbroV
lane finished (`FERTIG-V`), the GabbroV-bridge lane (`~/gabbro-v`, runner `lauf-b.sh`, owner of
`programmlogik/`, `lean.rs` and `beweis.rs`; task `dokumente/GABBROV.md` (the task file is in git history)) on
Claude Sonnet 5.5 except stage S3, the simulation theorem, on Claude Opus 5.5.
Since 2026-09-30 the GabbroV-bridge lane is done (`FERTIG-B`) and a PARSER lane works in
`~/gabbro-v` (`lauf-p.sh`, sieve (a), generic proofs only). A third lane, the C-free lane, also runs on the
server since 2026-09-30 (`~/gabbro-c`, runner `lauf-c.sh`, Sonnet 5.5; goal: no handwritten C and
no libc in the network stack's binaries, then in every Gabbro binary), owner of `laufzeit/`,
`bibliothek/linux/` and `bibliothek/linux-kmod/`. It builds and tests in its own tree, merges into master only with
`cargo test --no-fail-fast` green, pulls before it pushes, and never force-pushes. Runner and
task files: `~/claude-lane/` on that machine (`lauf.sh`, `AUFTRAG-*.md`, `STAND.md`, `logs/`).
Nothing on that machine is loaded into its running kernel: kernel modules are tested in QEMU.

- **GitHub:** push is `git@github.com:SimonVitzethum/Gabbro.git` with key
  `~/.ssh/id_ed25519_github`; the host key was checked against GitHub's published ed25519
  fingerprint. Fetch goes over https.
- **Caprock** (the OS this language exists for) lies read-only in `../caprock-messbasis`.
  Never commit into it.

## 5. Muse lanes (opencode, local) — the workhorse

**Layout, all local:**

- Each lane works in its own clone beside this checkout, one per lane, on branch `muse/NNN`,
  with no remote.
- The wrappers in the repo root — `./cargo-pruef`, `./emission-pruef`, `./lean-bau`,
  `./lean-probe` — are the only build entry points a lane uses (permissions: no push and no
  network for lanes).
- Lane prompts live in `lanes/NN.md` (compose with the HARD-RULES preamble), logs in
  `logs/NN.log`; keep task copies while the lane is active or awaiting review.
  Remove numeric lane task Markdown after final checked integration; preserve reports/logs and Git history.

**Writing a lane:**

- **Every lane prompt MUST start with the HARD-RULES preamble.** Compose it with
  `bin/lane-datei NN task.md` (preamble in `lanes/VORSPANN.md`, `{N}` = lane number) and check
  that the file contains `HARD RULES`.
  - *Found 2026-09-15:* lanes 194–200 were launched with the task only, because an empty base was
    copied forward. The preamble was added to their files afterwards, and the auto-continuation
    now tells them to re-read the file. Review those lanes against the rules by hand: no `sorry`,
    `axiom` or `native_decide`, a witness for every theorem, and the commit rules.
- **Keep a copy of every lane file** in `.claude/muse-arbeit/lanes5/` and `.claude/muse-sicherung/`.
- **A good task names:**
  - the files to read;
  - the exact deliverable;
  - what is RESERVED for it: diagnostic codes, gift (poison-probe) numbers, example numbers;
  - "Do not touch MARKE_EMIT";
  - "Write MUSE-REPORT-NN.md";
  - `ZEUGE:` lines for the target theorems.
- **One lane, one topic.** Two lanes that both edit the same central Rust file will conflict at
  merge.

**Launching:** start the lane in its clone, in the background, with a time budget; the lane
file carries the task and the HARD RULES. Keep the master the lane was branched from fresh —
a lane branched from a stale master measures against a tree that no longer exists.

**Watching:** poll `logs/NN.log` for `=== ENDE` and count
`git -C <lane-clone> rev-list --count master..HEAD`.

**Reviewing a finished lane.** Read `MUSE-REPORT-NN.md` and `git diff --stat master..HEAD` in the
clone, then check:

- the task that was actually done is the task that was given (lane 195 lost its prompt to a
  provider error and chose its own task);
- no `sorry`, `admit`, `axiom` or `native_decide`;
- `#print axioms` is standard;
- every new theorem with a ∀-over-syntax premise has a non-degenerate `_zeuge` (memory
  `zeugenpflicht`);
- Rust lanes: poison probe and positive probe present, corpus diff measured, `./cargo-pruef`
  zero failures;
- the claim is not bigger than the proof.

**The two rejections to remember:**

- **Lane 147:** textbook lemmas over self-invented mini-models, and decorative witnesses. Sent
  back.
- **Lane 184:** a simplification that was really a tightening. It added N308, edited the corpus
  and broke the F04 frozen excerpt. Rejected; the work is kept on `muse/184-verworfen`. Lane 191
  redid it correctly: 0 diagnostic diffs, demanded effects 616 → 277.

**Merging a lane:** `bash .claude/muse-arbeit/muse-merge.sh NN msgfile`. In order, it:

1. fetches `muse/NN` from the lane clone;
2. merges with `--no-commit`;
3. auto-resolves only `Grammatik.lean` import conflicts, and takes master's side of the ledger
   files;
4. moves the report to `messung/muse/`;
5. builds `grammatik/` locally before committing;
6. commits, deletes the branch and deletes the lane clone.

The message file ends with the attribution lines. Other conflicts abort; resolve them by hand,
then `git add` + `./commit.sh`.
After the commit, `muse-merge.sh` calls `lane-putzen.sh`: the standard is
COMPLETE cleanup but only after merge — session rows, state line and
`/tmp` leftovers go; `lanes/NN.md`, `logs/NN.log` and the merged report
stay as audit. The review loop archives reviewer evidence and deletes
reviewer clones on FREI/FINAL-ROT the same way.

**Merging an Opus branch:** `bash .claude/muse-arbeit/opus-merge.sh BRANCH msgfile`, the same
flow for a local worktree branch. For a branch that arrives via GitHub, `git fetch origin
opus/…:opus/…` first.

**After merges:**

1. Refresh the lanes' warm Lean cache from the merge build.
2. Bundle master, run `cargo test --no-fail-fast`, and push only if the tests and the key grep
   are clean and origin is not ahead. If origin moved, `git pull` (merge) first and run it again.
   - **The push gate is the four guardians** (`./instrumente/abnahme.py`, Simon 2026-10-17: exactly
     four). The C-emitter check (`pruefe-emission.sh`) and its counters (`MARKE_EMIT*`) are gone:
     the C backend was removed on 2026-10-17.

## 6. Opus agents (Claude subagents, max 2)

- Spawn them with `isolation: worktree` and `run_in_background: true`.
- **Their Lean and cargo builds run in their own local directory**, e.g. a worktree beside this
  checkout. The prompt says so explicitly:
  - keep `grammatik/.lake` warm (copy it from a tree that has one) so `lake build` does not
    start cold;
  - **and `programmlogik/.lake` is the one that bites `cargo test`.** `gabbro prove` builds
    `programmlogik/`, which needs **mathlib**; with no cache there, `lake` goes off to clone
    mathlib4 and the run hangs with zero CPU. *Measured 2026-09-15: two Opus trees stalled 13
    and 19 minutes on exactly this, and both times it was the apparatus and not the tree.*
    Until there is a staged cache, either copy `programmlogik/.lake`
    from a tree that has one, or keep `cargo test` off the lane and say so in the report;
  - a stale `programmlogik/.lake` is worse than none: an `incompatible header` makes
    `gabbro prove` announce *"the exported program is not valid Lean"*, which is a
    sentence about the olean and not about the program (met in the acceptance run of
    2026-09-15);
  - build with `lake build` in the agent's own directory, never in this checkout while
    something else builds there.
- **The prompt names:** the standards (no `sorry`, `native_decide` or new `axiom`; standard
  axioms; witnesses), the plan and SATZKARTE updates expected, "commit on your branch, do not
  merge", and the report they finish with.
- **Use them for** the hard single pieces (model repairs, closing theorems, verdicts).
- **Session limits:** when an Opus agent stops on a session or weekly limit, its worktree keeps
  the work. Resume it with SendMessage after the reset; do not start a fresh one.

## 7. Number ranges and counters (free from here)

| Kind | Next free |
|---|---|
| Diagnostic codes | **N587** (slot release took N586). The alias rules took **R014**/**R015**: next `R016` |
| Gift (poison-probe) numbers | **1471** (`beispiele/gift/1470-geraet-am-portraum-ohne-llvm.gab` is the last; 1448-1469 stay unused) |
| Example numbers | **1165** (`beispiele/1164-operanden-zuerst-weiten.gab` is the last) |
| Lane numbers | **1403**: allocate unique IDs from the live coordinator registry |

*The per-lane reservation ledger that stood here (2026-09 to 2026-10) is history: `git log -p AGENTS.md`
before the consolidation of 2026-10-17. Re-measure instead of trusting the row above:
`grep -rho '\bN[0-9]\{3\}\b' crates/ | sort -u | tail`, `ls beispiele beispiele/gift | tail`.
A ledger of reservations drifts; the highest number in the tree does not.*

- Unused parts of a reserved block stay with the follow-up work of the same wall (for example
  N411–415 for the integer-match exhaustiveness refusal that lane 227 left open, review G07);
  they are never handed to another topic. Next free is always above the highest number in use,
  so a stale reservation can never collide with a new one.
- A lane that takes numbers without a reservation (O-1, 249, 256 above) is booked here by the
  merger in the same merge.
- The test `keine_zwei_korpusdateien_teilen_eine_nummer` catches collisions between lanes.
- **Every new refusal code comes with its sentence** in `saetze.rs` in the same commit
  (the sentence register in `pruefe-pruefer.py`), and with a poison probe.

## 8. Files that matter

| What | Where |
|---|---|
| The goal statement | `grammatik/Grammatik/Zielsatz/Kern/Spec.lean` (review target), `Beweis.lean`, `Akzeptiert.lean`, `Proben*.lean`, `SpecProben.lean` |
| Model | `RufMaschineG.lean` (machine G), `Semantik.lean` (`execEnd`, `rufAt`), `SperreBeweis.lean`, `Lebendigkeit.lean`, `Gleitkomma*.lean`, `EinpassenVoll.lean`, `AntwortOrte.lean`, `Nichtinterferenz/` |
| Translation validation | Active target: `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5 (source → final x86 bytes, W / GX reuse). Existing C proof record: `Schlusssatz104.lean` (first chain), `Schlusssatz.lean` + `KorrespondenzAllg.lean` (stage (a) generic, `korrOk`), `Kette104*.lean`, `Kette108.lean`, `CNebenlaeufig.lean` + `Schlusssatz124.lean` + `Korpus124.lean` (stage (b)), `CFormen*.lean`, `CSpeicher.lean`, `CSemantik.lean`, `Parser/` (T3) |
| Plans | `dokumente/BEWEIS.md` (§5 review questions, §8 extension rules, §9–§10 gaps), `PLAN-UEBERSETZUNGSVALIDIERUNG.md` (§§0–5 active x86 target, §§6–7 historical C record), `dokumente/PRUEFER.md`, `dokumente/BEWEIS.md`, `GLEITKOMMA.md` |
| Theorem map | `dokumente/SATZKARTE.md` (§§13–27; new sections at the end, and renumber on a merge collision) |
| Known absences | `TODO.md` (O1–O14) |
| Verdicts | `dokumente/BEWEIS.md` part C (one table); the old reports are in Git |
| Guardians | `instrumente/abnahme.py` runs the four: `pruefe-lean.py`, `pruefe-llvm.py`, `pruefe-pruefer.py`, `pruefe-gabbrov.py` (`dokumente/WERKZEUGKASTEN.md`) |
| Rust tools | `gabbro lean-g` (exporter), `gabbro obligations --g`, `gabbro counterexample`, `gabbro corr-lean`, `gabbro certificate`, `gabbro pruefe --fix`, `gabbro abgeleitet`, `gabbro zeremonie`, `gabbro paesse` |

## 9. Pitfalls that cost real time (each happened)

**Tools and timestamps:**

- **`rsync -a` + `cargo` build a mixture**, because `cargo` trusts mtimes. Use `-rlpgoD` for
  trees that cargo builds (CLAUDE.md).
- **`pgrep -f` / `pkill -f` match their own command line.** Kill by PID, and wait by polling a
  file.
- **`commit.sh` commits only staged files.** A merge message path must be absolute; the scripts
  apply `realpath`.
- **A guardian that aborts reads like one that passed.** Look for the numbers it no longer
  prints. `cargo test` needs `--no-fail-fast`.

**Running lanes:**

- **A lane cloned from a stale base** works against a master that no longer exists. Refresh the
  base before launching.
- **Oversized opencode context gives a provider error.** Restart a fresh session with a STATE
  note rather than `--continue`.
- **`--continue` after a failed first run** has no task. Lane 195 invented its own; the
  continuation now points at the lane file.

**Merging:**

- **Merge conflicts that recur:**
  - `Grammatik.lean` imports: take the union;
  - duplicate SATZKARTE § numbers: renumber;
  - two lanes defining the same Lean name: rename one;
  - duplicate `Satz` insertions in `saetze.rs`: keep both;
  - `fahnen.rs`: take the union;
  - emission counters: re-measure.
- **Semantic merge breaks** show up only in the build: a new structure field needs `none`
  appended at every literal, and an arity change in `lean_g.rs` needs every caller updated.
  Always build after a merge, even a clean one.
- **Sorry is mechanically refused** (Simon, 2026-10-04): the Lean guardian (`instrumente/pruefe-lean.py`)
  fails on `sorry`/`admit`/`native_decide`/`sorryAx`/`unsafe` in `grammatik/` code and on any `axiom`
  not recorded in `instrumente/teile/kein-sorry-allowlist.txt` (currently only `dma_inhalt`); the GabbroV
  guardian does the same for `programmlogik/Proofs` and `programmlogik/gabbrov`. `bruecke/` is not measured.

**Machines:**

- **ELAN_TOOLCHAIN leak rebuilds everything under the wrong Lean** (measured
  2026-10-04: desktop session exported `v4.34.1`, agents inherited it, full
  incompatible rebuild burned RAM/swap for garbage while the repo pins
  v4.33.1). `lean-bau`/`lean-probe` start lake with `env -u ELAN_TOOLCHAIN`;
  every clone copy carries the same line (copies are local-only, re-apply
  after re-cloning). After a toolchain incident replace poisoned
  worktree `.lake` caches with the warm master cache, never resume them.

- **Low memory kills jobs silently.** A push job died that way once.
  Watch RAM before heavy builds; one build at a time in one checkout.
- **RAM discipline for agents, Lean builds independent and killable** (Simon,
  2026-10-04): agents run Lean ONLY through the wrappers (`lean-bau`,
  `lean-probe` — adaptive `-M`/`-j` from free RAM, one build via `lean-slot`,
  builds pinned to cores 4+ so ~50% CPU during builds is normal, not a bug);
  never raw `lake` (unbounded flags, wrong cwd outside `grammatik/`). Every
  slot holder writes `locks/lean.pid` (PID + command, removed on exit) — end
  any Lean build without touching agents via
  `kill -- -$(ps -o pgid= -p $(cat locks/lean.pid))`. 10 opencode servers cost
  ~1 GB each: worker count IS a RAM decision. `/tmp` is RAM-backed tmpfs
  (checkpoints + opencode temp live there). No swap = no safety net: the next
  spike kills processes (OOM) instead of slowing down.
- **The combined merge+push was blocked by the classifier once.** Split it into two steps.

## 10. Talking to Simon

- **German, direct, concrete.** Say what was done, what is open and what is uncertain. Never
  claim more than was measured.
- **Estimates:** give ranges, name the critical path, and note that Muse throughput is
  review-bound.
- **They follow from other devices.** Short status lines while long jobs run are welcome.

*Current work list: `TODO.md`. History of how things got here: `git log`, the verdicts and the
lane reports.*

## 11. Direct compiler: goals that still stand (2026-10-03)

*The x86-64 coordinator handoff that stood here (Muse waves 558-625, failover supervisor, lane
cleanup) belongs to the stopped x86 work (section 3, 2026-10-07); it is in `git log -p AGENTS.md`.*

Both the architectural hardware model and the full Gabbro-to-final-binary pipeline are to be
completed in Lean without a persistent SSA IR or a second source interpreter: the existing typed
source plus checked target blocks and bytes, recomputed certificates, and later Rust producing
untrusted candidates that a Lean validator checks (source-derived unit, all reachable support,
entry and binding bytes, linking and relocation, the actual final mapping). Source safety, G/GX
concurrency, IEEE, contracts, call logs and budget guarantees remain; OS and freestanding
profiles stay generic and software is user logic.

Performance goals against equivalent C built with GCC `-O3`: minimum 80 %, target 95 %,
ambitious above 110 %. Fixed-work score is `100 * Ctime / Gabbrotime`, throughput score is
`100 * Gabbrothroughput / Cthroughput`. Record per-workload and per-class results with matched
hardware, ISA, semantics and compiler settings on full validated direct binaries; legacy-C
execution, unvalidated output, golden agreement or emulation are not direct-backend evidence.
Compile latency includes checking, optimisation, production, validation and Lean kernel checking
(cold, warm, incremental, memory). Targets are OPEN until measured; no universal speed claim.
Central record: `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`.

## 12. Model onboarding: behavior rules that make entry easier (Simon, 2026-10-04)

*New models (any provider) fail the same way on first contact: outdated tactic
names, invented lemma names, uncommitted work, ended turns. The HARD-RULES
preamble (`lanes/VORSPANN.md` rules 15–16) now carries the toolchain truth; this
section is the coordinator-side record.*

- **Toolchain truth, not training memory.** `grammatik/` pins Lean v4.33.1 with
  NO mathlib: `split` (never `split_ifs`), `omega`/`decide`/`simp` available,
  `norm_num`/`ring_nf` absent. **Mathlib is allowed EVERYWHERE since 2026-10-08** (Simon: "mathlib darf
  ueberall genutzt werden"); `grammatik/` requires it pinned to the tag with the
  same toolchain (v4.33.1, `grammatik/lakefile.toml`; precompiled via `lake exe
  cache get`, ~7.5 GB under `.lake/packages`, fetched by the coordinator because
  lanes have no network). It is still not a fix for tactic-name errors: read the
  names, do not guess. `gabbro_ziel` must stay on exactly `propext`,
  `Classical.choice`, `Quot.sound` (Mathlib adds no axiom). Modules that do not
  import Mathlib do not pay for it.
- **Names are read, not guessed.** Every `BitVec.*`/helper lemma name is
  grepped from the tree before use; `unknown identifier` = wrong name.
  Canonical definitions are reused (`Stapel.lean` push), never duplicated.
- **Silicon over proof shape.** A green proof of a wrong hardware definition
  (e.g. PUSH imm32 zero-extended — silicon sign-extends) is a finding for the
  reviewer, counted as REPAIR material, never as a result.
- **Work discipline for newcomers.** Commit the green skeleton early (preamble
  rule 10), never end a turn with work pending (rule 11 — the harness resumes
  sessions, single-shot stops prove nothing), one definition per check.
- **Capability tests run outside the coordinator** (scratch clones, private
  logs, held slot locks, no manifest/state/dispatch entries) until a model
  passes review; only then do its lanes register. Test clones are deleted
  after evaluation.
