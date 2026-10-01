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
  (`grammatik/Grammatik/Zielsatz/Spec.lean` is the statement, `Beweis.lean` the proof) has been
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

- **Target portability** (Simon, 2026-10-01): the direct x86-64 compiler must
  support extensible profiles for arbitrary operating systems and freestanding
  environments. Keep source semantics, IR, optimisation and validation generic;
  describe ABI/image/entry requirements in checked profiles and implement
  environment services in Gabbro bindings with user-logic proof obligations.
  No implicit Linux/POSIX/libc/ELF dependency. Freestanding has no mandatory
  host runtime or dynamic loader. Every selected profile retains complete
  final-byte, entry, support-code and mapping validation. This is a requirement,
  not a claim that these targets are implemented.

- **Direct compiler progress record** (Simon, 2026-10-01):
  [`DIRECT-COMPILER.md`](DIRECT-COMPILER.md) is the central
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
- **Proposed friend optimiser ownership:** `grammatik/Grammatik/X86/OptimizationRules.lean`
  and `OptimizationWitnesses.lean` are reserved for the friend handoff. Muse lanes
  do not edit these paths; reuse the one accepted IR and wait for its frozen interface.
  The complete planned optimiser specification belongs in `grammatik/OPTIMIZER.md`.
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
- **Simplicity is a goal, but no guarantee is given up for it** (PLAN-EINFACHHEIT.md). The measure
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
`programmlogik/`, `lean.rs` and `beweis.rs`; task `dokumente/AUFTRAG-GABBROV-VERIFIKATION.md`) on
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
2. Bundle master, run `cargo test --no-fail-fast` and the emission check, and push only if
   tests, emission and key grep are clean and origin is not ahead. If origin moved,
   `git pull` (merge) first and run it again.
   - Do NOT run it with `EMISSION=true`.
   - Emission counters (`MARKE_EMIT`, `MARKE_EMIT_G`, `MARKE_EMIT_M` in
     `instrumente/pruefe-emission.sh`) are re-measured by the merger, not by lanes. Each bump is
     dated with its reason.

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
    `pruefe-lean-programm.sh` announce *"the exported program is not valid Lean"*, which is a
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
| Diagnostic codes | **N578** (highest issued: N577, C-free lane, 2026-10-01; **N569/N570 are taken by the network lane** (`region.leeren`, `static.ausrichtung`; committed 2026-09-30)) |
| Gift (poison-probe) numbers | **1398** (highest file: `beispiele/gift/1397`, C-free lane; **1371-1374 are taken by the network lane** (committed 2026-09-30), 1375-1379 left free for it) |
| Example numbers | **185** (highest file: `beispiele/184`, C-free lane; **175 is taken by the network lane** (`175-puffer-gibt-seiten-zurueck`, committed 2026-09-30), 176-179 left free for it) |
| Lane numbers | **644** next free; allocate unique IDs from the actual live coordinator registry. |

*Ledger re-measured **2026-09-28** (server lane) the same way — `grep -rho '\bN[0-9]\{3\}\b'
crates/ | sort -u | tail`, `ls beispiele beispiele/gift`. **It was stale again**, and by more
than last time: it read N466 / 1171 / 158 while N466 itself was already taken (lane 259's
`R-commit`) and Opus lanes had reached N568, gift 1363 and example 165. Three registers over
one thing, and the one nobody reads is the one that drifts.*

*Ledger re-measured 2026-09-21 (review G13) by grepping `crates/` for issued `N` codes and
listing `beispiele/` and `beispiele/gift/`. The row above was stale from 2026-09-17 to that
day: it still said N391 / 1052 / 147 / 221 while N446–N455 and gifts up to 1127 were in use.
What was reserved in TODO §-1/§0 and what was actually taken:*

| Lane | Reserved N / gift / example | Taken |
|---|---|---|
| 221 | N391–395 / 1052–1056 / — | gifts 1052, 1053; no code |
| 223 | N396–400 / 1057–1061 / — | gifts 1057, 1058; no code |
| 225 | N401–405 / 1062–1066 / — | gifts 1062–1066; no code |
| 226 | N406–410 / 1067–1071 / 149–150 | gifts 1067, 1068; examples 149, 150; no code |
| 227 | N411–415 / 1072–1076 / — | gifts 1072–1076; no code. **Fix lane F1 (2026-09-21) took N411–N414** from this block for the integer-match coverage refusal (gifts 1128–1131 from the free range); N415 stays with the wall |
| 229 | N416–420 / 1077–1081 / 151 | gifts 1077, 1078; no code; example 151 went to lane 237 |
| 232 | N421–425 / 1082–1086 / — | N421, gift 1082 |
| 236, 237 | — / — / 147–148, 151–152 | examples 147, 148, 151, 152 |
| 240 | N426–430 / 1087–1091 / — | gift 1087; **N426 and gift 1088 were taken by lane 257** from this block |
| 242 | N431–435 / 1092–1096 / 153–154 | examples 153, 154; no code, no gift |
| 245 | N436–440 / 1097–1101 / — | gifts 1097, 1098; no code |
| 246 | N441–445 / 1102–1106 / — | nothing |
| O-1 (Opus) | **not reserved** | N446–N450, `C185`, gifts 1107–1112, examples 155, 156. **Gift 1112 removed 2026-09-26** (merge of lane 260): it pinned `C185` on the shape of 155, which lane 260 now lowers, so it no longer falls; 155 carries the shape as a positive. **Gift 1114 moved to `beispiele/1114-kind-handed-read.gab`** in the same merge: its only expected line was `C185`; the legal handed read is now a positive |
| 249 | **not reserved** (TODO row says "—") | N451, N452, gifts 1113–1117 |
| 256 | **not reserved** | N453–N455 (the spare of the block N451–455 that lane 249 chose itself), gifts 1118–1127 |
| Fix lane F2 | **not reserved** (free range) | gifts 1132–1138; no code (`N426` and `N211` tightened, not minted) |
| Fix lane F3 | **not reserved** (free range) | N456, N457, gifts 1139–1147; no example (`N450`/`N451` tightened, not minted) |
| Fix lane F4 | **not reserved** (free range) | N458–N462, gifts 1148–1154; no example (`LG001` reused for repeated starts in the exporter) |
| Fix lane F5 | **not reserved** (free range) | N463, N464, gifts 1155–1158; no example (examples 96/149/150 edited to the new buffer clause) |
| Fix lane F6 | **not reserved** (free range) | N465, gifts 1159–1168; no example (gift 1125 turned from clean side to `N454`, renamed `1125-index-in-max-ohne-laenge`) |
| Fix lane F7 | **not reserved** (free range) | gifts 1169, 1170; no code, no example (`E011` tightened, `LG005` reused for a binding covering a carrier in the exporter; examples 09/147/148 edited) |
| Fix lane F10 | **not reserved** (free range) | example 157; no code, no gift. **`N315` retired** (idle duplicate start, admitted since the goal covers pools) and **gift 976 removed** with it; `LG001` for repeated starts lifted in the exporter |
| Fix lane F11 | **not reserved** | nothing: no code, no gift, no example (`H102` unchanged; the work is the Lean leg `keinKernHalt`) |
| Opus lane O25 (2026-09-26) | N481–N485 / 1201–1210 / — | N481–N483 (`namen.sperrprimitiv_ordnung`, OFFEN O26), gifts 1201–1203; no example. **Opus lane O25b took N484** (`wirkungen.vertrag_atomar`, a contract over a shared atomic) **and gift 1204**; N485 and gifts 1205–1210 stay with the O25 wall (the payload rule). **Opus lane O25c** took nothing from the block (the payload rule stays open); it added **example 162** (`beispiele/162-geteilte-flagge.gab`, not reserved: the first certified program with a shared atomic) |
| Opus agent D (invariants) | N496–N500 / 1231–1240 / — | N496, gifts 1231–1234; no example (examples 09 and 17 edited: 09's false invariant replaced, both now `maintain`); N497–N500 and gifts 1235–1240 stay with the invariant work (OFFEN O11's `ops` condition) |
| Opus agent E (linking) | N501–N505 / 1241–1250 / — | N501–N505 (`namen.verbund`); probe numbers 1241–1245 as LINK probes under `messung/proben/verbund/` (a link probe is two units, each clean alone, so not a `beispiele/gift/` file); no example. Gifts 1246–1250 stay with the linking work |
| Opus agent F (link races) | N516–N520 / 1246–1250 / — | N516 (`namen.verbund`, a module split over two units); link probes 1246–1248 under `messung/proben/verbund/` (pairs `NNNN-…-bib.gab` + `NNNN-…-app.gab`); no example. N517–N520 and 1249, 1250 stay with the linking work |
| Opus agent G (OFFEN O1) | N531–N535 / 1291–1300 / — | N531, N532 (`kbedingung.breaking-rests-here`, `kbedingung.breaking-blocks-maintainers`), gifts 1291, 1292; no example. N533–N535 and gifts 1293–1300 stay with the O1 work (the name of `breaking` in G, path-sensitive order) |
| Opus agent H (OFFEN O19) | N551–N555 / 1331–1340 / — | nothing: no code, no gift, no example (`H102` unchanged; the refused shape is `gift/460`, and the Lean side is the component `maskenB` and the leg `KernHaltE`). N551–N555 and gifts 1331–1340 stay with the O19 work |
| Opus agent I (bare metal, OFFEN O32) | N556–N560 / 1341–1350 / — | nothing: no code, no gift, no example (the work is the runtime `laufzeit/metall/`, the generated `<unit>.metall.c` and the QEMU stage `instrumente/pruefe-metall.sh`; its gifts are harness mutations, not corpus files). N556–N560 and gifts 1341–1350 stay with the O32 work |
| Opus agent J (freestanding, OFFEN O32/O33) | N561–N565 / 1351–1360 / — | nothing: no code, no gift, no example (the work is stage 12 `instrumente/pruefe-freistehend.sh`, the metal entries/arena/core limit in `laufzeit/metall/`, `gabbro build`'s `metal` link, and new QEMU images whose gifts are harness mutations). N561 is the named candidate for the entry-binding check (O32 (7)); N561–N565 and gifts 1351–1360 stay with this work |
| Opus agent L (OFFEN O31 + O32 residue) | N561–N570 / 1351–1370 / 163–165 | N561 (`eintritt.bindung`), N562–N567 (`syscall.zielbindung`), N568 (`namen.verbund`, link: one kernel); gifts 1351–1363; examples 163 (system-call variables, two targets), 164 (metal only, the program's own kernel entry), 165 (an entry on #GP through the error-code twin stub). N569, N570 and gifts 1364–1370 stay with the O31 work. Also: one new word `target` (`MARKE_WOERTER` 244 → 245), probe program `sonden/sonde_metall_systemruf.c` (`MARK_QUOTE` (21, 54) → (22, 55)) |
| Server lane, phase 2, session 25 (M-ALLTAG C, memory discipline; `~/gabbro-netz` `docs/ALLTAG-C-ENTWURF.md`) | **N569–N570** / **1371–1374** / **175** | `N570` (`static.ausrichtung`: `aligned N` on a `static` that is no constant power of two; gift 1374; the clause lets a ring buffer sit on page boundaries); `N569` (`region.leeren`: `reset X at i count n;` on something that is no zero-initialised `static mut` array); gifts 1371 (`N569`, a scalar as the carrier), 1372 (`M103`, a range past the end), 1373 (`E005`, the store without `writes X`); example 175 (clean, emits, runs as `beispiel175` / `beispiel175-gebunden`). The statement gives a range of a static buffer back: it reads as zero and whole pages go back through the program's weak `gabbro_os_leeren` (`bibliothek/linux/linux.c`, `linux.gab` `os_bindung_null` widened by one clause). No arena change: **an arena slot is write-once, so the give-back had nothing to say there** (the first attempt, `reset A at i`, was built and thrown away for that reason). Measured by `instrumente/pruefe-seiten-zurueck.sh` (RSS 2504 -> 1608 KiB, unbound stays, poison caught). Numbers 1375-1379 and 176-179 stay free for the network lane (the C-free lane reserved them); the global next-free is the §7 table |
| Server lane, phase 2, session 22 (walls 5 and 9 of `~/gabbro-netz` `docs/WAENDE-M1.md`) | **not reserved** | **no code**: the annotation on `let … else` is HONOURED (`ast::LetSonst.typ`, checked in `m1.rs` against the callee's answer with the existing `M101`/`M135`), and a `narrow` is lowered by its own function's declarations of the name (`emit.rs`, `vorzeichenlose_namen_hier`). Gifts **1369** (`M101`), **1370** (`M135`); examples **170** (`let … else` with a range), **171** (the `narrow` next to a signed name) |
| Server lane, phase 1 (TODO §0e) | **not reserved** | **nothing**: no code, no gift, no example. What it added instead: the instruments `instrumente/miss-arena-decke.sh` (H4, the ceiling against the cost) and `instrumente/pruefe-kernelmodul.sh` (a Gabbro unit as a Linux kernel module, QEMU only); the runtime `laufzeit/kmodul/` (`kmodul.c`, `arena.c`, `kmodul.h`, `include/`); the probes `messung/proben/arena-h4/ceiling-{10mib,32gib}.gab` and `messung/proben/kmodul/{halde-treiber.gab,melde.c}`; one CLI test (`der_link_ohne_with_leitet_die_schnittstellen_ab`). The poison probes of both instruments are HARNESS mutations (`--gift`), not `beispiele/gift/` files, so they take no gift number |
| Server lane, phase 1, session 2 (TODO §0e, acceptance point 2) | **not reserved** | **nothing**: no code, no gift, no example. What it added instead: the instrument `instrumente/pruefe-nebenlaeufig-zwilling.sh` (the emitted C of a concurrent program against a HANDWRITTEN C twin, called as stage 22b of `pruefe-emission.sh`), the probe `messung/proben/nebenlaeufig/` (`sperre-rueckgabe.gab` + `sperre-rueckgabe-hand.c` + `treiber.c`), one cargo test (`der_wert_wird_unter_der_sperre_gelesen`), and the emitter repair it found: a `return <expr>` inside `locks` released the lock before evaluating the expression (`emit.rs`, the `Return` arm; 12 of 317 emitting files change). `MARKE_EMIT_M` 156 → 157. **Also K4** (the same session): the manifest word `kmod <runtime dir> <kernel build dir>` and the third art `unit <name> module <init> <exit>` in `crates/gabbro-cli/src/bau.rs` (`modulregel`, `kmod_modul_binden`), `#define GABBRO_ARENEN` in the emitter, the shared binary-choice register `instrumente/binaer.sh` (with its speech probe in `pruefe-waechter.py`), 6 CLI tests in `bausystem.rs`. The instrument's poison probes are HARNESS mutations (`--gift`), not `beispiele/gift/` files, so they take no gift number |
| Server lane, phase 1, session 4 (TODO §0e, K3's C half) | **not reserved** | gift **1364** (`eintritt-via-anderem-pfad`) and example **166** (`eintritt-irq-maskiert`) -- the twin witnesses of ONE widening: `H102`'s trigger is a `via` word, any of them, instead of the literal `idt` (a misspelt path and a host kernel's interrupt path both disarmed it in silence). **No `N` code:** `H102` keeps its name and its sentence, and what moved is the trigger, which the sentence now states with its measurement. Also added, and none of it takes a number: `laufzeit/kmodul/sperre.h` (the module target's lock primitives -- `masks irqs` is `raw_spin_lock_irqsave`), the generated `sperren.h` from `bau.rs::sperrenliste` (the same lock register the hosted and bare-metal drivers read), the probe `messung/proben/kmodul/{sperre-takt.gab,takt.c}`, a second probe in `instrumente/pruefe-kernelmodul.sh` with three more harness mutations (`--gift 5..7`, so no gift numbers), 3 unit tests in `bau.rs` and 1 CLI test in `bausystem.rs`. Emission counters: `MARKE_EMIT` 142 → 143, `MARKE_EMIT_M` 157 → 158 |
| Server lane, phase 1, session 3 (TODO §0e, H3 + the `atomic` refusal) | **not reserved** | **nothing**: no code, no gift, no example. What it added instead: the Lean section `Form` of `grammatik/Grammatik/ArenaDyn.lean` (`DynForm`, `Block.dynGrowB`, `Block.dynAlloc`, the four PLAN-DYNAMISCH §9 theorems, the simulation `dynAlloc_simuliert`, the witness namespace `DynZeuge`); a COMMENT-ONLY diff of `grammatik/Grammatik/Zielsatz/Spec.lean` (two new entries in THE ONE LIST under (d), `Laufzeit.reserve` and `Laufzeit.commit`, plus one NOT CLAIMED clarification -- 36 insertions, 1 deletion, no definition and no premise moved) with its review `messung/SERVER-0E-SPEC-DIFF.md`; the build-time refusal of an `atomic` in a `module` unit (`crates/gabbro-cli/src/bau.rs`: `AtomarFund`, the atomic arm of `sammle`, the new head of `modulregel`) with 1 CLI test (`ein_modul_mit_atomic_faellt`, with its positive twin); `dokumente/OFFEN.md` **O34** (what lifting that refusal needs). A manifest-level refusal has no `Satz`, so it mints no `N` code -- the same reading `treiberregel` and the module rule already stand on |
| Server lane, phase 1, session 5 (TODO §0e, K6) | **not reserved** | **nothing**: no code, no gift, no example. A LIFTED refusal keeps no `Satz`, so it mints nothing -- session 3's blanket refusal of an `atomic` in a `module` became the refusal of a FLOATING-POINT one, and the rest is a lowering. What it added instead: `laufzeit/kmodul/include/stdatomic.h` rewritten from a refusal into the mapping (the emitter's nine C11 call forms onto `READ_ONCE`/`WRITE_ONCE`, `smp_load_acquire`/`smp_store_release`, `smp_store_mb` and the `try_cmpxchg` family, one row per ordering); the instrument `instrumente/pruefe-atomar-zugriffe.py` (token-level, stage 22c of `pruefe-emission.sh`, its own `--selbsttest`); a third probe `atomar` in `instrumente/pruefe-kernelmodul.sh` with the mapping-expansion stage and three more harness mutations (`--gift 8..10`, so no gift numbers); the probe `messung/proben/kmodul/{atomar-faeden.gab,atomar.c}`; a module's `concurrent` roots as kernel threads (`TreiberPlan::art`, `bau.rs::wurzelliste` -> `wurzeln.h`, `laufzeit/kmodul/kmodul.c`); the comment-only `Spec.lean` block **(M11)** (47 insertions, 0 deletions) with its review `messung/SERVER-0E-SPEC-DIFF.md` Part II. 3 unit tests in `bau.rs` and 1 CLI test in `bausystem.rs`. Emission counter: `MARKE_EMIT_M` 158 -> 159; README guardian count 50 -> 51. **And K7's measurement half** (same session): the stage `symbole_pruefe` of `pruefe-kernelmodul.sh` -- what the module RUNTIME still takes from the kernel, `nm -u` on the `.ko` intersected with the runtime objects', as a per-probe ratchet (4 / 7 / 9, twelve distinct names) with gift 11 as its poison probe -- and OFFEN **O35**, which is that list and what closing it needs |
| Server lane, phase 1, session 6 (TODO §0e, K7) | **not reserved** | **nothing**: no code, no gift, no example — and this time the reason was a decision and not a habit. Session 5's plan had reserved **N569** for the K7 refusal; it was not taken, because the rule is about a MANIFEST and a `Satz` says what is true of a program the CHECKER passed (`eintrittsregel`'s reading, `bau.rs`). Next free is unchanged: **N569 / 1365 / 167**. What it added instead: `laufzeit/kmodul/bindung.h` (the interface between the module runtime and the program's binding — twelve declarations, no definition, so the twelve kernel names of OFFEN O35 are the program's); `bibliothek/linux-kmod/{linux-kmod.gab,linux-kmod.c}` (the binding a program takes off the shelf — **a new top-level directory, and the seventh booked emission root**, `MARKE_EMIT_BIB=1`); `bibliothek/linux-kmod/stdatomic.h` (the K6 atomic table, moved out of the runtime — 160 macro lines byte-identical — while `laufzeit/kmodul/include/stdatomic.h` became a refusal again); `bau.rs::bindungsregel` plus a new manifest file kind (a `.h` in a `module` unit's file list, copied into the module's include directory in place of the runtime's shim); harness gift **12** in `instrumente/pruefe-kernelmodul.sh` (a `--gift` run, not a `beispiele/gift/` file) and a repair of gift 11's anchor; 3 CLI tests in `bausystem.rs`. `Zielsatz/Spec.lean`: **5 insertions, 2 deletions, comment only** (the path in (M11) and a parenthesis), reviewed in `messung/SERVER-0E-SPEC-DIFF.md` Part III. `instrumente/pruefe-sondendeckung.py`: `MARK_AUSSEN` 13 → 23, stale since 2026-09-04 (8 of the 10 predate this session). Emission counters: `MARKE_EMIT`, `-G`, `-M` UNCHANGED (no emitted byte moved); README guardian count unchanged (no new instrument) |
| Server lane, phase 1, sessions 7+10 (TODO §0e, K8's measurement) | **not reserved** | **nothing**: no code, no gift, no example — a measurement mints nothing, and the one repair it found is a defect in a GENERATED artefact, which no `Satz` speaks about. Next free unchanged: **N569 / 1365 / 167**. What it added instead: the instrument `instrumente/pruefe-os-bindung.sh` (what the HOSTED runtime takes from the OS, K7's per-object criterion over a built binary, plus the raw-`syscall` stage `nm` is blind to, plus the bare-metal half K8 asks for; `MARKE_OSSYM=12`, `MARKE_ROHRUF=3`, 5 harness gifts, so no `beispiele/gift/` files); the probe `messung/proben/os-bindung/{os-probe.gab,melde.c}`; and the defect it found — **neither generated driver reserved the unit's dynamic arenas**, so a hosted or bare-metal unit with an `arena … max` ran with `base == NULL` and a silent dead heap (`crates/gabbro-cli/src/treiber.rs::arenen_reservieren`, `GENERATOR_KENNUNG` `treiber-gen-4` → `-5`, 1 unit test). Counters: `MARKE_EMIT_M` 159 → **160** (the new probe emits), `MARK_AUSSEN` 23 → **24** (`sonde_os_probe_melde`), README guardian count 51 → **52**; `MARKE_EMIT` and `-G` unchanged |
| Server lane, phase 1, session 10 (TODO §0e, K8's first slice) | **not reserved** | **nothing**: no code, no gift, no example. The refusal it adds is about a MANIFEST, which no pass ever sees, so it has no `Satz` — the reading session 6 wrote down. Next free unchanged: **N569 / 1365 / 167**. What it added instead: `laufzeit/bindung.h` (the hosted interface — six declarations, no definition) and `bibliothek/linux/{linux.gab,linux.c}` (the binding a hosted program takes off the shelf; `bibliothek/`'s SECOND unit, `MARKE_EMIT_BIB` 1 → 2); `laufzeit/arena_dyn.c` rewired to call only bound names (`mmap`, `mprotect`, `sysconf`, `fprintf`, `exit`, `abort` gone); `bau.rs::bindungsregel_gehostet` + the shared `bindung_pruefe`/`BindungsZiel` (one check for both targets, `W7`); `gabbro build` compiling a NON-MODULE unit's own `.c` bodies into `<unit>.fremd<N>.o` and linking them into a `program` (the restriction that stood there was lifted, and its test turned into its positive twin); harness gift **6** in `instrumente/pruefe-os-bindung.sh`; the repair of `instrumente/binaer.sh` (a newer TEST file no longer calls the binary stale — session 6's finding 9); 3 CLI tests in `bausystem.rs`. `MARK_AUSSEN` 24 → **26** (`sonde_os_bindung`, `sonde_os_null`). `MARKE_OSSYM` 12 → **7**, which is the measurement of the slice. `MARKE_EMIT`, `-G`, `-M` unchanged — no emitted byte of any existing unit moved |
| Server lane, phase 1, session 11 (TODO §0e, K8's second slice) | **not reserved** | **nothing**: no code, no gift, no example. The refusal it widens is the MANIFEST rule of the row above, which has no `Satz` — next free is unchanged: **N569 / 1365 / 167**. What it added instead: the generated hosted driver's seven OS names became the program's (`crates/gabbro-cli/src/treiber.rs::erzeuge` — `pthread_create`, `pthread_join`, `pthread_mutex_lock`/`_unlock`, `pause`, `fprintf`, `abort`), and with them the per-root adapters and the never-spawned idle root `ruhe`; `laufzeit/bindung.h` + `bibliothek/linux/{linux.gab,linux.c}` grew the lock trio, the thread pair and two report codes, plus the named assumption `os_bindung_faden`; `bau.rs::bindungsregel_gehostet` grew the rows, hung off the DRIVER and not off the lock word; the pin scanner became `treiber.rs::faden_start_zaehlung` (`gabbro_os_faden_start`, the shape the bare-metal driver already had); harness gift **7** in `instrumente/pruefe-os-bindung.sh` (a binding of the wrong ARITY) and a repair of gift 1's anchors; `instrumente/pruefe-atomar-zugriffe.py` now reads `binaer.sh` instead of its own copy (session 10's finding, in a second register); 1 CLI test in `bausystem.rs` and 2 unit tests in `treiber.rs`. Counters: `MARKE_OSSYM` 7 → **0**, `MARK_AUSSEN` 26 → **27**, `GENERATOR_KENNUNG` `treiber-gen-5` → **`treiber-gen-6`**. `MARKE_EMIT`, `-G`, `-M`, `-BIB` and the README guardian count UNCHANGED |
| Server lane, phase 1, session 11 (TODO §0e, K8's LAST slice) | **not reserved** | **nothing**: no code, no gift, no example — and no build row either, which is the one decision worth reading: the trigger for the last pair would be a run-time `start` EXPRESSION, which `modulkarte`'s walk over ITEMS does not see, and a text scan for it would be a second register over what the checker already knows (`fusswache2::startet`). Next free unchanged: **N569 / 1365 / 167**. What it added instead: `laufzeit/faden.c`'s three raw `syscall` sites (`clone`, the child's `exit`, `futex`) became `gabbro_os_klon`/`gabbro_os_wort_warte` in `bibliothek/linux/linux.c`, with the named assumption `os_bindung_klon` (the three promises about the join word, and their ORDER); a FOURTH stage `gehostet_pruefe` in `instrumente/pruefe-os-bindung.sh` that reads the SOURCE of every file in `laufzeit/` — `nm` sees only what a binary LINKS, and its first run found **31 OS calls** in `start.c`/`start_pool.c`, which nothing links; both hand drivers bound, their idle roots and root adapters dropped, and `start.c`'s 124 observation moved into the test (`BEOBACHTUNG_124`, appended at the same `NACHLAUF` marker as the generated driver's, so both artefacts carry it character for character); harness gift **8** and a rewrite of gift 2; `-pthread` removed from `pruefe-emission.sh`'s five compile lines (`-D_REENTRANT` makes glibc set `_POSIX_C_SOURCE` to `199506L`, and the 158 driver's included `linux.c` then redefines it). Counters: `MARKE_ROHRUF` 3 → **0**, `MARK_AUSSEN` 27 → **28**. `MARKE_OSSYM` stays 0; `MARKE_EMIT`, `-G`, `-M`, `-BIB`, `GENERATOR_KENNUNG` and the README guardian count UNCHANGED |
| Server lane, phase 2 (`~/claude-lane/AUFTRAG-2.md`, wall 1 of the network stack) | **not reserved** | gifts **1365**, **1366** and example **167** — the three witnesses of ONE widening: **`reason` becomes the thirteenth item kind that carries `pub`**. **No `N` code:** the rule that speaks is `N038` (the closed export hull) and `N025` (the module boundary), and both keep their names and their sentences; what moved is the GRAMMAR, which had no word for the one thing an exported signature could name and not explain. Measured cost of the gap: `pub fn f() -> T or R` was unwritable in any spelling (`P041` with the word, `N038` without it), so **no function with an error channel could leave its module** — which is every OS call of the phase-2 stack (`~/gabbro-netz/docs/WAENDE-M1.md`, wall 1). Files: `ast.rs::Reason.oeffentlich`, `parse.rs` (the `pub` list and `reason(oeffentlich)`), `bindung.rs::ausgefuehrter_name` (the `Reason` arm moved out of the no-`pub` group), `namen.rs::sichtbarkeit` (the `Reason` row in the map — the widening is also a STRENGTHENING: a `reason` can be private now, and `gift/1365` is the `use` on one that used to pass in silence), `dokumente/SYNTAX.md` (`reason = [ "pub" ] …` plus §9's note), the sentences `parser.pub-nur-wo-die-grammatik-es-fuehrt`, `namen.modulgrenze` and `namen.ausfuhrhuelle`. Counters: `MARKE_EMIT` 143 → **144** (example 167 emits; both gifts are refused by the checker and write no C, so `MARKE_EMIT_G` stays 18). Nothing else moved |
| Server lane, phase 2 (the pointer-index blind spot, found while writing the stack's byte readers) | **not reserved** | gifts **1367**, **1368** and example **168**. **No `N` code:** the rule is `M101`, which keeps its name and its sentence — what moved is one `match` arm in `umgebung.rs::typ_von_ort`, so that `p[i]` on a pointer answers the POINTEE instead of `Typ::Unbekannt`. The arm matched on `durchgreifen()`, which follows a pointer to its pointee, so a `ptr<…> u8` arrived already as `Ganzzahl`, matched no `Typ::Feld` and took the catch-all: *a rule that reads like it is about indexing and runs as a rule about arrays.* Measured before the repair, release binary of `f55b4713`: `return buf[v];` typed `bool`, `u8 in 0 .. 3` and `u32 in 0 .. 1` in three files, all 0 errors; and `buf[0] = wert;` with `wert : u64 in 0 .. 65535` into a `ptr<normal, w> u8` — **a truncating store with 0 errors**, which `m1.bereich` says cannot reach the emitter. Blast radius, measured: `cargo test --no-fail-fast` 1433 passed 0 failed with no file edited; over the whole tree 7 files gain type coverage (12 expressions: `gift/764`, `765`, `784`–`786`, `messung/k3-fragmente/K01`, `K04`), and **0 of the 146 `beispiele/` files change at all** — no example indexes a pointer, which is why the hole could stand. Second yield: with `buf[v] : u8` the widening conversion carries 0 .. 255 through (`umwandlung_ruf` already kept a source range where the source HAD one), so the byte readers need no dead `narrow` per byte and reach 100 % M1 coverage. Counters: `MARKE_EMIT` 144 → **145** (example 168 emits; both gifts are checker-refused, `MARKE_EMIT_G` stays 18) |
| Server lane, phase 2 (the unsigned-name set's SCOPE, found three times while writing the stack) | **not reserved** | example **169**, and **no gift and no `N` code** — because this repair adds no refusal: what changed is WHICH comparison the emitter writes. The policy stands unchanged (*Unwissen faellt nach lautstark* — where the type is unknown the lower `narrow` check is emitted and the guardian goes red rather than a check vanishing quietly); what was wrong is the SCOPE. `emit.rs`'s third collector built `namen.vorzeichenlos` over the whole UNIT and keyed by BASE NAME, and two kinds of declaration landed in it that are not statements about the sign of a number: **a pointer** (`vorzeichen` answers `None`, so `netz::bytes::gleich(a : ptr<normal, r> u8, …, b : ptr…)` knocked `a` and `b` out for every function in the unit) and **a `let` with no declared type** (`let hoch = u32_klein(TIMESPEC, 4);` in `netz::os::linux::jetzt_ns` made `narrow hoch` unbuildable in `netz::eth::eth_adr_schreiben`, three modules away). Measured in `~/gabbro-netz` (`docs/WAENDE-M1.md` wall 6): **three correct programs refused**, each at a line that could not help it, and the giveaway was that `c` and `d` four lines below the refused `narrow a` came out right. *A name was a unit-wide resource and nothing said so at its declaration.* The same commit closes **wall 4** of that file from the same place: `StmtArt::LetSonst` has no `typ` field at all, so it now reads the declared result type of the function it unpacks — the source `let_tyexpr` already answers for the local types beside it, so no second register (W7). Files: `crates/gabbro-check/src/emit.rs` (one collector), `crates/gabbro-check/tests/rechenwerk.rs` (one test, four assertions — the fourth is the half that does NOT move: a signed value keeps its `>= 0`, read both from a declared type and through a result type), `beispiele/169-narrow-neben-einem-zeiger-desselben-namens.gab` (refused in four places by `df7c1812`, builds here), `grammatik/Grammatik/Zertifikat/REGISTER.txt` (regenerated: 169 is `UNCERTIFIED LG002`, the pointer target, exactly like 168). Counters: `MARKE_EMIT` 145 → **146** (example 169 emits; no gift, so `MARKE_EMIT_G` stays 18), freestanding 327 → **328**. Walls measured green in this order: `cargo test --no-fail-fast` **1434 passed, 0 failed**; `pruefe-emission.sh` **ALL PASS, 51 durchgestochen, 328 von 328**; `grammatik` `lake build` **356 jobs** and `gabbro_ziel` on exactly `propext, Classical.choice, Quot.sound`; `pruefe-saetze.py` ratchet **55 unchanged**. **Isabelle is not installed on this machine, so `abnahme.py --voll` was NOT run** |
| C-free lane (`~/gabbro-c`, `lane/c-frei`, C1 + the Lean debt, 2026-09-30) | **not reserved** | examples **172** (`prozess-ohne-libc`, a `nolibc` process with its own `write`/`exit_group` gates), **173** (`abbruch-ohne-libc`) and **174** (`tor-im-modell`, the first CERTIFIED program that calls the kernel); **no gift and no `N` code** -- the `nolibc` entry rule is a MANIFEST rule (`bau.rs::eintrittsregel`, no `Satz`, the reading of session 6), and the exporter's new refusals are `LG` codes. What it added: the exporter carries a `syscall` gate as `D.Ax` and an `assume` as `D.Annahme` (`lean_g.rs::read_gate`, `tr_gate_stmt`), refusing the fallible gate (LG007), gate `requires`/`ensures` (LG003), gate writes and `kernel` pairings (LG001) and an answering gate in an `Endblock` (LG004) by name; two PROVED templates `tor.nie` and `start.nolibc` (`grammatik/Grammatik/SchablonenOhneLibc.lean`, register 21 -> 23 entries, 10 -> 12 machine-checked); an emitter repair: an infallible gate with a value no longer gets the `_wert` out-parameter of the channel form (its call was a C error) |
| C-free lane, the pointer-index hole (OFFEN **O36**, 2026-09-30) | **not reserved** (N569/N570 were already taken by the network lane) | **N571** (`zeiger.index_in_der_ausdehnung`: an index through a pointer is held against the extent its function's `requires` names), gifts **1380** (no extent), **1381** (an index behind a constant extent), **1382** (`N463` widened: a constant clause over a one-byte array); example **180** (the accepted shapes). `N463` widened to every non-bare clause form (no new code). Gifts `764`, `784`-`786` gained the clause they lacked, `765` lost its `p[1]` twin |
| C-free lane, `Endblock.bindAxiom` (NEEDS OPUS item 2, 2026-09-30) | **not reserved** | example **181** (`gate-at-top-level`, CERTIFIED: a value gate bound at the top level of a body, a unit body ending in a `-> never` gate); **no code, no gift** -- nothing new is refused: the exporter's LG004 for a gate at the top level is LIFTED, and the one shape still without a form (a `-> never` call ending an `else` that must not fall off) keeps an `LG` refusal. The Lean side: `Endblock.bindAxiom`, machine rule `endeBindAxiom`, two `RestHalt` arms in `Zielsatz/Spec.lean` (header block "end-block gate"), SATZKARTE §61 |
| C-free lane, the reason channel `bindAxiomElse` (NEEDS OPUS item 1, 2026-09-30) | **not reserved** | example **182** (`fallible-gate`, CERTIFIED: a `-> T or R` gate at the top level); **no code, no gift** -- the exporter's LG007 for `or R` is LIFTED (a fallible gate with a non-integer answer keeps an LG007 by name). The Lean side: `D.agruende`, `Block`/`Endblock.bindAxiomElse`, `sonstPasst`, four machine rules, one `KopfHalt` and one `RestHalt` arm in `Zielsatz/Spec.lean`; the PROVED template `tor.fehlbar` (register 23 -> 24 entries, 12 -> 13 machine-checked); SATZKARTE §62 |
| C-free lane, the region gate (Simon's decision 1, 2026-09-30) | **not reserved** | emitter code **C186** (`syscall.stub`: a region answer without its `or R` channel), gifts **1383** (`C186`), **1384** (`N571`: an index past the gate's extent), **1385** (`N463`: a length past it at a call), **1386** (`M140`: no number becomes a pointer), **1387** (`N571`: a name bound twice carries no extent); example **183** (`region-vom-tor`, `nolibc`, prints `OK`, imports nothing). No `N` code: the extent of a region answer is `N571`/`N463` widened (the gate's `ensures … <= lenof(result)` over a name bound once). The PROVED template `tor.region` (register 24 -> 25 entries, 13 -> 14 machine-checked, `SchablonenOhneLibc.lean` §4); OFFEN O37 (byte pointers have no G form, so 183 stays `UNCERTIFIED` (first refusal `LG003`, the gate's `ensures`; behind it `LG002`, the byte pointer); nothing releases a region)
| C-free lane, the hosted arena runtime (2026-09-30) | **not reserved** | **nothing**: no code, no gift, no example. `laufzeit/arena_dyn.c` deleted; the generated hosted driver writes the arena runtime (`treiber.rs::ARENA_LAUFZEIT`, CLI `gabbro runtime arena`), the PROVED template `arena.dyn` (register 25 -> 26 entries, 14 -> 15 machine-checked, `SchablonenArena.lean`); `bibliothek/linux/linux.gab` defines `gabbro_os_melden`/`_ende`/`_reserve`/`_commit`/`_seitengroesse` in Gabbro over four `linux_os_*` gates (falsifiers `sonde_os_mmap`, `_mprotect`, `_write`, `_exit_group`); `GENERATOR_KENNUNG` `treiber-gen-6` -> `-7`; `Spec.lean` comment-only block "arena runtime"
| C-free lane, hosted locks and the page return (2026-09-30) | **not reserved** | **nothing**: no code, no gift, no example. PROVED templates `sperre.ticket` (the `CTicket.lean` ticket lock written by the hosted driver, `treiber.rs::SPERRE_TICKET`) and `region.leeren` (`SchablonenArena.lean` §2; register 26 -> 28 entries, 15 -> 17 machine-checked); `linux.gab` gains `gabbro_os_nachgeben` (gate `sched_yield`, falsifier `sonde_os_sched_yield`) and `gabbro_os_seiten_zurueck` (gate `madvise`, `sonde_os_madvise`); `gabbro_os_sperre_*` and `gabbro_os_leeren` gone from `linux.c`/`bindung.h`; `laufzeit/start.c`, `start_pool.c` deleted; `GENERATOR_KENNUNG` `treiber-gen-8`; `MARK_AUSSEN` 32 -> 34
| C-free lane, the clone trap and the stack-gate call (2026-09-30, OFFEN O38) | **not reserved** | **N572** (`klon.uebergabe`: every stack-gate call hands to a `child` region -- a call with none checked clean and the child returned through the plain stub on the handed stack), gift **1388**; gifts 1117, 1139, 1140 fire `N572` beside their own code. Emitter: the inline trap of lane 260 stores the raw answer AFTER the branch (the child wrote 0 into the parent's slot before)
| C-free lane, hosted threads without pthread (2026-09-30) | **not reserved** | emitter code **C187** (`syscall.stub`: a stack gate with fewer than two callee-saved registers it neither binds nor destroys has no trampoline), gift **1389**. PROVED templates `tor.trampolin` (the C-only entry of every stack gate) and `faden.laufzeit` (the hosted thread runtime, `treiber.rs::FADEN_LAUFZEIT`; `SchablonenFaden.lean`; register 28 -> 30 entries, 17 -> 19 machine-checked). `N464` widened: a constant clause `4 <= lenof(w)` binds a fixed-size buffer. `bibliothek/linux/linux.c`, `laufzeit/bindung.h`, `faden.c`, `faden.h` DELETED; `linux.gab` gains the stack gate `gabbro_os_klon_tor`, `gabbro_os_klon_flaggen`, `gabbro_os_faden_ende` (`exit`), `gabbro_os_warte_wort` (`futex`); CLI `gabbro runtime threads`; `GENERATOR_KENNUNG` `treiber-gen-9`
| C-free lane, the os-probe's report and the `nolibc` entry hooks (2026-09-30) | **not reserved** | **nothing**: no code, no gift, no example. `messung/proben/os-bindung/melde.c` deleted (the report is Gabbro over `linux.gab`'s new `gabbro_os_schreibe`, `gabbro_os_schreibe_zahl`): hosted C0 = 0; `MARKE_EMIT_M` 162 -> 161, `MARK_AUSSEN` 34 -> 33. The `nolibc` entry calls the unit's `gabbro_os_anfang()` first and hands a returned `main` status to its `gabbro_os_ende(code)` (`bau.rs::nolibc_haken`, `prozess_start`; `start_nolibc_haken` proved, `SchablonenOhneLibc.lean` §2); 1 CLI test. The network stack's C-free change is now a script: `~/claude-lane/C-FREI-FUER-NETZ.py`
| C-free lane, the `child` region outlined (2026-09-30, OFFEN O38 closed) | **not reserved** | **nothing**: no code, no gift, no example. PROVED template `tor.kind` (`SchablonenFaden.lean` §3, `kind_region`; register 30 -> 31 entries, 19 -> 20 machine-checked): the lowered triple's region is `gabbro_kind_<nr>(handed)`, called by the trap in the child -- no `asm goto` into the parent's frame. Gifts 1113, 1115, 1116 lose `allein` (the C compiler now refuses the read of a caller value too). `region.leeren`'s helper rewritten in forms `pruefe-cformen.py` classifies (it was RED since that merge: 5 unclassified statements, now GREEN)
| C-free lane, the kernel-module runtime generated (C2 slice 1, 2026-09-30) | **not reserved** | **nothing**: no code, no gift, no example. `laufzeit/kmodul/` and `bibliothek/linux-kmod/stdatomic.h` DELETED; `gabbro build` writes the module driver (`treiber.rs::erzeuge_kmod`, `kmod_koepfe`, `KMOD_STDATOMIC`), PROVED templates `arena.modul` and `modul.lebenslauf` (`SchablonenModul.lean`; register 31 -> 33 entries, 20 -> 22 machine-checked); manifest words `kmod <kbuild> <load> <unload>`, `provision <bytes>`, `note <section> <text>` (manifest refusals, no `Satz`); `N506` widened (a constant clause `k <= lenof(p)` binds a fixed-size object, `N464`'s twin); `Spec.lean` comment only ((M11): the compiler's C11 builtins instead of the LKMM table); `GENERATOR_KENNUNG` `treiber-gen-10`
| C-free lane, the kernel-module binding in Gabbro (C2 slice 2, 2026-09-30) | **not reserved** | **N573** (`extern.variadik`: the variadic marker `...` of an `extern fn` parameter list), gifts **1390** (the marker at a Gabbro function), **1391** (a record behind it); no example (the positive side is `bibliothek/linux-kmod/linux-kmod.gab`: `_printk`, `panic`). `linux-kmod.c` keeps only the thread pair; `messung/proben/kmodul/melde.c`, `atomar.c` DELETED (the probes report through `gabbro_kern_zeige`/`_halt`). Also **N574** (`fremd.ohne_code`: a foreign body takes no parameter whose type carries a function pointer; OFFEN O39), gifts **1392**, **1393**

| C-free lane, the kernel thread start in Gabbro (C2 slice 3, 2026-10-01, OFFEN O39) | **not reserved** | **N575**-**N577** (`eintritt.code`: the type `entry fn(…) -> R` -- where it stands, no Gabbro caller of a function taking one, one whole hand-over outside every loop), gifts **1394**-**1397**, example **184** (`code-vom-treiber`). `bibliothek/linux-kmod/linux-kmod.gab`'s thread start and join sleep are Gabbro (`kthread_create_on_node`, `wake_up_process`, `msleep`); `linux-kmod.c` keeps the core number only. PROVED template `faden.modul` (`SchablonenModul.lean` §3; register 33 -> 34 entries, 22 -> 23 machine-checked). Emitter repair: a function-pointer PARAMETER is written with its name inside the declarator (it was `T (*)(…) name`, a C error). OFFEN O40 (private functions of one name in two modules share a C name)
- Unused parts of a reserved block stay with the follow-up work of the same wall (for example
  N411–415 for the integer-match exhaustiveness refusal that lane 227 left open, review G07);
  they are never handed to another topic. Next free is always above the highest number in use,
  so a stale reservation can never collide with a new one.
- A lane that takes numbers without a reservation (O-1, 249, 256 above) is booked here by the
  merger in the same merge.
- The test `keine_zwei_korpusdateien_teilen_eine_nummer` catches collisions between lanes.
- **Every new refusal code comes with its sentence** in `saetze.rs` in the same commit
  (`pruefe-saetze.py`), and with a poison probe.

## 8. Files that matter

| What | Where |
|---|---|
| The goal statement | `grammatik/Grammatik/Zielsatz/Spec.lean` (review target), `Beweis.lean`, `Akzeptiert.lean`, `Proben*.lean`, `SpecProben.lean` |
| Model | `RufMaschineG.lean` (machine G), `Semantik.lean` (`execEnd`, `rufAt`), `SperreBeweis.lean`, `Lebendigkeit.lean`, `Gleitkomma*.lean`, `EinpassenVoll.lean`, `AntwortOrte.lean`, `Nichtinterferenz/` |
| Translation validation | Active target: `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5 (source → final x86 bytes, W / GX reuse). Existing C proof record: `Schlusssatz104.lean` (first chain), `Schlusssatz.lean` + `KorrespondenzAllg.lean` (stage (a) generic, `korrOk`), `Kette104*.lean`, `Kette108.lean`, `CNebenlaeufig.lean` + `Schlusssatz124.lean` + `Korpus124.lean` (stage (b)), `CFormen*.lean`, `CSpeicher.lean`, `CSemantik.lean`, `Parser/` (T3) |
| Plans | `dokumente/PLAN-ZIELSATZ.md` (§5 review questions, §8 extension rules, §9–§10 gaps), `PLAN-UEBERSETZUNGSVALIDIERUNG.md` (§§0–5 active x86 target, §§6–7 historical C record), `PLAN-EINFACHHEIT.md`, `NICHTINTERFERENZ.md`, `GLEITKOMMA.md` |
| Theorem map | `dokumente/SATZKARTE.md` (§§13–27; new sections at the end, and renumber on a merge collision) |
| Known absences | `dokumente/OFFEN.md` (O1–O14) |
| Guardian-booked figures | `messung/KENNZAHLEN.md` (moved out of the old TODO.md; `pruefe-zahlen.py` reads it) |
| Verdicts | `messung/URTEIL-*-2026-09-1*.md`; lane reports `messung/muse/MUSE-REPORT-NN.md` |
| Instruments | `instrumente/zaehle-kette.py` (existing C-chain count; does not validate x86 bytes), `pruefe-cformen.py` (three states: lemma / assumption / uncovered), `pruefe-emission.sh`, `abnahme.py` (all guardians), `mutiere-pruefer.py` |
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

**Machines:**

- **Low memory kills jobs silently.** A push job died that way once.
  Watch RAM before heavy builds; one build at a time in one checkout.
- **The combined merge+push was blocked by the classifier once.** Split it into two steps.

## 10. Talking to Simon

- **German, direct, concrete.** Say what was done, what is open and what is uncertain. Never
  claim more than was measured.
- **Estimates:** give ranges, name the critical path, and note that Muse throughput is
  review-bound.
- **They follow from other devices.** Short status lines while long jobs run are welcome.

*Current work list: `TODO.md`. History of how things got here: `git log`, the verdicts and the
lane reports.*

## 11. Coordinator handoff: connecting the direct compiler (2026-10-01)

This section records the working knowledge needed to take over this session.
Treat the dated numbers below as a snapshot. Re-read the live registry and Git
before reporting current activity or publishing. The latest task is to **connect
the existing Lean components**, with up to **15 productive Muse processes** and
substantial delegation of implementation, independent review and organisation.

**Latest steering, 2026-10-01: Simon resumed Muse coordination after Glass
Town did not work and requested sustained overnight progress with up to 15
productive models and completion monitoring.** The earlier pause is historical;
do not restore it without a new user request. Before taking over, inspect live
`inventory`, `overnight-monitor.json`, completion events and worker identities.
Do not start a second coordinator. Actual active models, starting runners,
waiting builds and queued dependencies are different counts.

Connection wave558-575 has progressed: byte decoder soundness, narrow/muldiv/
shift/control codecs, loaded-image/relocation execution and several access/entry/
budget connections are integrated. SourceMemory570 is a committed candidate
under review588; scalar FP codec565 and source-linked IR287 are still working
in the last measured snapshot. Full typed-carrier TSO->W/GX and source-to-final-
bytes validation remain OPEN. The publication suite again found a resource
failure in the native Lean measurement path; owner618 and reviewer619 diagnose
it without weakening tests or verifier verdicts.

The overnight wave has owners594-605 and618 with independent reviewers606-617
and619. Owner594 evaluates direct lowering from the existing typed source AST/
GabbroV versus an additional SSA stage; an extra IR is not a requirement for
correct source-to-binary validation. Preserve IR287 work, but do not freeze an
unnecessary parallel source representation before this decision. Owner595 and
reviewer607 produce the portable read-only completion monitor. Until accepted,
the existing coordinator's bootstrap monitor records events and bounded
interrupted-turn recovery. Monitor deployment must not create a second scheduler.

`coordinator-events.jsonl` and `overnight-monitor.json` record completions,
actual verified model PIDs, blockers, capacity gaps and worker liveness. The
`monitor_report` action returns newly undelivered events to the orchestrator.
Dispatch owns useful automatic backfill; watch owns checked serial integration
and publication. Neither a completion notification nor a positive review may
bypass the source build, axiom, test, emission or key-scan gate. The overnight
monitor is bounded to 12 hours; author turns remain bounded and recoveries are
limited. If the queue empties, organisation must supply substantive disjoint
closure tasks; do not start filler to make the process count look busy.

At the pause, master was `8596f83e`: ValidatorSkeleton349, DecodingCoverage435
and StackUnwind542, DecodeFault543, RegionFresh544, PayloadResidue545,
ContractSites546 had landed with their exact independent reviews. The X86
directory now has 62 accepted modules. The publication wave's Lean build
passed; its remaining checks were interrupted by the requested pause. This
does **not** grant a successful full publication result or an upstream push.

### Current proof boundary and critical path

- The accepted X86 directory currently contains 55 Lean modules, about 26,300
  physical lines, including optimisation and validation helpers. The complete
  local grammar build passed with 420 jobs. Counts are not completion evidence.
- `Codec.decode` and `Ausfuehrung.schritt` cover the 14 pilot forms;
  `Byteschritt` fetches actual executable memory before decoding and executing.
  Wider integer, scalar SSE2, LOCK and other helpers do not yet form one
  completely byte-connected target machine. In particular, encoder round-trip
  consistency is not hardware correspondence.
- `TSO` has real canonical byte memory, per-core FIFO buffers, forwarding,
  issue and flush. Per-byte facts do not establish aligned whole-word atomicity.
  A complete per-access target-to-W/GX simulation is still OPEN. Preserve the
  existing source `schwach_ist_gX` result; do not assume the missing target leg.
- Source-linked IR owner 287 has a substantial preserved, uncommitted
  `IR.lean` draft in its isolated clone. It is **not an accepted interface**.
  Resume this owner; do not make a competing IR. Reviewer 303 waits for a
  clean committed candidate and joint source/table-write witnesses.
- ValidatorSkeleton owner 349 and reviewer 387 are now integrated. Its
  `valX86` checks image mapping
  and decode coverage, not complete source refinement. `valX86_sound` and the
  source-to-final-loaded-byte closing theorem remain OPEN.
- Actual loaded mapping, relocations followed by re-decoding, source-memory
  representation, source duties, runtime/entry bodies and budget-stop ordering
  must be connected. Named hardware timing bounds never prove software bodies,
  source simulation, fairness or bounded CAS retries.

### Local control plane and delegation

The existing coordinator is
`.claude/muse-arbeit/x86/coordinate.py`; it launches the actual local
`/home/simon/.opencode/bin/opencode` with model
`opencode-go/muse-spark-1.3-contributor`. The contributor clones are
`/home/simon/Dokumente/gabbro-muse/aNNN`, each on local `muse/NNN` with no
remote. Do not substitute other models silently or touch Simon's OpenCode.

The private control files are deliberately ignored; committed `lanes/NNN.md`,
`messung/muse/MUSE-REPORT-NNN.md` and `DIRECT-COMPILER.md` are the portable audit.
If the private control plane is unavailable, reconstruct it from committed
tasks/reports and existing clone identities; do not infer acceptance from a
missing state file or recreate a clone over existing work.

- `manifest.json`: ownership, priorities, accepted dependencies and paired
  reviewers. Allocate IDs from this registry, not the historical table in §7.
- `state/NNN.json`: author/reviewer status, exact candidate hashes and PIDs.
  `report_ready` means a candidate exists; it does not mean accepted or merged.
- `dispatch.json` / `dispatch.log`: independent automatic backfill. The
  dispatcher schedules useful authors, repairs and exact-candidate reviews.
- `watch.json` / `watch.log`: serial integration and publication. Dispatch can
  remain alive while integration stops at a gate; inspect both separately.
- `publication-checks.json`, `publication-result.json` and `wave-*.log`: check
  provenance. README-only publication also has `readme-update-result.json`.
  These files can describe different commits; fetch and inspect `origin/master`
  before claiming what is published. Never relabel an old check as a fresh one.

Use the approved coordinator entry point with **positional lane numbers**:

```bash
python3 /home/simon/Dokumente/Gabbro/.claude/muse-arbeit/x86/coordinate.py inventory
python3 /home/simon/Dokumente/Gabbro/.claude/muse-arbeit/x86/coordinate.py session_count
python3 /home/simon/Dokumente/Gabbro/.claude/muse-arbeit/x86/coordinate.py build_activity
python3 /home/simon/Dokumente/Gabbro/.claude/muse-arbeit/x86/coordinate.py resume NNN --budget 14400 --feedback /absolute/path/to/feedback.md
python3 /home/simon/Dokumente/Gabbro/.claude/muse-arbeit/x86/coordinate.py merge AUTHOR REVIEWER
python3 /home/simon/Dokumente/Gabbro/.claude/muse-arbeit/x86/coordinate.py dispatch_start --budget 0
python3 /home/simon/Dokumente/Gabbro/.claude/muse-arbeit/x86/coordinate.py watch_start --budget 0
```

Inspect identities and status first. Start commands reject an already-live
worker; never launch duplicate dispatchers/watchers. `--budget 0` means the
dispatcher/watcher persists; contributor turns have bounded budgets. Use
`dispatch_stop` or `watch_stop` only for our own verified worker identities and
at clean integration boundaries. Do not stop author models just to edit docs.
`coordinator-pause.json` is a private safe-boundary pause marker; remove it only
after its owning coordinator update is finished.

### Connection wave ownership

New connection owners 558–575 are registered with paired reviewers
576–593 (`reviewer = author + 18`). Their committed prompts are authoritative;
registration and a target of 15 are not a claim that 15 models are running.

| Owners | Deliverable |
|---|---|
| 558 | Integration organisation and concrete producer/consumer plan |
| 559–561 | Arbitrary-input decoder soundness, loaded-image execution, patched-byte re-decoding |
| 562–566 | Narrow, multiply/divide, shift, scalar FP and conditional byte-facing connections |
| 567–569 | Shared TSO-history projection, realised instruction footprints and fetched stack execution |
| 570–572 | Source-world byte representation, entry/user duties and budget-stop/work connection |
| 573–574 | Actual W store/read bridges; wait for accepted 567 and 570 interfaces |
| 575 | One extended decoder/execution path; waits for accepted decoder producers |

IR287 resumes alongside this wave. Owners may prove a useful bounded
connection or a precise obstruction, but must not manufacture a desired
simulation premise, duplicate an interpreter, count a conjunction of checks as
execution, or claim the full bridge from a byte-level projection alone.
Keep the friend-reserved optimiser files untouched. No overlapping writers of
canonical vocabulary; central fixes need an explicitly assigned follow-up.
Reviewer clones get exact committed snapshots and their own checks. Organisation
agents propose ordering and mechanical integration; semantic acceptance remains
independent, and publication remains serial and checked.

### Known integration and apparatus issues

- The integration watcher previously stopped after an intermittent CLI alias
  test failure. Muse 556 diagnosed resource starvation/concurrent Lean duty
  measurements; Muse 557 independently reviewed the exact repair. Both are now
  merged (`a6e63a86`, `daec5d32`). The candidate's full suite passed with
  1471 tests and zero failures; **fresh integrated publication checks are still
  required**. The repair serialises measurements per model and retries only
  specific bounded resource failures; it does not weaken checker verdicts.
- Accepted candidates 542–546 and reviewers 548–552 were integrated before
  the pause. They cover StackUnwind, DecodeFault, RegionFresh, PayloadResidue
  and ContractSites. Read their actual CUTS before using them as foundations.
- Heavy builds share a memory lease through the pool's `cargo-slot` and
  `lean-slot`. Native Lean retains two workers and a 4096-MiB heap budget;
  the recovered process virtual-address ceiling is 16 GiB. The old 8-GiB
  virtual ceiling caused `failed to create thread` even on unchanged source.
  Do not confuse virtual address space with resident RAM or relax proof gates.
- Some condensed wrappers can exit successfully after a child failure. Check
  their **complete-output summary** (`== exit 0`, zero errors/failing tests),
  not only shell return code. `cargo-pruef` retains `.tmp/cargo-test-full.log`.
- Rust/prover reviewers need warm **private** `programmlogik/.lake` and
  `bruecke/.lake` as well as `grammatik/.lake`. Missing or incompatible caches
  caused network stalls or misleading exported-program errors. Never share a
  writable build directory across clones or download dependencies in a lane.
- Separate per-lane OpenCode databases prevent the earlier shared SQLite/session
  failures. Keep those private paths; do not inspect keys/config credentials.
- Scratch belongs on the project SSD, not RAM-backed `/tmp`. Keep actual model
  PIDs separate from starting jobs, Python runners and build processes. Aim for
  15 useful models, report actual counts, and record genuine resource/dependency
  bottlenecks rather than starting filler.

### Publication and preservation

The README change removing Caprock and replacing the quick start with a tested
Hello workflow is pushed and upstream-verified at `6faacdfe`. Preserve it during
later merges. The Hello sequence generated source, checked, built and printed
`Hi`; Isabelle and developer acceptance commands were removed from the entry
workflow. README metrics and negative guardian probes must remain protected.

363 fully merged local branches were removed. The worktree
`.claude/worktrees/agent-afcfe48d684b6bb5b` still contains unique uncommitted
`laufzeit/metall/metall.ld` and `start.S` changes: **preserve it**. Other unmerged
worktrees and the unsuccessful separate README-publication candidate are not
eligible for automatic merged-work cleanup. Delete clean accepted lane clones
only after checked integration, retaining committed reports and logs.

Update this handoff and `DIRECT-COMPILER.md` when its operational facts change.
The next coordinator should be able to distinguish a running author, reviewed
candidate, integrated theorem, green publication check and verified upstream
push without relying on this conversation.


### Automatic coordinator takeover and completed task cleanup

Simon explicitly authorised an OpenCode coordinator to take over if the
foreground Codex session no longer responds, including a usage-limit stop.
The intended trigger is five minutes without a foreground heartbeat; it does
not query or infer an API usage balance. The fallback consumes one of the
same **15** model slots, leaving at most 14 contributor/reviewer models.
Only foreground Codex records `root_heartbeat`; background monitoring must
never keep that heartbeat alive. An exclusive owner lease and action lock
prevent competing foreground coordinators. Returning Codex requests a safe
handback before mutating root; dirty integrations and running publication
actions must be preserved. Explicit user pause overrides takeover/backfill.

Implementation belongs to author620 and independent reviewer621:
`instrumente/coordinator-failover.py` with mock-provider, lock, pause,
PID-identity and handback tests. The private prototype is not armed until
this exact candidate is reviewed and integrated. Inspect live
`.claude/muse-arbeit/x86/failover-status.json` and `orchestrator-lease.json`
for the actual role/health; registration is not an operational takeover.
Fallback source work stays delegated to isolated contributors; no direct
push bypass is granted. Checked publication, goal axioms and exact independent
reviews remain mandatory. Persist handoff notes in private `FALLBACK-HANDOFF.md`.

Latest instruction: remove numeric lane task Markdown when work is finally
over. Author622/reviewer623 own `instrumente/lane-cleanup.py` and adversarial
fixtures. Delete only registered, completed, idle lane tasks after checked
integration and after pending task consumers have their exact snapshots.
Keep active, paused, incomplete, blocked, repair and review-waiting tasks.
Preserve `lanes/VORSPANN.md`, reports/logs, all unmerged source, and Git task
history. Run historical sweeps and future cleanup at serial clean boundaries;
commit tracked removals and keep progress links pointing to surviving evidence.

Architecture594/reviewer606 is accepted: use the existing typed Syntax/exec
source as the reference and lower directly to checked machine blocks/bytes.
A persistent SSA IR is not required. Preserve the unaccepted IR287 draft as
design input; do not introduce another source interpreter on the trust path.
Full generic source-to-final-loaded-byte validation remains **OPEN**.
