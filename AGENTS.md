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
3. **Then:** translation validation, i.e. the chain source → model → emitted C, checked in Lean.

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
README §5 says exactly this; keep it that way.

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

- **Push master without asking**, after checked merges. First grep the outgoing diff for keys.
  Never push red. Never force-push. No new branches on GitHub: lane branches stay
  local (`muse/NNN` never leaves this machine), Opus branches stay in their
  worktree until their review lands — the only remote branch besides master is
  the one under active review.
- **Delete worktrees and clones right after a merge.** That covers `.claude/worktrees/*`,
  the lane clones, and the `gabbro-opus-*` directories.
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
- **Floats are in scope** (IEEE model done). Probabilistic statements are OUT of scope for now.
  **Dynamic data structures are IN scope** (Simon, 2026-09-28): structures that grow without a
  static element bound, on heap regions with a declared ceiling and refuse-on-full (TODO §0e).
  A heap without a ceiling stays refused.
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

**Exception since 2026-09-28 (Simon): one autonomous Claude lane on `ubuntu@simon.jocraft.cc`.**
At most ONE agent runs there at a time, in its own clone `~/Gabbro` (and, for the network
stack, `~/gabbro-netz/`). It builds and tests in its own tree, merges into master only with
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
  `logs/NN.log`; keep a copy of every lane file in `.claude/muse-arbeit/lanes5/` and
  `.claude/muse-sicherung/`.

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
| Diagnostic codes | **N569** (highest issued: N568, Opus lane L) |
| Gift (poison-probe) numbers | **1364** (highest file: `beispiele/gift/1363`, Opus lane L) |
| Example numbers | **166** (highest file: `beispiele/165`, Opus lane L) |
| Lane numbers | **259** workers (highest used: 258); reviewers from **373** at least (372 is the highest named in the tree; the loop's own counter is authoritative) |

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
| Server lane, phase 1 (TODO §0e) | **not reserved** | **nothing**: no code, no gift, no example. What it added instead: the instruments `instrumente/miss-arena-decke.sh` (H4, the ceiling against the cost) and `instrumente/pruefe-kernelmodul.sh` (a Gabbro unit as a Linux kernel module, QEMU only); the runtime `laufzeit/kmodul/` (`kmodul.c`, `arena.c`, `kmodul.h`, `include/`); the probes `messung/proben/arena-h4/ceiling-{10mib,32gib}.gab` and `messung/proben/kmodul/{halde-treiber.gab,melde.c}`; one CLI test (`der_link_ohne_with_leitet_die_schnittstellen_ab`). The poison probes of both instruments are HARNESS mutations (`--gift`), not `beispiele/gift/` files, so they take no gift number |

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
| Translation validation | `Schlusssatz104.lean` (first chain), `Schlusssatz.lean` + `KorrespondenzAllg.lean` (stage (a) generic, `korrOk`), `Kette104*.lean`, `Kette108.lean`, `CNebenlaeufig.lean` + `Schlusssatz124.lean` + `Korpus124.lean` (stage (b)), `CFormen*.lean`, `CSpeicher.lean`, `CSemantik.lean`, `Parser/` (T3) |
| Plans | `dokumente/PLAN-ZIELSATZ.md` (§5 review questions, §8 extension rules, §9–§10 gaps), `PLAN-UEBERSETZUNGSVALIDIERUNG.md` (chain count, §6 stage (a), §7 stage (b)), `PLAN-EINFACHHEIT.md`, `NICHTINTERFERENZ.md`, `GLEITKOMMA.md` |
| Theorem map | `dokumente/SATZKARTE.md` (§§13–27; new sections at the end, and renumber on a merge collision) |
| Known absences | `dokumente/OFFEN.md` (O1–O14) |
| Guardian-booked figures | `messung/KENNZAHLEN.md` (moved out of the old TODO.md; `pruefe-zahlen.py` reads it) |
| Verdicts | `messung/URTEIL-*-2026-09-1*.md`; lane reports `messung/muse/MUSE-REPORT-NN.md` |
| Instruments | `instrumente/zaehle-kette.py` (the chain count, the one headline metric of translation validation), `pruefe-cformen.py` (three states: lemma / assumption / uncovered), `pruefe-emission.sh`, `abnahme.py` (all guardians), `mutiere-pruefer.py` |
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
