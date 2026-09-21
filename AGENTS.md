# AGENTS.md — how work on Gabbro is run

*Written 2026-09-15 by the Claude session that ran the project from the laptop until the move to
the server, as the hand-over of everything it knew that is not in the code. `CLAUDE.md` stays the
Simon's work instructions (German); this file is the operating manual beside it. Where the two
disagree, `CLAUDE.md` wins.*

**Who reads this:**

- **The orchestrating Claude session** on `ubuntu@simon.jocraft.cc` (tmux `Claude-Gabbro`,
  tree `/home/ubuntu/Gabbro`). It reads everything below.
- **A Muse contributor lane** (opencode on `fisch`), if it sees this file. The HARD RULES in its
  lane prompt bind it, and §5–§8 are not its business. In particular it never runs `ssh`,
  `rsync`, `git push` or `cargo`/`lake` directly; it uses `./cargo-pruef`, `./emission-pruef`,
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
README §6 says exactly this; keep it that way.

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
  - `StartEndeG`, `KeinStartGrundG`, `KeinLogikHaltG`;
  - no deadlock and `KeinWarteZyklus`;
  - `FortschrittG`, whose stop kinds are hardware, flag, budget and `nieZurueck`;
  - `ZeitAb`.
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
  freedom, invariants at entry, one start on several threads, and linking of separately compiled
  units. Probabilistic statements and dynamic unbounded structures are out of scope (§3), but
  `Spec.lean` does not name them. Every extension of the goal is reviewed as a diff of
  `Spec.lean`.

## 3. Simon's standing instructions

- **Push master without asking**, after checked merges. First grep the outgoing diff for keys.
  Never push red. Never force-push. No new branches on GitHub: lane branches stay
  fisch-local (`muse/NNN` never leaves the clone), Opus branches stay in their
  worktree until their review lands — the only remote branch besides master is
  the one under active review.
- **Delete worktrees and clones right after a merge.** That covers `.claude/worktrees/*`, fisch
  `~/gabbro-muse/aNNN`, and the `gabbro-opus-*` directories.
- **Opus agents: at most 2 at a time.** Simon said on 2026-09-14: "nutze 2 opus agenten".
  Muse lanes: as many as useful. Use the free model slots too (3 slots, falling back to
  opencode-go on a rate limit). The Go budget can run out, which is fine.
- **Commit messages** go through `arbeitsprotokoll/.commitmsg` + `./commit.sh`. It commits STAGED
  changes only, so `git add` first.
- **Language:** documents, comments, commit messages, diagnostics and `TODO.md` are in English.
  The conversation with Simon is in German. Muster (guardian patterns) become bilingual
  BEFORE a document changes language.
- **Work in real folders, not `/tmp`.** `/tmp` is RAM on the laptop. Scratch files go to
  `.claude/muse-arbeit/kratz/`.
- **Every Lean build and every `cargo` run goes to fisch.** No exceptions for "just a small one".
- **Simplicity is a goal, but no guarantee is given up for it** (PLAN-EINFACHHEIT.md). The measure
  is: ceremony count down AND pass register constant. Never derive `ensures`, and never turn a
  refusal into a warning.
- **Safety is never traded for features** (Simon, 2026-09-17). No lane weakens a guarantee —
  memory safety, race freedom, contracts, costs, lock discipline — to make a wall go green.
  Walls that only yield by weakening are recorded as findings (208's vacuity pins, 203's
  recorded blockage of 07 and 125). Reviewers reject bypasses, no matter how green the build.
- **Floats are in scope** (IEEE model done). Probabilistic statements and dynamic unbounded data
  structures are OUT of scope for now.
- **Tag milestones** at the push that reaches them.
- **Security:**
  - Never write API keys or passwords into the repo, memory or logs. The opencode keys live only
    in fisch `~/gabbro-muse/cfg/key-go` and `key-zen`.
  - When the permission classifier blocks something (e.g. searching the server for credentials),
    do not work around it; ask Simon.
  - A local password Simon once gave was for WireGuard only; it is recorded nowhere.

## 4. Machines

| machine | role | notes |
|---|---|---|
| `ubuntu@simon.jocraft.cc` (host `GaussBerechnungen`) | **orchestrator since 2026-09-15** | 15 GB RAM, ~9 GB free (Minecraft holds 4 GB: tmux `mc`, `-Xms4G -Xmx4G`). 39 GB disk free. Passwordless `sudo`. Runs WireGuard `wg-quick@wg1`, the link to fisch's network. GitLab is stopped but still enabled — ask Simon before disabling it. No Isabelle. Claude is installed natively in `~/.local/bin` (self-updating); the old npm copy in `/usr/local` can go once no session uses it. |
| `ki-pc-fisch-101` (host `fisch`) | **all compute** | 110 GB RAM, 16 cores. Rust in `~/.cargo/bin`, Lean via `~/.elan/bin/lake` (Lean 4.33.1), Isabelle in `~/Isabelle2025-2`. Reached from ubuntu directly: `ssh ki-pc-fisch-101`, key `~/.ssh/id_ed25519_fisch`. |
| Simon's laptop | former orchestrator | 31 GB RAM with little free. Reaches fisch via `ProxyJump jocraft` (`Host ki-pc`). Local wg1 is down. |

- **GitHub:** push is `git@github.com:SimonVitzethum/Gabbro.git` with key
  `~/.ssh/id_ed25519_github`; the host key was checked against GitHub's published ed25519
  fingerprint. Fetch goes over https.
- **Caprock** (the OS this language exists for) lies read-only in `../caprock-messbasis` on the
  laptop. Never commit into it.

## 5. Muse lanes (opencode on fisch) — the workhorse

**Layout on fisch, `~/gabbro-muse/`:**

- `bin/` holds the tools:
  - `neu-agent3 NN` clones the lane from `stage/gabbro3.bundle`, copies the warm Lean cache
    `stage/lake3`, and writes the queued wrappers `lean-bau`, `lean-probe`, `cargo-pruef` and
    `emission-pruef`.
  - `lauf-agent3 NN SECONDS` runs the lane, with up to 3 auto-continuations.
  - `hinweis-agent NN MSGFILE [SECONDS]` sends reviewer feedback into the lane's session.
  - `modell-wahl` picks the free slot or Go.
  - `lane-datei NN TASKFILE` composes a lane file.
- `lanes/NN.md` holds the lane prompts; `logs/NN.log` the logs; `aNNN/` the clones, one per
  lane, on branch `muse/NNN`, with no remote.
- `merge-bau/` is the warm build directory for merges. `stage/` holds the bundle and the Lean
  cache.
- `cfg/` holds `opencode.json` (permissions: no push, ssh, rsync, cargo, lake or network) and
  the keys.

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

**Launching** (the bundle must contain the master you want; `pruef-push.sh` refreshes it):

```bash
ssh ki-pc-fisch-101 'cd ~/gabbro-muse && bin/neu-agent3 NN >/dev/null; (setsid nohup bin/lauf-agent3 NN 10800 >/dev/null 2>&1 < /dev/null &)'
```

Use `setsid` plus a subshell; a plain `nohup … &` inside `ssh` kept the ssh call hanging.

**Watching:** run a persistent Monitor that polls `logs/NN.log` for `=== ENDE` and counts
`git -C aNN rev-list --count master..HEAD`. **Its lane range must cover the new numbers**: the old
monitors covered 100–159 and 160–199, and lane 200 onward needs a new range.

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

1. fetches `muse/NN` from the fisch clone;
2. merges with `--no-commit`;
3. auto-resolves only `Grammatik.lean` import conflicts, and takes master's side of the ledger
   files;
4. moves the report to `messung/muse/`;
5. builds `grammatik/` on fisch `merge-bau`;
6. commits, deletes the branch and deletes the fisch clone.

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

1. `bash .claude/muse-arbeit/lake3-von-fisch.sh` refreshes the lanes' warm Lean cache from
   `merge-bau`.
2. `EMISSION=./instrumente/pruefe-emission.sh bash .claude/muse-arbeit/pruef-push.sh` bundles
   master, runs `cargo test --no-fail-fast` and the emission check on fisch, and pushes only if
   `ct=0 em=0 failed=0`, origin is not ahead, and the key grep is empty. If origin moved,
   `git pull` (merge) first and run it again.
   - Do NOT run it with `EMISSION=true`.
   - Emission counters (`MARKE_EMIT`, `MARKE_EMIT_G`, `MARKE_EMIT_M` in
     `instrumente/pruefe-emission.sh`) are re-measured by the merger, not by lanes. Each bump is
     dated with its reason.

## 6. Opus agents (Claude subagents, max 2)

- Spawn them with `isolation: worktree` and `run_in_background: true`.
- **Their Lean and cargo builds go to their own fisch directory**, e.g. `gabbro-opus-tv` or
  `gabbro-opus-nb`. The prompt says so explicitly:
  - sync with `rsync -rlpgoD --delete --exclude .lake/ --exclude target/ …`;
  - seed the cache with `cp -a ~/gabbro-muse/stage/lake3 …/grammatik/.lake`;
  - **and `programmlogik/.lake` is the one that bites `cargo test`.** `gabbro prove` builds
    `programmlogik/`, which needs **mathlib**; with no cache there, `lake` goes off to clone
    mathlib4 and the run hangs with zero CPU. *Measured 2026-09-15: two Opus trees stalled 13
    and 19 minutes on exactly this, and both times it was the apparatus and not the tree.*
    There is no staged cache for it yet — until there is, either copy `programmlogik/.lake`
    from a tree that has one, or keep `cargo test` off the lane and say so in the report;
  - a stale `programmlogik/.lake` is worse than none: an `incompatible header` makes
    `pruefe-lean-programm.sh` announce *"the exported program is not valid Lean"*, which is a
    sentence about the olean and not about the program (met in the acceptance run of
    2026-09-15);
  - build with `ssh … lake build`.
- **The prompt names:** the standards (no `sorry`, `native_decide` or new `axiom`; standard
  axioms; witnesses), the plan and SATZKARTE updates expected, "commit on your branch, do not
  merge", and the report they finish with.
- **Use them for** the hard single pieces (model repairs, closing theorems, verdicts).
- **Session limits:** when an Opus agent stops on a session or weekly limit, its worktree keeps
  the work. Resume it with SendMessage after the reset; do not start a fresh one.

## 7. Number ranges and counters (free from here)

| Kind | Next free |
|---|---|
| Diagnostic codes | **N466** (highest issued: N465, fix lane F6; also `C185`, O-1) |
| Gift (poison-probe) numbers | **1171** (highest file: `beispiele/gift/1170`, fix lane F7) |
| Example numbers | **157** (highest file: `beispiele/156`) |
| Lane numbers | **259** workers (highest used: 258); reviewers from **373** at least (372 is the highest named in the tree; the loop's own counter on fisch is authoritative) |

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
| O-1 (Opus) | **not reserved** | N446–N450, `C185`, gifts 1107–1112, examples 155, 156 |
| 249 | **not reserved** (TODO row says "—") | N451, N452, gifts 1113–1117 |
| 256 | **not reserved** | N453–N455 (the spare of the block N451–455 that lane 249 chose itself), gifts 1118–1127 |
| Fix lane F2 | **not reserved** (free range) | gifts 1132–1138; no code (`N426` and `N211` tightened, not minted) |
| Fix lane F3 | **not reserved** (free range) | N456, N457, gifts 1139–1147; no example (`N450`/`N451` tightened, not minted) |
| Fix lane F4 | **not reserved** (free range) | N458–N462, gifts 1148–1154; no example (`LG001` reused for repeated starts in the exporter) |
| Fix lane F5 | **not reserved** (free range) | N463, N464, gifts 1155–1158; no example (examples 96/149/150 edited to the new buffer clause) |
| Fix lane F6 | **not reserved** (free range) | N465, gifts 1159–1168; no example (gift 1125 turned from clean side to `N454`, renamed `1125-index-in-max-ohne-laenge`) |
| Fix lane F7 | **not reserved** (free range) | gifts 1169, 1170; no code, no example (`E011` tightened, `LG005` reused for a binding covering a carrier in the exporter; examples 09/147/148 edited) |

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

- **A lane cloned from a stale bundle** works against a master that no longer exists. Refresh the
  bundle (`pruef-push.sh`) before launching.
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

- **Low memory on the orchestrator kills jobs silently.** A push job died that way once.
  Everything heavy goes to fisch.
- **The combined merge+push was blocked by the classifier once.** Split it into two steps.

## 10. Talking to Simon

- **German, direct, concrete.** Say what was done, what is open and what is uncertain. Never
  claim more than was measured.
- **Estimates:** give ranges, name the critical path, and note that Muse throughput is
  review-bound.
- **They follow from other devices.** Short status lines while long jobs run are welcome.

*Current work list: `TODO.md`. History of how things got here: `git log`, the verdicts and the
lane reports.*
