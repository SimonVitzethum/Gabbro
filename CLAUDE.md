# Gabbro — working instructions

**Operating manual: [`AGENTS.md`](AGENTS.md)** — state, goal, procedures (lanes, merge, push),
number ranges and the expensive pitfalls. The work list is `TODO.md`. The manual is loaded here:

@AGENTS.md

*Shortened on 2026-10-17: the guardian anecdotes (mutation run, number guardians, abort rules) belong to
the 80 guardians that no longer exist. They are in git (`git log -p CLAUDE.md`); what still counts as a
rule is stated below.*

## Language and syntax follow the Lean model (Simon, 2026-10-17)

**The Lean model (`grammatik/`) is the single source for language and syntax.** Whenever anything about the
language or its syntax changes (a construct, a clause, a type rule, a rule that accepts or rejects a
form), it goes FIRST into the Lean model (machine G, `Akzeptiert`, `gabbro_ziel` stays on
`propext`/`Classical.choice`/`Quot.sound`, a reviewed `Spec.lean` diff when the statement moves).
Only then follow the checker, the compiler and `SYNTAX.md`/`LANGUAGE.md` — never the other way round. If the
checker accepts something the model does not know, the checker is wrong. A pure lowering of an existing form
(LLVM) does not change the language and is not covered by this rule.

## No legacy in the compiler, the checker and the parser (Simon, 2026-10-17, fixed rule)

**The compiler, the checker and the parser carry no legacy: only the newest state.** What is replaced is
deleted (the history is in git), not kept beside the new: no compatibility layers, no deprecated paths,
no old names or flag aliases, no refusal codes for things that no longer exist, no remnants of the C emitter
(C naming rules, C templates, `emit.rs` references). A change is finished only when it has removed its
predecessor.

## There are exactly four guardians

| Guardian | Subject | What it checks |
|---|---|---|
| `instrumente/pruefe-lean.py` | the Lean model (`grammatik/`) | `lake build`, `gabbro_ziel` only on `propext`/`Classical.choice`/`Quot.sound`, no `sorry`/`admit`/`native_decide`/`axiom`, at most 20 entries per folder |
| `instrumente/pruefe-llvm.py` | the LLVM compiler | `cargo test --test llvm`, nine programs as a binary on x86_64 and aarch64 (qemu) with the same result, the heap stays free until used (no read/write mapping above 1 GiB) |
| `instrumente/pruefe-pruefer.py` | the checker (Rust) | `cargo test --workspace --no-fail-fast`, sentence register, identifiers assigned only once |
| `instrumente/pruefe-gabbrov.py` | GabbroV (`programmlogik/`) | `lake build`, proofs without `sorry`, `gabbro prove` GREEN, no GREEN without Lean |

`./instrumente/abnahme.py` runs all four one after the other (`--lean`, `--llvm`, `--pruefer`, `--gabbrov`
each alone). Exit code: `0` measured and green, `1` measured and red, `2` **nothing or not everything
measured** — that is not a green. Helper parts (sentence register, layout tool, model coverage, `baue-llvm.sh`)
live in `instrumente/teile/` and run only through the four. **A fifth guardian is not built**: whatever is
to be checked anew becomes a test in `cargo test`, a Lean theorem or a stage in one of the four.

## Everything runs locally, with an eye on memory

Everything that computes runs in this checkout: every Lean build, every `cargo` run, every acceptance run.
There is no second machine any more (since 2026-09-27); recipes for servers or SSH in old notes are history.
`git push` goes through `~/.ssh/id_ed25519_github`.

* **One heavy run at a time, `free -g` beside it.** Heavy are `cargo build`, `cargo test`, `lake build`
  and the acceptance run. *An abort for lack of memory is not a finding.*
* **`cargo test` and a Lean run must not run at the same time in ONE tree:** `cargo test` calls
  `gabbro prove`, which rebuilds with `lake` and replaces the `.olean` files that running `lean` processes
  read (measured: 52 phantom errors `Body.olean … does not exist`).
* **Always `cargo test` with `--no-fail-fast`**, otherwise it reports only the first failed probe. Whoever
  wants to count must not stop at the first hit (applies to every measurement, also `set -e` in scripts).
* **`-rlpgoD` and not `-a` when a tree built by `cargo` is copied:** `cargo` decides freshness by
  timestamp; without the `t` it builds from a mixture.
* **Do not wait with `pgrep -f`/`pkill -f`:** the pattern finds its own command line. Wait for a run with a
  file whose last line you read, or with `ps -C`.
* `rustc`/`cargo` live in `~/.cargo/bin`; Lean through `elan` (`ELAN_TOOLCHAIN` must not be set,
  `lean-bau`/`lean-probe` remove it).

## Agents

* **Every agent gets its OWN directory** (its own worktree beside the checkout, never this checkout) and
  its own scratch directory. Two runs in one tree measure a mixture.
* **An agent's working tree is on `master` before the run starts** (a `--ff-only` catch-up costs nothing).
* **Both trees into an agent directory:** `crates/` and `grammatik/`; `programmlogik/` needs its warm
  `.lake` (Mathlib), otherwise `cargo test` hangs (`gabbro prove` goes cloning). A stale `.lake` is worse
  than none.
* At most two Opus agents at a time (AGENTS.md §6).

## What else applies

* **The working language is ENGLISH, everything except the conversation:** source comments, all `.md`
  files **and their file names**, commit messages, diagnostics, `gabbro hilfe`. German remains only for the
  conversation with Simon in this checkout. The commit history is not rewritten.
* **At most 30 `.md` files in the repo** (state 2026-10-20: 28). New documents only if no existing one has
  room; reports, verdicts and interim states belong in git, not in the tree.
* **Commit messages only through `arbeitsprotokoll/.commitmsg` + `./commit.sh`** (R19; commits only staged
  changes).
* **Caprock lies read-only in `../caprock-messbasis`: never commit into it.** Correction proposals go in
  the log, not in the foreign tree.
* **`aarch64` stays sealed** ("blocked — lineage"), no third attempt — for the old C-emitter line. The LLVM
  path carries both targets (`x86_64`, `aarch64`); the Lean part of the hardware runs through `ARM-PLAN.md`.
* **The Isabelle part has been transferred to Lean, the `.thy` set is frozen** (15 theories in
  `grammatik/Beweise/` against 15 Lean files in `grammatik/Grammatik/Isabelle/`). A new proof belongs in
  Lean. Isabelle2025-2 lives under `~/Isabelle2025-2` (without `sudo`, own JDK, no AFP).
* **A guardian that aborts reads like one that passed.** Whoever finds a run red or aborted looks for the
  cause first in what was NOT printed any more, and measures the base in a throwaway worktree before the
  merge instead of guessing.
