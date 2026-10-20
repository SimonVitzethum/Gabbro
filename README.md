# Gabbro

Gabbro is a systems programming language with a Rust compiler and a Lean 4 model of its core language and safety properties.

> **Gabbro's goal: the user proves only their own logic and named hardware assumptions; the language carries the rest, on a multicore
> kernel with DMA.**

Memory safety, race freedom, contracts where claimed (in concurrent runs too) and time are carried by the language and proved once over
its model. Per program the user owes what is explicit and named: the logic (`NutzerPflichtA`: bodies at every budget and against every
shared-atomic-read value, plus start duties) and the hardware assumptions (`HardwareAnnahmen`). Loader, runtime thread creation and
foreign behaviour are still named assumed premises (c)/(d); their correspondence is unproved.

**In one sentence about the state:** the goal theorem is proved over the model, with a witness and non-degeneracy; the Rust checker and
the LLVM backend are **not** verified, and no bridge to any binary exists yet ([section 5](#5-proved-and-not-proved)).

## What Gabbro is

- **No standard library, no libc, no linked runtime.** Everything a program does to the outside world goes through its own `syscall`
  items (raw kernel gates with declared registers, contracts and error channels) or through hardware register forms. The operating system
  is user logic, never an assumption of the language. Networking, files, TLS and the like are written in Gabbro, in your program or in a
  binding library (`bibliothek/`), and checked like any other code. The container, text and time helpers every program needs are planned
  as native Gabbro modules ([PLAN-STDLIB](dokumente/PLAN-STDLIB.md)), not as C behind a border.
- **One backend: LLVM.** Checked Gabbro lowers directly to LLVM IR for x86-64 and AArch64: no C, no libc; locks, threads and arenas are
  generated IR over raw kernel gates ([LLVM-BACKEND](dokumente/LLVM-BACKEND.md)). The C11 emitter was removed on 2026-10-17 (tag
  `archiv/c-emitter-2026-10-17`, which also holds its Lean line).
- **The backend is not verified.** Final-binary refinement needs a complete Lean model of the CPU, which is being built on the
  [Sail Arm](https://github.com/rems-project/sail-arm) specification plus a multicore memory model in Lean ([plan](ARM-PLAN.md)).

## 1. Quick start

Install **Rust 1.86 or newer** (the crates have no third-party dependencies) and put `~/.cargo/bin` on your `PATH`. Checking source needs
nothing else. `gabbro build` additionally needs the LLVM tools `opt`, `llc` and `ld.lld`; there is no C compiler in the chain.

```bash
git clone https://github.com/SimonVitzethum/Gabbro
cd Gabbro
cargo install --path crates/gabbro-cli
gabbro new hello
gabbro check hello.gab
gabbro build hello.bau
./target/hello/hello
```

The program prints `Hi`. `gabbro new` creates `hello.gab` (source) and `hello.bau` (build manifest); read them next to the
[tutorial](dokumente/TUTORIAL.md). `gabbro passes` shows checker coverage, `gabbro obligations hello.gab` the user obligations left.

## 2. Proof check in two commands

**Everything above is a claim; this is how you stop taking it on trust.** The goal theorem is proved in Lean 4 over the language model
(thread machine over GX, shared-atomic rely):

```bash
git clone https://github.com/SimonVitzethum/Gabbro && cd Gabbro/grammatik
lake build Grammatik.Zielsatz.Beweis Grammatik.Zielsatz.Proben Grammatik.Zielsatz.ProbenW1 Grammatik.Zielsatz.BeweisAtomar
lake env lean NachpruefungZiel.lean     # prints the axioms of every sentence named below
```

`elan`/`lake` come from [leanprover/elan](https://github.com/leanprover/elan); Lean 4.35.0 pins itself from `grammatik/lean-toolchain`.
The only dependency is [Mathlib](https://github.com/leanprover-community/mathlib4), pinned to the matching tag in
`grammatik/lakefile.toml`; the first build fetches it (about 7.5 GB with precompiled oleans via `lake exe cache get`). The goal theorem
itself does not import it, and `#print axioms` still prints exactly the three standard axioms.

| Printed line | What it means |
|---|---|
| `gabbro_ziel … [propext, Classical.choice, Quot.sound]` | only Lean's standard three: no `sorryAx`, no axiom of ours. **A `sorryAx` here would mean it is not proved.** |
| `…_zeuge` | a two-thread program that moves memory satisfies it, so the sentence is not empty |
| `…probeA/D…`, `w1_abgelehnt` | programs the checker **refuses**: a checker that accepts everything would make the theorem worthless |

**What those lines do NOT say:** an axiom list shows a *proof* is valid, not that the *statement* is right. The three axioms prove no
model fidelity and remove no premise: checked program, user logic, hardware assumptions and runtime stay owed. The statement is
`Zielsatz/Kern/Spec.lean`; its header is the one list of named assumptions and of what is NOT CLAIMED, and wins wherever other text
disagrees.

## 3. How the guarantee is meant to work

The Rust checker and compiler will **not** be verified: the compiler is untrusted and shows its work. **Every accepted program gets a
Lean-checked certificate:**

> **Lean accepts the certificate ⟹ (1)** the source parses to `P`, **(2)** `P` satisfies the model, **(3)** every execution of the
> validated final image refines `P` / GX: bytes, layout, relocations, entries, conventions.

Five pieces ([plan](dokumente/PLAN-TRANSLATION-VALIDATION.md) §§0-5):

| Piece | What | State |
|---|---|---|
| **T3** | Lean parser, source to `P` | items in; generics and round trip in flight |
| **T1** | model certificates per constructor | see the plan, §1 |
| **T4** | AArch64 semantics (from Sail Arm) and image decoding | planned |
| **T2** | final-byte correspondence validator | planned |
| **T5** | proof templates for runtime, entries, locks, recurring duties | 41 templates, 30 machine-checked |

Concurrency reuses W / GX; the per-access bridge to the Arm memory model is open. A proved validator would refuse bad output, but it still
needs the new validator and its proof.

## 4. Status

Measured snapshot 2026-10-17. Each figure names its command; since the four-guardian cut these are dated results, not guarded values
(see [MESSUNGEN](dokumente/MEASUREMENTS.md), [TOOLBOX](dokumente/TOOLBOX.md)). Work in progress is in [TODO.md](TODO.md).

| | | |
|---|---|---|
| **Compiler** | 12 passes: 3 complete, 9 carried with a named residue, 0 partial, 0 open | 497 diagnostics · `gabbro passes` |
| **Grammar** | 189 EBNF rules, closed and reachable | vocabulary covers every terminal, 245 / 245 |
| **Proof templates** | 41, of which 30 are machine-checked | `gabbro templates` |
| **Corpus** | 170 clean examples, 898 poison files | `cargo test --no-fail-fast` |
| **Backend** | LLVM (the only one), x86_64 and aarch64 | `./instrumente/pruefe-llvm.py` |
| **Guardians** | exactly 4: Lean model, LLVM compiler, checker, GabbroV; each prints its work quantity, exit `2` means not measured | `./instrumente/abnahme.py` |
| **Blind spots** | 72 blind · 176 covered · 24 poison-only · 12 no cell (of 285 pairs); poison-only is a hint, not a proof | `gabbro blindspots` |
| **Usability** | 312 of 2431 teaching sites and 14 of 110 real-code sites may fall (2564 and 110 clause sites) | `gabbro ceremony` |

The 15 Isabelle theories in [`grammatik/Beweise/`](grammatik/Beweise/) hold 3512 lines of Isar and are frozen; new proofs go to Lean.

## 5. Proved and not proved

**Proved over the model:** `theorem gabbro_ziel : GabbroZiel` ([statement](grammatik/Grammatik/Zielsatz/Kern/Spec.lean), proof
`Zielsatz/BeweisAtomar.lean`; tags `milestone-2026-09-15-gabbro-ziel` and `-zielsatz-bestaetigt`). Six review rounds; round 6: *"the goal
with named gaps, no unnamed gap found"*. The checker inside the statement is the **Lean** checker, not the Rust one. GabbroV derives
premise (b), the user's logic, in Lean from the source for five programs; that does not certify binaries.

**Not proved, still open:**
- No pass is proved individually (sentences are measured on checked cases, never the rule).
- Complete backend validation, final-byte validation and hardware/concurrency correspondence are **open**; the final-binary validator is
  not implemented. Never call the compiler or a binary verified.
- Most accepted programs are not judged in Lean at all; the rest are refused by the exporter and listed by name as not claimed in
  `target/zertifikate/REGISTER.txt`, written on every `cargo test --test zertifikate`.

## 6. Documents

| | |
|---|---|
| Start here | [Tutorial](dokumente/TUTORIAL.md) · [open work](TODO.md) · [goal statement](grammatik/Grammatik/Zielsatz/Kern/Spec.lean) · [how work is run](AGENTS.md) |
| Language | [Own and aliasing](dokumente/A1-OWN-PAPER.md) (`own`, `R014`/`R015`, `noalias`) · [Syntax](dokumente/SYNTAX.md) |
| Backend and hardware | [LLVM backend](dokumente/LLVM-BACKEND.md) · [AArch64 plan](ARM-PLAN.md) · [translation validation](dokumente/PLAN-TRANSLATION-VALIDATION.md) |
| Plans | [dynamic structures](dokumente/PLAN-DYNAMIC.md) · [standard library](dokumente/PLAN-STDLIB.md) · [long-range](dokumente/PLAN-LONG-RANGE.md) |
| Measurements | [MESSUNGEN](dokumente/MEASUREMENTS.md) · [TOOLBOX](dokumente/TOOLBOX.md) |

> **How this repository is written: AI agents, and where the human stands.** Agents do implementation, checking and coordination; Simon
> decides what counts as reached, refused or merged. Every commit names its model (`Co-Authored-By`). **Nothing counts because an agent
> said so:** numbers are re-measured at merge time, and a claim bigger than its proof gets sent back.

> **License: AGPL-3.0** ([LICENSE](LICENSE)). What you write in Gabbro is not a derived work: your program, everything the compiler
> makes of it and the binaries are yours, under any license. **The condition applies only if you call the result formally verified or secure:** then the
> generated files say which checker said so. Claim nothing and you owe nothing ([addendum](LICENSE-ADDENDUM.md)). The working language is
> **English**; example identifiers stay German (grammar data).
