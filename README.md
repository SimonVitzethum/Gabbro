# Gabbro

> **Status 2026-11-10: research prototype, work in progress. There is NO working Gabbro compiler and NO working
> Gabbro checker yet.**
> What exists is a Lean 4 model with a proved goal theorem, and Stage 0, a partial verified path from Gabbro to an
> assembly IR. The repository holds Lean and one assembly file (the runner); the outdated Rust checker, the LLVM
> emitter and the C probes were deleted on 2026-11-10 and live in git history only.

Gabbro is a systems programming language designed so that **the user proves only their own logic and named hardware
assumptions**. Memory safety, race freedom, contracts and time are meant to be carried by the language and proved once
over its model.

## What exists

| Part | State |
|---|---|
| **Lean model and goal theorem** (`grammatik/`) | `gabbro_ziel` is proved over the model on exactly `propext`, `Classical.choice`, `Quot.sound`, with witnesses and refusal probes. The checker inside the statement is the Lean one. |
| **Stage 0** (`stage0/`, `runner/`) | Lean compiles part of the userspace language to the IR `S0IR` with a generic lowering theorem; an x86-64 assembly runner executes it. Of 320 source regressions, 242 pass (167 executions, 75 expected refusals), 68 expected executions are refused at compilation and 10 refusal diagnostics differ; no executed case returned a wrong exit code (measured 2026-11-06). These counts are not language coverage. |
| **Native floats** (`nativefloat/`) | Floating operations are opaque in Lean and executed by the CPU. `RootNativeFloat.Hardware` is the explicit, ISA-independent hardware assumption (bit codec, order, conversions, literals, correct rounding of `+ - * /`). Instruction-level correspondence per target is still owed. |
| **GabbroV** (`programmlogik/`, `bruecke/`) | The `Body` model and the bridge to machine G, with duty files for five programs. The duty printer was part of the deleted Rust tool; the five files are tracked inputs until a Lean generator exists. |

## What does not exist

- A working Gabbro compiler, and a working Gabbro checker for the full language (the verified ones are the goal).
- A verified compiler, or any proved bridge from the model to a binary. Never call the compiler or a binary verified.
- A standard library; programs bring their own `syscall` items and bindings.
- Full source-to-IR coverage. Open forms are in
  [IR-COMPILATION-LANES](dokumente/IR-COMPILATION-LANES.md).

## Check the proof yourself

```bash
git clone https://github.com/SimonVitzethum/Gabbro && cd Gabbro/grammatik
lake build Grammatik.Zielsatz.Kern.Beweis Grammatik.Zielsatz.Atomar.BeweisAtomar
lake env lean NachpruefungZiel.lean     # prints the axioms of every named sentence
```

Lean 4.35.0 pins itself from `grammatik/lean-toolchain`; the only dependency is Mathlib (first build is large). A
`sorryAx` in the printed axiom list would mean the sentence is not proved.

**What this does not say:** an axiom list shows a proof is valid, not that the statement is right. The statement is
`grammatik/Grammatik/Zielsatz/Kern/Spec.lean`; its header is the one list of named assumptions and of what is NOT
CLAIMED, and wins wherever other text disagrees. The user still owes the logic of their program and the hardware
assumptions. Loader, runtime thread creation and foreign behaviour are named assumptions whose correspondence is unproved.

## Goal: a formally verified Gabbro compiler

The aim is a **formally verified Gabbro checker and compiler**, not an untrusted compiler with after-the-fact
certificates. Both are specified in Lean (the model, `AkzeptiertX`, the lowering) and proved correct against that
specification, and the compiled code is verified against the CPU. The proof runs through the complete test sets **M**
(accepted programs) and **N** (refused programs): a tool that agrees with the model on M and N agrees on every program
(`vollstaendig_hinreichend`), together with logic proofs (GabbroV). Stage 0 is the first verified slice of this path.
Open: M and N as concrete values for the whole model, the lowering cells, the CPU model for the final machine code
(the x86-64 runner's instruction subset is tested against the CPU), and the checker and compiler themselves.

## Documents

[goal statement](grammatik/Grammatik/Zielsatz/Kern/Spec.lean) · [syntax](dokumente/SYNTAX.md) ·
[language](dokumente/LANGUAGE.md) · [Stage-0 compilation](dokumente/IR-COMPILATION-LANES.md) ·
[GabbroV](dokumente/GABBROV.md) · [low-level plan](dokumente/LOW-LEVEL-SYNTAX-PLAN.md) ·
[long-range plan](dokumente/PLAN-LONG-RANGE.md) · [how work is run](AGENTS.md)

> **License: AGPL-3.0** ([LICENSE](LICENSE)). Your Gabbro programs, what the compiler makes of them and the binaries are
> yours, under any license. The condition applies only if you call the result formally verified or secure
> ([addendum](LICENSE-ADDENDUM.md)). The working language is English; example identifiers stay German (grammar data).
