# Gabbro

Gabbro is a systems programming language with a Rust compiler and a Lean 4
model of its core language and safety properties.

> **Gabbro's goal: the user proves only their own logic and named hardware
> assumptions; the language carries the rest — on a multicore kernel with DMA.**

Memory safety, race freedom, contracts where claimed — in concurrent runs too —
and time are carried by the language and proved once over its model. Per program
the user owes what is explicit and named: the logic (`NutzerPflichtA`: bodies at
every budget and against every shared-atomic-read value, plus start duties) and
the hardware assumptions (`HardwareAnnahmen`). The direction is OS-as-user-logic
with declared contracts — but loader, runtime thread creation and foreign
behaviour are still named assumed premises (c)/(d), their correspondence unproved.

Proved today is narrower than the goal; exactly one place states it: the
header of [`Zielsatz/Spec.lean`](grammatik/Grammatik/Zielsatz/Kern/Spec.lean). Where
they disagree, the header wins. The honest sentence is **"the goal theorem is
proved over the model, with a witness and non-degeneracy"** — not "Gabbro is
verified" ([details](#5-proved-and-not-proved)).

There is **no standard library, no libc and no runtime you link**. Everything a
program does to the outside world goes through its own `syscall` items (raw
kernel gates with declared registers, contracts and error channels) or through
hardware register forms; the operating system is user logic, never an assumption
of the language. Networking, files, TLS, HTTP and the like are not built in and
not forbidden: they are written in Gabbro, in your program or in a binding
library (`bibliothek/`), over those gates, and checked like any other code. The
container, text and time helpers a program needs on every page are planned as
native Gabbro modules ([PLAN-STDLIB](dokumente/PLAN-STDLIB.md)), not as C behind
a border.

There is one backend: **LLVM**. Checked Gabbro lowers directly to LLVM IR (x86-64 and
AArch64), with no C, no libc and no linked runtime — locks, threads and arenas are generated
IR over raw kernel gates ([LLVM-BACKEND](dokumente/LLVM-BACKEND.md)). The C11 emitter was
removed on 2026-10-17 (repository tag `archiv/c-emitter-2026-10-17`; its Lean proofs stay as
archived evidence). The backend is not verified: the final-binary refinement needs a complete
Lean model of the CPU, which is built on the Sail Arm specification
([sail-arm](https://github.com/rems-project/sail-arm)) plus a multicore memory
model in Lean, and is not finished ([plan](ARM-PLAN.md)).

## 1. Quick start

Install **Rust 1.86 or newer**. The Rust crates have no third-party dependencies.
Checking source needs nothing else. `gabbro build` needs the LLVM tools `opt`, `llc` and
`ld.lld` on `PATH` — there is no C compiler (`cc`) in the chain.
Ensure `~/.cargo/bin` is on your `PATH`.

```bash
git clone https://github.com/SimonVitzethum/Gabbro
cd Gabbro
cargo install --path crates/gabbro-cli
gabbro new hello
gabbro check hello.gab
gabbro build hello.bau
./target/hello/hello
```

The program prints `Hi`. `gabbro new` creates `hello.gab` (source) and
`hello.bau` (build manifest). Open them alongside the [tutorial](dokumente/TUTORIAL.md)
to learn the language.

For checker coverage, run `gabbro passes`; for outstanding user obligations, run
`gabbro obligations hello.gab`.

## 2. Proof check in two commands

**Everything above is a claim — this is how you stop taking it on trust,** proved
in Lean 4 over the language model (thread machine over GX, shared-atomic rely):

```bash
git clone https://github.com/SimonVitzethum/Gabbro && cd Gabbro/grammatik
lake build Grammatik.Zielsatz.Beweis Grammatik.Zielsatz.Proben Grammatik.Zielsatz.ProbenW1 Grammatik.Zielsatz.BeweisAtomar
lake env lean NachpruefungZiel.lean     # prints the axioms of every sentence named below
```

`elan`/`lake` come from [leanprover/elan](https://github.com/leanprover/elan); Lean
4.33.1 pins itself from `grammatik/lean-toolchain`. The only dependency is
[Mathlib](https://github.com/leanprover-community/mathlib4), pinned to the tag for the same
toolchain in `grammatik/lakefile.toml`; the first build fetches it (about 7.5 GB with precompiled
oleans via `lake exe cache get`). The goal theorem itself does not import it, and
`#print axioms` still prints exactly the three standard axioms.

| Printed line | What it means |
|---|---|
| `gabbro_ziel … [propext, Classical.choice, Quot.sound]` | only Lean's standard three — no `sorryAx`, no axiom of ours. **A `sorryAx` here would mean it is not proved** |
| `…_zeuge` | a two-thread program that moves memory satisfies it, so the sentence is not empty |
| `…probeA/D…`, `w1_abgelehnt` | programs the checker **refuses** — a checker that accepts everything would make the theorem worthless |

The translation evidence (archived C chain, LLVM certificate) is described in [PLAN-UEBERSETZUNGSVALIDIERUNG](dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md) and [LLVM-BACKEND](dokumente/LLVM-BACKEND.md) §7 — the recipe above prints only the goal-theorem sentences.

**What those lines do NOT say:** an axiom list proves a *proof* valid, not the
*statement*. The three axioms prove no model fidelity and remove no premise:
checked program, user logic, hardware assumptions, runtime stay owed.

## 3. How the guarantee is meant to work

The Rust checker and emitter will **not** be verified: the compiler is untrusted
and shows its work — **every accepted program gets a Lean-checked certificate:**

> **Lean accepts the certificate ⟹ (1)** the source parses to `P`, **(2)** `P`
> satisfies the model, **(3)** every execution of the validated final image
> refines `P` / GX — bytes, layout, relocations, entries, conventions.

The five pieces ([plan](dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md) §§0–5):
**T3** Lean parser (source → `P`; items in, generics and round-trip in flight);
**T1** model certificates per constructor; **T4** AArch64 semantics (derived
from the Sail Arm model) and image decoding (planned — C semantics stay as
backend evidence); **T2** final-byte correspondence validator (planned —
`korrOk` is C-only); **T5** proof templates for runtime, entries, locks,
recurring duties (register below). Concurrency reuses W / GX; the per-access
bridge to the Arm memory model is open — a proved validator refuses bad output,
still requiring the new validator and its proof.

## 4. Status

Measured snapshot 2026-10-17 — every figure carries its command; since the four-guardian cut these figures are dated results, not guarded values (see [MESSUNGEN](dokumente/MESSUNGEN.md) and [WERKZEUGKASTEN](dokumente/WERKZEUGKASTEN.md)).

| | | |
|---|---|---|
| **Compiler** | 12 passes, 3 complete, **9 carried with a named residue**, 0 partial, 0 open | 497 diagnostics · `gabbro passes` |
| **Grammar** | **189 EBNF rules**, closed and reachable | vocabulary covers every terminal, 245 / 245 |
| **Proof templates** | **41, of which 30 are machine-checked** | `gabbro templates` |
| **Corpus** | 170 clean examples, 898 poison files | `cargo test --no-fail-fast` |
| **Backend** | LLVM backend (the only one, no C), x86_64 and aarch64 | `./instrumente/pruefe-llvm.py` |
| **Guardians** | exactly 4: Lean model, LLVM compiler, checker, GabbroV; each prints its work quantity, `2` means not measured | `./instrumente/abnahme.py` |
| **Blind spots** | **72 blind · 176 covered · 24 poison-only · 12 no cell** *(of 285 pairs)* — poison-only is a hint, not a proof | `gabbro blindspots` |
| **Usability** | 312 of 2431 teaching sites and 14 of 110 real-code sites **may fall** — 2564 and 110 clause sites | `gabbro ceremony` |

The 15 theories in [`grammatik/Beweise/`](grammatik/Beweise/)
hold 3512 lines of Isar; new proofs go to Lean only.

## 5. Proved and not proved

- **Proved over the model:** `theorem gabbro_ziel : GabbroZiel`
  ([statement](grammatik/Grammatik/Zielsatz/Kern/Spec.lean), proof
  `Zielsatz/BeweisAtomar.lean`, tags `milestone-2026-09-15-gabbro-ziel` and
  `-zielsatz-bestaetigt`), six review rounds; round 6: *"the goal with named
  gaps — no unnamed gap found"*. The checker inside is the **Lean** checker.
- The C-model chain is closed for five programs by one generic theorem
  (concurrently one, under named premises); GabbroV derives premise (b) in Lean
  from the source for five programs. These do not certify binaries.

Not proved, still open: no pass proved individually (sentences measured on
checked cases, never the rule); complete Rust backend validation, final-byte
validation and hardware/concurrency correspondence **OPEN**; the direct
final-binary validator is not implemented — never call the compiler or a binary verified.
Most accepted programs are not judged in Lean at all; the rest are refused by
the exporter and listed by name as not claimed in
[`REGISTER.txt`](grammatik/Grammatik/Zertifikat/REGISTER.txt).

## 6. Documents

- [ARM-PLAN.md](ARM-PLAN.md) — the AArch64 direction: Sail Arm model, multicore memory model, compiler
- [Own and aliasing](dokumente/A1-OWN-PAPER.md) — `own`, rules R014/R015, the Lean object model, `noalias`
- [Tutorial](dokumente/TUTORIAL.md), [open items](TODO.md), [goal statement](grammatik/Grammatik/Zielsatz/Kern/Spec.lean), [measurements](dokumente/MESSUNGEN.md), [LLVM backend](dokumente/LLVM-BACKEND.md)

> **How this repository is written — AI agents, and where the human stands.**
> Agents do implementation, checking and coordination; Simon decides what counts
> as reached, refused, merged. Every commit names its model (`Co-Authored-By`).
> **Nothing counts because an agent said so:** numbers are re-measured at merge
> time; a claim bigger than its proof gets sent back.

> **License: AGPL-3.0** ([LICENSE](LICENSE)) — what you write in Gabbro is not
> a derived work: program, generated C and binaries are yours, under any
> license. **The condition applies only if you call the result formally
> verified or secure**: then the generated files say which checker said so.
> Claim nothing and you owe nothing ([addendum](LICENSE-ADDENDUM.md)). Working
> language is **English**; example identifiers stay German — grammar data.
