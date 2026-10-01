# Gabbro

Gabbro is a systems programming language for writing verified operating
systems — Caprock is the reason it exists — with a Rust implementation and a
Lean 4 model of its core language and safety properties.

> **Gabbro's goal: the user proves only their own logic and named hardware
> assumptions; the language carries the rest — on a multicore kernel with DMA.**

Memory safety, race freedom, contracts where claimed — in concurrent runs too —
and time are carried by the language and proved once over its model. Per
program the user owes only what is explicit and named: the application logic
(`LogikPflicht`, at every budget, against every value a shared atomic read may
return) and the hardware assumptions (`HardwareAnnahmen`). OS, runtimes,
thread startup and locks are never trusted or assumed — they are user/binding
logic with checked contracts and implementations.

Proved today is narrower than the goal; exactly one place states it: the
header of [`Zielsatz/Spec.lean`](grammatik/Grammatik/Zielsatz/Spec.lean). Where
they disagree, the header wins. The honest sentence is **"the goal theorem is
proved over the model, with a witness and non-degeneracy"** — not "Gabbro is
verified" ([details](#5-proved-and-not-proved)).

The working backend emits C11 plus inline assembly. The selected target is a
direct x86-64 backend with Lean final-byte validation — `-O3`-like from
invariants, fast including validation, for arbitrary OS and freestanding
profiles. Lean X86 helpers exist but are not the complete hardware model;
backend and validation are not implemented ([record](DIRECT-COMPILER.md)).

## 1. Quick start

Zero external dependencies — the three crates need `std` and each other only;
**Rust 1.86 or newer** (`f64::next_up`/`next_down` stable there). **`cc` is
needed at run time, not at build time** — only `gabbro build` calls it.

```bash
git clone https://github.com/SimonVitzethum/Gabbro && cd Gabbro
cargo install --path crates/gabbro-cli     # `gabbro` into ~/.cargo/bin
gabbro check beispiele/01-tabelle.gab
gabbro build beispiele/172-prozess-ohne-libc.bau
gabbro passes                              # what each pass does and does NOT do
gabbro templates                           # the proof-template register
gabbro obligations beispiele/*.gab         # what a HUMAN still owes — counted, not discharged
cargo test --no-fail-fast                  # the test corpus
./instrumente/abnahme.py                   # every guardian, one command, per-guardian verdict
./instrumente/pruefe-emission.sh           # every emitted unit must compile
./instrumente/mutiere-pruefer.py           # damage one rule at a time: 422 mutations, one anchor each
isabelle build -d beweise -c Gabbro        # the machine-checked templates
```
`gabbro passes` also prints what each pass does **not** check — unchecked silence must never look green.

## 2. Proof check in two commands

**Everything above is a claim — this is how you stop taking it on trust,** proved
in Lean 4 over the language model (thread machine over GX, shared-atomic rely):

```bash
git clone https://github.com/SimonVitzethum/Gabbro && cd Gabbro/grammatik
lake build Grammatik.Zielsatz.Beweis Grammatik.Zielsatz.Proben Grammatik.Zielsatz.ProbenW1 Grammatik.Zielsatz.BeweisAtomar
lake env lean NachpruefungZiel.lean     # prints the axioms of every sentence named below
```

`elan`/`lake` come from [leanprover/elan](https://github.com/leanprover/elan); Lean
4.33.1 pins itself from `grammatik/lean-toolchain` — **no mathlib, no other dependency.**

| Printed line | What it means |
|---|---|
| `gabbro_ziel … [propext, Classical.choice, Quot.sound]` | only Lean's standard three — no `sorryAx`, no axiom of ours. **A `sorryAx` here would mean it is not proved** |
| `…_zeuge` | a two-thread program that moves memory satisfies it, so the sentence is not empty |
| `…probeA/D…`, `w1_abgelehnt` | programs the checker **refuses** — a checker that accepts everything would make the theorem worthless |
| `schlusssatz…`, `kette_104/108…`, `K124…` | existing C-backend translation validation, source text → model → emitted C; no x86 byte validation |

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
**T1** model certificates per constructor; **T4** x86 semantics and image
decoding (planned — C semantics stay as backend evidence); **T2** final-byte
correspondence validator (planned — `korrOk` is C-only); **T5** proof templates
for runtime, entries, locks, recurring duties (register below). Concurrency
reuses W / GX; the per-access x86-TSO bridge is open — a proved validator
refuses bad output, still requiring the new validator and its proof.

## 4. Status

Measured snapshot 2026-10-01 — every figure carries its command; provenance and limits in [PROJECT-STATUS](dokumente/PROJECT-STATUS.md).

| | | |
|---|---|---|
| **Compiler** | 12 passes, 3 complete, **9 carried with a named residue**, 0 partial, 0 open | 481 diagnostics · `gabbro passes` |
| **Grammar** | **188 EBNF rules**, closed and reachable | vocabulary covers every terminal, 242 / 242 |
| **Proof templates** | **34, of which 23 are machine-checked** | `gabbro templates` |
| **Corpus** | 157 clean examples, 856 poison files | `cargo test --no-fail-fast` |
| **Backend** | working C11 backend (`cc -std=c11 -Wall -Wextra -Werror`, `-O0` and `-O2`); every emitted unit is compiled, part executed against a handwritten twin | `./instrumente/pruefe-emission.sh` |
| **Guardians** | 56, each with deadline, two-way speech test, red on abort, pinned locale, and work quantity beside the verdict; **75 of 89 instruments carry all five requirements** | `./instrumente/abnahme.py` |
| **Blind spots** | **73 blind · 175 covered · 24 poison-only · 12 no cell** *(of 285 pairs)* — poison-only is a hint, not a proof | `gabbro blindspots` |
| **Usability** | 312 of 2431 teaching sites and 14 of 110 real-code sites **may fall** — 2431 and 110 clause sites | `gabbro ceremony` |

The 15 theories in [`beweise/`](beweise/) hold 3512 lines of Isar (Isabelle2025-2); new proofs go to Lean only.

## 5. Proved and not proved

- **Proved over the model:** `theorem gabbro_ziel : GabbroZiel`
  ([statement](grammatik/Grammatik/Zielsatz/Spec.lean), proof
  `Zielsatz/BeweisAtomar.lean`, tags `milestone-2026-09-15-gabbro-ziel` and
  `-zielsatz-bestaetigt`), six review rounds; round 6: *"the goal with named
  gaps — no unnamed gap found"*. The checker inside is the **Lean** checker.
- The C-model chain is closed for five programs by one generic theorem
  (concurrently one, under named premises); GabbroV derives premise (b) in Lean
  from the source for five programs. These do not certify x86 binaries.

Not proved, still open: no pass proved individually (sentences measured on
checked cases, never the rule); complete Rust backend validation, final-byte
validation and hardware/concurrency correspondence **OPEN**; the direct x86
backend is not implemented — never call the compiler or a binary verified.
Most accepted programs are not judged in Lean at all; the rest are refused by
the exporter and listed by name as not claimed in
[`REGISTER.txt`](grammatik/Grammatik/Zertifikat/REGISTER.txt). Caprock is not
written in Gabbro yet; fragments, with origin and verdict, in
[`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md).

## 6. Documents

- [DIRECT-COMPILER.md](DIRECT-COMPILER.md) — direct x86-64 compiler record ([design](DIRECT-COMPILER-DESIGN.md), [optimiser](grammatik/OPTIMIZER.md), [portability](dokumente/x86/TARGET-PORTABILITY.md))
- [Tutorial](dokumente/TUTORIAL.md), [open items](TODO.md), [goal statement](grammatik/Grammatik/Zielsatz/Spec.lean), [provenance](dokumente/PROJECT-STATUS.md)

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
