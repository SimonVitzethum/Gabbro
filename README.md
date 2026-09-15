# Gabbro

**A systems language that carries the proof plumbing, so that verifying an operating system
costs a fraction of what it costs today.** One output: C11 plus inline assembly. The compiler
is safe Rust (`forbid(unsafe_code)`) with zero external dependencies.

The point is not to have another language. The point is to write an operating system in it —
**Caprock** — and then verify that system cheaply.

> **License: AGPL-3.0** ([LICENSE](LICENSE)) — **with an additional permission that answers the
> important question up front:** what you write in Gabbro is not a derived work. Your program,
> the generated C and the binaries are yours, under any license you like. The condition is one
> line: generated C files and binaries carry a notice saying they came out of Gabbro. Details in
> [LIZENZ-ZUSATZ.md](LIZENZ-ZUSATZ.md).

---

## 1. The problem

seL4 is the reference point, and it is an honest one: a verified microkernel, with roughly
**20 lines of proof for every line of code**. That verified configuration is **single-core and
has no DMA** — so those 239 458 proof lines describe a kernel without real concurrency.

Most of what such a proof establishes is not the interesting part. It is **plumbing**: index
bounds, overflow, aliasing, framing, lock order, data races, termination, phase, leafness,
publication, refinement. Eleven classes, and the same eleven in every kernel ever written.

Gabbro's claim is that plumbing belongs to the **language**, not to the proof:

> **Gabbro proves everything except functional correctness — on a multicore kernel with DMA.**

**Nine of the eleven classes are carried today.** The two that are not no longer hang on a
missing pass: *race* hangs on exactly three of its 28 forms, and those three are the alias;
*refinement* hangs on the semantics of a function body, which is what section 4 is about.

**Multicore and DMA are set, not optional.** That is deliberate, and it is a statement against
the most convenient of all simplifications. The pairing (`publishes`/`awaits`) is load-bearing
rather than a "later", and the `dma` space carries real statements instead of a classification.

## 2. Why this is not a solver problem

The other way to get here is an SMT solver: write the program, write the annotations, let Z3
discharge them. Verus and Dafny do that well. Gabbro does not, for two reasons.

**A refusal is better than a timeout.** Where a solver gets slow, a grammar says which
construct it will not carry and why, by name. The compiler ships **391 diagnostics** and no
search procedure.

**A template falls once, not per program.** Every construct the language carries turns into one
generator obligation — proved a single time, over the semantics — instead of an obligation per
program that uses it. That amortisation is the whole economic argument, and it is measurable
rather than rhetorical.

Here is what a program looks like. A table whose writes are guarded by a linear token, with
exactly one place in the world that can mint that token:

```gabbro
module beispiel::eigner_mit_erzeuger {

table Plaetze count 8 owner Marke {
    slot {
        benutzt : bool,
    }
}

linear ghost type Marke;

extern fn erste() -> Marke effects { pure } costs <= 1 ops;
extern fn lege_ab(m : Marke) effects { consumes m } costs <= 8 ops;

impl fn schreibe(m : Marke, i : index into Plaetze)
    effects { writes Plaetze.slots, consumes m }
    costs   <= 32 ops
{
    Plaetze.slots[i].benutzt = true;
    lege_ab(m);
}

impl fn runde(i : index into Plaetze)
    effects { writes Plaetze.slots }
    costs   <= 64 ops
{
    let m = erste();
    schreibe(m, i);
}

}
```

No annotation on that program says "no data race" or "no double free". The declarations say who
writes what, what it costs, and that the token moves exactly once — and the rest follows from
the grammar.

## 3. What it is for: Caprock

**Caprock is the kernel this language exists for**, and the target is larger than the kernel:
an operating system, and a distribution on top of it, that is **formally verified everywhere
except the drivers**.

**Linux drivers already run under Caprock.** That is what makes "except the drivers" a viable
line instead of an excuse — the enormous, permanently moving, hardware-specific part of any OS
is borrowed rather than rewritten, and it is the one part nobody has ever verified at scale.
Everything above it is in scope.

**The first commercial target is isolation.** A Vercel-style cloud platform that runs tenant
workloads **under Caprock instead of under virtual machines**. The trade there is concrete: a
hypervisor buys isolation with a second kernel, a second scheduler and a cold start measured in
hundreds of milliseconds; a kernel whose isolation is a proved property rather than a
configured one can buy the same separation at process cost. That is the use case Gabbro's
verification budget is being spent for, and it is the reason the multicore and DMA requirements
above are not negotiable — a platform that oversubscribes cores and hands devices to tenants
has no use for a single-core proof.

What that still requires is written down rather than assumed: the driver boundary has to be a
*named* assumption with a stated interface, not a gap, and the isolation argument has to reach
from the model down to the emitted C. Section 4 is the plan for the second half.

## 4. How the proof works: the checker is not trusted

The Rust checker and emitter — around 110 000 lines — will **not** be verified. Proving them
would have cost an estimated 700 000 lines of proof, and it would have proved them against a
*second copy* of the model rather than against the model itself.

Instead the compiler is treated as untrusted and made to show its work. **For every program it
accepts, it emits a certificate, and Lean checks that certificate.** The closing theorem has
this shape:

> **Lean accepts the certificate ⟹**
> **(1)** the source text parses to a program `P`, and
> **(2)** `P` satisfies the model — types, safety, lock order, and
> **(3)** the emitted C refines `P`.

So every run of the C corresponds to a run of `P`.

**The failure mode is one-way.** A broken checker can only reject good programs, whose
certificates then fail to go through. It can never let a bad program past. This matters more
than it sounds: the two real defects this project has shipped both sat *in the emitter*, below
every pass, where no Gabbro program could defend itself — a device access emitted at the wrong
width, and two same-named devices given the same port offset, both silent, both with a clean
`cc -Werror`. Both are closed, both carry a poison probe, and both are written out in full in
[`dokumente/BEWEIS.md`](dokumente/BEWEIS.md). Certificate checking is the structural answer to
that class.

**What is left in the trust base:** the Lean kernel, the C compiler, the hardware profile, and
named assumptions about devices and the scheduler. Those assumptions stand as premises inside
the theorem, not as prose beside it.

### The five pieces

| | what it establishes | status |
|---|---|---|
| **T3 — Parser in Lean** | source text → `P`, so the certificate starts from the source and not from a representation Rust produced | lexer, expressions, statements and items are in; the generic version and the print/parse round-trip are in flight |
| **T1 — Model certificates** | `P` satisfies the typing and safety rules, by a decidable certificate per constructor | all 40 expression and all 50 statement constructors carried in Lean; Rust prints statement certificates for 47 of 253 bodies |
| **T4 — Semantics of the emitted C** | what the generated C means: memory model, integer semantics, a full UB list, one correspondence lemma per form | 48 of 73 emitted forms have their lemma; a guardian goes red the moment the emitter produces a form without one |
| **T2 — Correspondence re-checker** | *this* C program consists of exactly those correspondences | designed, not built — **the one piece that closes the chain** |
| **T5 — Proof templates** | each recurring obligation gets a soundness theorem over the real semantics | 5 of 21 bound; the remaining 16 are still an abstract core |

### Not started: the concurrent half

The model is concurrent; the emitted C is not yet — it contains no thread creation, and the
lock primitives are external prototypes. Closing that needs the lock specification with
happens-before as a named assumption, thread creation by the runtime as a second, DRF-SC as a
third (which *applies* here precisely because the race pass proves data-race freedom), and then
the correspondence between a model run and a C run with interleaving. That last item is the
largest single open piece in the project.

### Order of work

1. Finish the parser: generic, round-trip.
2. Close the C gaps — tagged unions, error-reason numbering, and the most frequent of the 25
   forms that have no semantics yet. Several of those will end as named assumptions rather than
   lemmas: inline assembly and device reads have no C semantics by construction.
3. Build T2 — the print format and the Lean re-checker.
4. Bind the remaining templates to the semantics.
5. The concurrent half.
6. The closing theorem with a witness on a real program, then a second witness on a program
   with real sharing.

## 5. Status

Everything below is produced by a command that stands beside it, and every one of them can be
re-run.

| | | |
|---|---|---|
| **Compiler** | 12 passes, 3 complete, **9 carried with a named residue**, 0 partial, 0 open | 391 diagnostics · `gabbro paesse` |
| **Grammar** | **177 EBNF rules**, closed and reachable | vocabulary covers every terminal, 240 / 240 |
| **Pass register** | **158 sentences over 12 passes — 150 measured, 2 ARGUED, 6 CONJECTURED, 0 proved**, claiming 335 diagnostic codes. *A written sentence is not a proved one; the last column is the whole rest* | `gabbro paesse --je-satz` |
| **Proof templates** | **21, of which 10 are machine-checked**; all **15** Isabelle theories now also exist in Lean (`grammatik/Grammatik/Isabelle/`, 15 files, imported by `Grammatik.lean`, so every build checks them), and new proofs go to Lean only | Isabelle2025-2, [`beweise/`](beweise/) · lanes 168/169 |
| **Corpus** | 109 clean examples, 668 poison files, 942 tests *(counted 2026-09-14, lane 177; the row stood at 891 without a re-run since lane 175)* | `cargo test --no-fail-fast` |
| **Emission** | **250 of 250 units emit and compile** under `cc -std=c11 -Wall -Wextra -Werror`, at `-O0` and `-O2`, with the same result; 37 are also executed and compared against a handwritten version, one of them a library chain across three units and a linker, under `-fsanitize=undefined` *(run 2026-09-14)* | `./instrumente/pruefe-emission.sh` |
| **Guardians** | 41, and **65 of 68 instruments carry all five requirements** — deadline, two-way speech test, red on abort, pinned locale, and work quantity beside the verdict | `./instrumente/abnahme.py` |
| **Mutation** | **386 of 413 anchors hold**, and a run catches 375 of 376 valid mutations | `./instrumente/mutiere-pruefer.py` |
| **Blind spots** | **74 blind · 174 covered · 24 poison-only · 12 no cell** *(of 285 pairs)* — four parts on purpose: a removal leaves numerator *and* denominator, and poison-only is a hint, not a proof | `gabbro blindstellen` |
| **Usability** | 7.5 % of the teaching corpus and 12.7 % of real code **may fall** — 1669 and 110 clause sites, split derivable / redundant / load-bearing | `gabbro zeremonie` |

The 15 theories in [`beweise/`](beweise/) hold 3 512 lines of Isar
(3 512 across all 15 theories). They are the amortisation argument as a *measurement* rather
than a claim — and the figure behaves honestly: it falls when a proved construct gets used, and rises when one gets
proved ahead of use.

## 6. What is not true yet

This section exists because the alternative is that a reader has to find it out.

- **No pass has been proved individually.** 155 written sentences, 147 of them *measured* —
  meaning a poison probe falls or a mutation is caught. That measures the implementation on
  checked cases, never the rule, and never all cases.
- **What IS proved is the goal theorem over the MODEL** — and only there. `theorem gabbro_ziel :
  GabbroZiel` (statement [`grammatik/Grammatik/Zielsatz/Spec.lean`](grammatik/Grammatik/Zielsatz/Spec.lean),
  proof `Zielsatz/Beweis.lean`, tag `milestone-2026-09-15-gabbro-ziel`), with a witness on a
  non-degenerate two-thread program. `#print axioms gabbro_ziel`: `propext`, `Classical.choice`,
  `Quot.sound` — which says the PROOF is valid, not that the statement is the right one. Three
  limits, all load-bearing:
  - The checker in the statement (`C.akzeptiert`) is the **Lean** checker. The tool people run is
    the **Rust** checker; the bridge to it and to the binary is translation validation (T1–T5),
    and it is open.
  - The third independent review ([`messung/URTEIL-OPUS-2026-09-15.md`](messung/URTEIL-OPUS-2026-09-15.md),
    [`messung/URTEIL-MUSE-2026-09-15.md`](messung/URTEIL-MUSE-2026-09-15.md)) found a named gap in
    the STATEMENT: an unsatisfiable lock invariant emptied the user obligation (P1); the
    program's starts, invariants and axiom ensures were free parameters (P2); payloads had no
    race conjunct (P3). All three are repaired (SATZKARTE §22). The fourth round found one more
    unnamed gap -- an out-of-range float literal emptied the obligation through a "hardware"
    stop (F1) -- plus a global-only deadlock leg (F2) and unlisted stop classes (F3); all
    repaired, `gabbro_ziel` re-proved (SATZKARTE §23). The fifth round found that decoding
    (einpassen) did not cover sums, floats and function pointers (G1, repaired, SATZKARTE §24).
    The sixth round -- both reviewers independently, a systematic sweep -- reads *the goal with
    named gaps, no unnamed gap found*; its one remark, answers at empty types (W1), is closed in
    the Lean checker Bool (component `antwortenB`, SATZKARTE §25) and in the Rust checker
    (`N310`–`N314`). Tag `milestone-2026-09-15-zielsatz-bestaetigt`.
  - What may be said: *the goal theorem is proved over the model, with a witness and
    non-degeneracy.* Not: *Gabbro is verified.*
- **The chain of section 4 is closed for one program.** `beispiele/104`, theorem
  `schlusssatz_104` (single-threaded; the runtime start and the binary-run correspondence as
  hypotheses, the C compiler and the hand transcription of the emitted text named). Every other
  program: open — chain count 1 of 101 (`instrumente/zaehle-kette.py`). Concurrent translation
  validation (stage b) is not started.
- **The proof-to-code ratio has no measured value.** The floor is about 0,5 : 1 — the abstract
  specification itself — and Gabbro does not claim to prove functional correctness, so the true
  figure is strictly above it. The upper bound is unknown, and a number without a source list
  does not belong in a document.
- **Caprock is not written in Gabbro yet.** Fragments are, with origin and verdict in
  [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md). The acceptance criterion is Caprock in
  full with a green run, and it is not close.

## 7. Try it

Zero external dependencies: the three crates depend on `std` and on each other, and on nothing
else. There is no lock file to trust and no registry to reach.

```
git clone https://github.com/SimonVitzethum/Gabbro
cd Gabbro
cargo install --path crates/gabbro-cli     # `gabbro` into ~/.cargo/bin
gabbro check beispiele/01-tabelle.gab
```

**Rust 1.86 or newer**, measured rather than guessed: `f64::next_up`/`next_down` became stable
there, and older toolchains end at `E0658`. **`cc` is needed at run time, not at build time** —
only `gabbro build` calls it, to compile the C this compiler emits.

```
cargo run --bin gabbro -- check beispiele/*.gab        # check files
cargo run --bin gabbro -- passes                       # what each pass does and does NOT do
cargo run --bin gabbro -- templates                    # the proof-template register
cargo run --bin gabbro -- obligations beispiele/*.gab  # what a HUMAN still owes -- counted, not discharged
cargo test --no-fail-fast                              # the test corpus
./instrumente/abnahme.py                               # every guardian, one command, per-guardian verdict
./instrumente/mutiere-pruefer.py                       # damage one rule at a time: 413 mutations, one anchor each
./instrumente/pruefe-emission.sh                       # every emitted unit must compile
isabelle build -d beweise -c Gabbro                    # the machine-checked templates
```

`gabbro passes` prints what each pass does **not** check. A tool that lets unchecked silence
look like a green result is a false green.

## 8. How to read this folder

**Every number in these documents carries the command that produced it.** A number without a
source list does not belong here — it is not wrong, it is uncheckable, and that is the more
expensive state. When you find a figure, you can re-run it.

| File | Role |
|---|---|
| [`TODO.md`](TODO.md) | open items only, cut by the stages of the plan |
| [`DONE.md`](DONE.md) | finished items only — every entry carries its evidence |
| [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) | the language: four mechanisms, two declaration rules, pairing, entry, boot, induction |
| [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) | the grammar, and what deliberately does not exist |
| [`dokumente/BEWEIS.md`](dokumente/BEWEIS.md) | the proof architecture — and the failure record of the emitter, in full |
| [`dokumente/PLAN.md`](dokumente/PLAN.md) | the way there: phases with two-sided gates |
| [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md) | everything that was run — what is not in here was not measured |
| [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md) | Caprock areas written out in Gabbro, with origin and verdict |
| [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md) | what was already wrong about this design, with the lesson |
| [`dokumente/WERKZEUGKASTEN.md`](dokumente/WERKZEUGKASTEN.md) | working rules from our own mistakes, each with the damage it was paid for |

Three sentences this folder keeps coming back to:

> **A number without a source list does not belong in a document.** It is not wrong — it is
> uncheckable, and that is the more expensive state.

> **A rule with no mutation against it is not covered, it is undamageable.** Zero mutations on a
> surface is not coverage; it means nothing there can break visibly.

> **Not refused is not confirmed.** Where an analysis is a lower bound it neither rejects nor
> approves — the third state has to exist, or the tool lies in one direction.

## 9. Versions and language

```
0.0.1    now, the first tag
0.1.0    beta
1.0.0    alpha
```

*That names `1.0.0` "alpha" after `0.1.0` "beta", which is the reverse of the usual order. It is
the intended scheme and not a typo.*

The working language of this repository is **English** — sources, documents, commit messages and
diagnostics. The translation is running rather than finished, and it cannot be one sweep:
several guardians and test files assert German strings, so the prose and its checkers have to
move in lockstep. Identifiers inside the example corpus are German and stay that way; they are
data for the grammar, not prose.
