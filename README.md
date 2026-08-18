# Gabbro

**A language whose point is to make seL4-style proofs cheap.** One output: **C plus inline
assembly**. Compiler in **safe Rust** (`forbid(unsafe_code)`).

The purpose is not to have another language. It is to **write a kernel in it and then verify
that kernel cheaply** — Caprock in full, with a green acceptance run.

> **License: AGPL-3.0** ([LICENSE](LICENSE)) — **with an additional permission that answers the
> important question up front:** *what you write in Gabbro is not a derived work.* Your
> program, the generated C and the binaries are yours, under any license you like. **The
> condition is one line:** generated C files and binaries carry a notice saying they came out
> of Gabbro. Details and the legal reasoning in [LIZENZ-ZUSATZ.md](LIZENZ-ZUSATZ.md).

## The goal, in one sentence

> **Gabbro proves everything except functional correctness — on a multicore kernel with DMA.**

All **plumbing** — index, overflow, **alias**, frame, lock, race, termination, phase, leafness,
publication, refinement — is carried by the language. **Eight of the eleven classes are carried
today**; the three that hang no longer hang on a missing pass, but each on something different:
*race* on the axiom layer, *phase* on «B37», *refinement* on the code generator that does not
exist.

> **Multicore and DMA are set, not optional.** That is a statement against the most convenient
> of all simplifications: **seL4's verified configuration is single-core**, and its 239 458
> measured proof lines prove a kernel without real concurrency. So for Gabbro the **pairing**
> (`publishes`/`awaits`) is not a "later", it is load-bearing, and the `dma` space carries real
> statements instead of a classification.

## The one number that defines success

**Proof lines : code lines.** seL4 sits at **20 : 1**. The floor — what no language can take
away — is about **0,5 : 1**, the abstract specification itself.

| | |
|---|---|
| **measured today** | **≥ 1,90**, open — and it hangs almost entirely on the **W column** |
| **target** | **0,5 : 1** |

**The measurement that produced that number also produced the sentence that matters more:**

> **The expensive obligations are many, but small.** 38 of 73 by head count (52 %) but only
> 34 % of the lines — a W obligation is on average **half the size** of a K or an A one. The
> distance to the floor therefore hangs on the W column, not on loop shapes.

**Which is why the dashboard carries a second number**, and it predicts maintenance rather than
writing: **W obligations per thousand lines, ≥ 0,63**. *Otherwise the folder optimises the
denominator that shines instead of the one that costs.*

## What is built

| | | |
|---|---|---|
| **Compiler** | 10 passes, 3 complete, 7 partial, **0 open** | 90 diagnostics · `gabbro paesse` |
| **Grammar** | **130 EBNF rules**, closed and reachable | vocabulary covers every terminal, 195 / 195 |
| **Proof templates** | **19, of which 4 are machine-checked** | Isabelle2025-2, `beweise/` |
| **Guardians** | 8, each with a two-way speech test | **65 of 65 mutations caught** |
| **Corpus** | 19 clean examples, 69 poison files, 79 tests | `cargo test` |

**The templates are the number to watch, not the passes.** They are the surface onto which
every rescue is deferred — *a template falls once, not per program* — and until 2026-08-16 that
sentence was a promise about ground nobody had walked on. **Four are walked now.**

## How to read this folder

**Every number in these documents carries the search path that produced it.** A number without
a source list does not belong in a document — that is rule W7, and it was paid for three times
in one day. When you find a number here, you can re-run it.

| File | Role |
|---|---|
| [`TODO.md`](TODO.md) | **open items only**, cut by role: decisions · measurements · build · bookkeeping |
| [`DONE.md`](DONE.md) | **finished items only** — every entry carries its evidence |
| [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) | the language: four mechanisms, two declaration rules, ordering pairing, entry, boot, induction |
| [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) | the grammar, and what deliberately does not exist |
| [`dokumente/BEWEIS.md`](dokumente/BEWEIS.md) | the proof architecture: criterion, machine and memory model, prover, the seL4 comparison |
| [`dokumente/PLAN.md`](dokumente/PLAN.md) | the way there — phases with two-sided gates, and the coverage assessment |
| [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md) | **everything that was run** — and what is not in here was not measured |
| [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md) | Caprock areas written out in Gabbro, with origin and verdict |
| [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md) | **what was already wrong about this design**, with the lesson |
| [`dokumente/WERKZEUGKASTEN.md`](dokumente/WERKZEUGKASTEN.md) | working rules from our own mistakes — each with the damage it was paid for |
| [`dokumente/AN-CAPROCK.md`](dokumente/AN-CAPROCK.md) | findings whose subject is Caprock — found here, belonging there |
| [`beweise/`](beweise/) | the Isabelle theories — each names what it does **not** prove |

## Running it

```
cargo run --bin gabbro -- pruefe beispiele/*.gab     # check files
cargo run --bin gabbro -- paesse                     # what each pass does and does NOT do
cargo run --bin gabbro -- schablonen                 # the proof-template register
cargo test                                           # 79 tests
./mutiere-pruefer.py                                 # damage one rule at a time: 65 of 65
./pruefe-syntax.sh                                   # grammar against the corpus, zero build warnings
./pruefe-klauseln.py                                 # declared, exported, never read
./pruefe-widerruf.py                                 # sentences the folder has revoked, still standing
isabelle build -d beweise -c Gabbro                  # the machine-checked templates
```

**`pruefe-widerruf.py` guards the class that cost this folder eight sites in three files on
2026-08-19** — a sentence that was true when written and says *"this can never work"* long
after it was built. *It prevents work rather than merely delaying it, and it does so
quietly, because it reads like a result.*

**`paesse` prints what each pass does *not* check.** A tool that lets unchecked silence look
like a green result is a false green — the same class of error `pruefe-syntax.sh` paid for
twice.

## The three sentences this folder keeps coming back to

> **A number without a source list does not belong in a document.** It is not wrong — it is
> uncheckable, and that is the more expensive state.

> **A rule with no mutation against it is not covered, it is undamageable.** Zero mutations on
> a surface is not coverage; it means nothing there can break visibly.

> **Not refused is not confirmed.** Where an analysis is a lower bound it neither rejects nor
> approves — the third state has to exist, or the tool lies in one direction.

## A note on language

**This README is English. Most of the folder is still German**, and the translation is running
rather than finished. The reason it cannot be one sweep: **six guardians and eight test files
assert German strings** — the check chain that makes this folder worth trusting is coupled to
the prose. Translating without moving them in lockstep would break exactly the thing that makes
the numbers above worth reading.
