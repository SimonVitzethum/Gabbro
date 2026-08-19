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
| **measured today** | **unknown, and above 0,5** |
| **target** | **0,5 : 1** |

<!-- widerruf:aus -->
**That is a withdrawal, dated 2026-08-19, and it replaces a number this folder quoted for four
days.** What stood here was `≥ 1,90`, and it was wrong in a way no rounding fixes.
<!-- widerruf:an -->

## Why the number was withdrawn

`Ueberschlag = w · 5,0 + (1 − w) · 0,3` was substituted with **`w` measured on Verus proof
bodies in Caprock**. That conflates two quantities the formula then multiplies together:

| | prover-dependent? |
|---|---|
| **the obligation mix** — how many of a kernel's obligations are value statements | **no.** `revoke` is a value statement no matter who proves it |
| **the line weight** — how many lines each one costs | **yes, entirely.** A Verus line is SMT-backed; the same theorem in Isar is a multiple, or a `by auto` |

**Verus is a defensible proxy for the first and none at all for the second** — and Gabbro's
proofs are Isabelle/HOL. *The number carried a proof economy that appears nowhere in this
folder.*

## Why no Isabelle-anchored number replaces it yet

The eleven theories in [`beweise/`](beweise/) are **entirely the (1 − w) side** — seven K,
three A, one about the checker, **zero W**. An Isabelle-anchored `w` would have numerator **0** by
construction, and the formula would return **0,30** — *below the seL4 anchor, hence a triumph,
and false.* That is the error class this folder already booked once, when `p_B3` was read as a
kernel-side `w` and produced 0,345.

**What is missing is not an Isabelle semantics of Gabbro** — the lowering to C is that, and
`spec fn`/`impl fn` stand in one language, so a value statement is proved over the
specification model like every existing theory. **What is missing is P6:** the *generated*
refinement obligation. Until it exists there is no W obligation that arose; there is only one
somebody would have to invent, and inventing the thing you then measure is the move R7 and W3
exist to prevent.

## What IS anchored on Isabelle today, and it is the carried side

```
1 790 lines of Isar  ·  9 proved generator templates  ·  142 corpus sites
                        → 12,6 lines per site (1 950 across all eleven theories)
```

> **It ROSE on 2026-08-19, from 10,4** — `Table_Ops_Erhaltung.thy` came in at 311 lines and
> `ops` has **zero** corpus sites, so the numerator grew and the denominator did not. *That is
> the honest behaviour of the figure and worth stating out loud: it falls when a proved
> construct gets used, and rises when one gets proved ahead of use.* **Proving before building
> is the folder's own rule (K11.3.2), and this is what it costs on the dashboard.**

**The only figure in this folder resting on the prover it actually uses.** It says nothing
about functional correctness — it says the amortisation argument as a *measurement* rather than
a claim: *a template falls once, not per program.*

## And why the replacement still says something

**Above 0,5 is not a hedge, it is an argument.** `0,5 : 1` is the abstract specification, and
Gabbro does not claim to prove functional correctness — so `W > 0`, so the metric is strictly
above the floor. **What has no bound today is the upper one**, and quoting a number for it
would be the fourth substitution in a row.

> *W7: a number without a source list does not belong in a document. It is not wrong — it is
> uncheckable, and that is the more expensive state.*

**What survives the withdrawal is the count, and it is the half that was never Verus's:**

> **38 of 73 obligations are value statements** (52 %) — the ceiling of step assurances covers
> a **minority**. *Which obligations a kernel has is a property of the kernel; only what each
> one costs in lines belongs to the prover.* **The head count stands, the line share went with
> the number.**

> ~~*"many, but small" — 52 % of the obligations, 34 % of the lines*~~ — **withdrawn
> 2026-08-19 with the metric.** The "small" was measured in Verus lines, and Isar lines are
> not those. *It may still be true; today nothing supports it.*

**Which is why the dashboard carries a second number**, and it predicts maintenance rather than
writing: **W obligations per thousand lines, ≥ 0,63**. *Otherwise the folder optimises the
denominator that shines instead of the one that costs.*

> **And the withdrawal of 2026-08-19 left it standing** — `38 / 60 756` counts obligations
> against kernel lines and never touches a proof line. *The second number was the
> prover-independent one all along, and nobody noticed until the first one had to go.*

## What is built

| | | |
|---|---|---|
| **Compiler** | 10 passes, 3 complete, 7 partial, **0 open** | 131 diagnostics · `gabbro paesse` |
| **Grammar** | **139 EBNF rules**, closed and reachable | vocabulary covers every terminal, 206 / 206 |
| **Proof templates** | **20, of which 9 are machine-checked** | Isabelle2025-2, `beweise/` |
| **Guardians** | 10, each with a two-way speech test | **151 of 152 mutations caught** *(run 2026-08-19)* |
| **Corpus** | 31 clean examples, 111 poison files, 126 tests *(run 2026-08-19)* | `cargo test` |

> **Eight of these numbers stood wrong until 2026-08-19**, and the guardian that now holds
> them was extended on the day it found them. *The number was maintained, the source was
> not* — the same class as the six closed `gap:` lines and the eight revoked sentences.
> Everything countable without a compiler run is now held mechanically by `pruefe-todo.py`;
> the two that need a run carry their measurement date.

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
cargo run --bin gabbro -- pflichten beispiele/*.gab  # what a HUMAN still owes -- counted, not discharged
cargo test                                           # 126 tests
./mutiere-pruefer.py                                 # damage one rule at a time: 151 of 152
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
