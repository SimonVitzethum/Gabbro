# Gabbro

**A language whose point is to make seL4-style proofs cheap.** One output: **C plus inline
assembly** — **all 50 corpus examples emit it, and all 50 compile** under `cc -std=c11 -Wall
-Wextra -Werror -O2`. Compiler in **safe Rust** (`forbid(unsafe_code)`).

> **Until 2026-08-20 that sentence carried no figure, and twelve of the 38 produced nothing.**
> Every one of the twelve refusals was named and reasoned (`C001`) — that was the point of the
> emitter and it stays the point. But *a claim without its number is a claim about a fragment*,
> and [`TODO.md`](TODO.md) said so about itself before anyone else did.

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
publication, refinement — is carried by the language. **Nine of the eleven classes are carried
today** *(corrected 2026-08-24: `phase` had stood among the hanging ones with the reason
«B37» — and `PFLICHTEN.md` records «B37» as **closed on 2026-08-17**, twice and with a date.
`gabbro paesse` reports the pass as `CARRIED`, its residue as a **decision**, not a gap:
the softer reading with a stage SET, deliberately not built. The README carried the older
sentence for a week)*; the two that hang no longer hang on a missing pass, but each on
something different:
*race* at **exactly three of its 28 forms** (re-measured 2026-08-24, `messung/RACE.md`: 22 rest
on a RULE, 2 on the axiom layer, 1 on both, **3 on nothing** — and those three are the ALIAS.
**`A1` closed on 2026-08-24 with `R007`**: it was the only one of the four decidable without an
alias analysis, and `gabbro alias` had counted the site for three days before a pass refused it),
*refinement* on the Isabelle semantics of a body, which P6 laid bare.

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

The 15 theories in [`beweise/`](beweise/) are **entirely the (1 − w) side** — eight K,
three A, one about the checker, one about the BRIDGE, **zero W**. An Isabelle-anchored `w` would have numerator **0** by
construction, and the formula would return **0,30** — *below the seL4 anchor, hence a triumph,
and false.* That is the error class this folder already booked once, when `p_B3` was read as a
kernel-side `w` and produced 0,345.

~~**What is missing is not an Isabelle semantics of Gabbro** — the lowering to C is that, and
`spec fn`/`impl fn` stand in one language, so a value statement is proved over the
specification model like every existing theory. **What is missing is P6:** the *generated*
refinement obligation.~~ — **revoked 2026-08-21 (`WK1`), by the build of P6 itself.**

**P6 exists since 2026-08-21** ([`messung/P6.md`](messung/P6.md)): `gabbro pflichten
--isabelle` writes the generated refinement obligation, and Isabelle checks it green — for
**one** of 47 obligations, and that one is a `K`, not a `W`. What the build laid bare is the
item underneath it: **16 of the 23 genuinely open obligations hang on the Isabelle semantics of
a Gabbro BODY**, 7 on the world model. *The lowering to C is a meaning for the COMPILER, not
one for the PROVER* — and until a body has the second kind, P6 produces `K` obligations and no
`W`. The metric stays withdrawn, and it is no longer P6 that holds it.

## What IS anchored on Isabelle today, and it is the carried side

```
2 007 lines of Isar  ·  9 proved generator templates  ·  142 corpus sites
                        → 14,1 lines per site (3 512 across all 15 theories)
```

> **It ROSE on 2026-08-19, from 10,4** — `Table_Ops_Erhaltung.thy` (311 lines) and
> `Gruppe_Erhaltung.thy` (217) came in, and `ops` has **zero** corpus sites while `group` has
> **one**, so the numerator grew and the denominator barely moved. *That is
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
| **Compiler** | 12 passes, 3 complete, **9 carried with a named residue**, 0 partial, 0 open | 268 diagnostics · `gabbro paesse` |
| **Grammar** | **154 EBNF rules**, closed and reachable | vocabulary covers every terminal, 218 / 218 |
| **Proof templates** | **21, of which 10 are machine-checked** | Isabelle2025-2, `beweise/` |
| **Pass register** | **86 statements over 12 passes — 74 measured, **2 ARGUED**, 5 conjectured, 0 PROVED.** 50 of 268 diagnostics still owe one, and that number is a **ratchet**: it may fall, not rise. *A written statement is not a proved one — the third column is the whole rest* | `gabbro paesse --je-satz` · `./instrumente/pruefe-saetze.py` |
| **Guardians** | 29, and ~~44 of 44~~ ~~45 of 45~~ ~~47 of 47~~ ~~49 of 49~~ ~~50 of 50~~ ~~52 of 52~~ ~~53 of 53~~ ~~54 of 54~~ ~~55 of 55~~ **56 of 56 instruments carry all five requirements** — four read statically (deadline · two-way speech test · red on abort · **pinned locale**), the fifth (**work quantity beside the verdict**, W17) measured only by `--lauf`, held by `./instrumente/pruefe-waechter.py`. *The locale demand joined on 2026-08-25: under `de_DE.UTF-8` the linker says `Mehrfachdefinition von`, and `pruefe-emission.sh` reported an error that did not exist.* *The static half reads SOURCE; `--lauf` runs the light ones under a deadline* | **294 of 294 mutations caught** *(run 2026-08-24, `ki-pc-fisch-101`)* |
| **Acceptance** | **one command over all of them**: `./instrumente/abnahme.py` reads the DIRECTORY, not a list, and says per guardian **green · RED · HALF-MEASURED · ABORTED · NOT RUNNABLE · skipped** — *a run that measured half must not look like one that measured all of it* (W26) with the **work quantity beside the verdict** — *a run that drives zero is red* (W17). Until 2026-08-30 there was no such run: §1.7 named eleven of 26, **seven stood in no list at all**, and two red ratchets rode along for two days and four merges. *A guardian nobody runs cannot be told apart from one that does not exist.* `--voll` adds the four expensive ones; the quick run **names** them instead of dropping them | `./instrumente/abnahme.py` *(first run 2026-08-30: 24 of 27 driven, 22 green, 2 RED — precisely the two booked ratchets)* |
| **Corpus** | 64 clean examples, 404 poison files, 378 tests *(run 2026-09-02 on `ki-pc-fisch-101` -- the `free -g` beside it stands in the commit, not in this cell: a memory figure in a CORPUS row is a number the guard reads as corpus data)* — the newest is `beispiele/64-writes-a-whole-buffer.gab`, which prints a whole buffer through ONE `write(fd, p, n)` instead of a `putchar` per byte. **What is bound at the C boundary is what carries its end in the SIGNATURE** -- `requires n <= KAP` is an obligation `M115` discharges at the call site, and a terminator scan leaves nothing to discharge (`N052`, new; `beispiele/63-druckt.gab` next door is the value-taking form) | `cargo test` || **Emission** | **52 of 52 examples emit C, and all 52 compile** under `cc -std=c11 -Wall -Wextra -Werror`, at **`-O0` and `-O2`**, with the same result — **24 of them are also run and compared against a handwriting**, and one of those is a LIBRARY CHAIN across three separately compiled units and a linker, and under `-fsanitize=undefined` | `./instrumente/pruefe-emission.sh` *(run 2026-08-28)* || **Usability** | **6.7 % of the teaching corpus and 12.8 % of REAL code may fall** — 1156 and 109 clause sites, split derivable / redundant / load-bearing. The calibration travels with the tool (`--tafel`, per rule a may-fall AND a reason), because an uncalibrated usability number makes `effects` and `costs` the cheapest thing to drop | `gabbro zeremonie` · `./instrumente/zaehle-zeremonie.py` |
| **Blind spots** | **79 blind · 168 covered · 25 poison-only · 13 no cell** *(of 285 pairs)* — four parts on purpose: a removal leaves numerator *and* denominator, and `poison-only` is a hint, not a proof | `gabbro blindstellen` |

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

## Installing it

**Zero external dependencies** — the three crates depend on `std` and on each other, and on
nothing else (`cargo tree`, 2026-09-01). So there is no lock file to trust and no registry to
reach:

```
git clone https://github.com/SimonVitzethum/Gabbro
cd Gabbro
cargo install --path crates/gabbro-cli     # `gabbro` into ~/.cargo/bin -- 11,8 s, 4,9 MiB
gabbro check beispiele/01-tabelle.gab
```

**Rust 1.86 or newer**, and that is measured rather than guessed: `f64::next_up`/`next_down`
became stable in 1.86.0, and on 1.75 or 1.80 the build ends at `E0658`. **`cc` is needed at
RUN time, not at build time** — only `gabbro build` calls it, to compile and link the C this
compiler emits. Everything else (`check`, `emit`, `abi`, `costs`, `effects`, `obligations`,
`certificate`, `lean`) reads and writes files and needs no C compiler at all.

## Versions

```
0.0.1    now, the first tag
0.1.0    „ist dann beta"
1.0.0    „dann Alpha"
```

*Note that this names `1.0.0` "Alpha" after `0.1.0` "Beta", which is the reverse of the usual
order; it is the intended scheme and not a typo.*

## Running it

```
cargo run --bin gabbro -- check beispiele/*.gab      # check files
cargo run --bin gabbro -- passes                     # what each pass does and does NOT do
cargo run --bin gabbro -- templates                  # the proof-template register
cargo run --bin gabbro -- obligations beispiele/*.gab  # what a HUMAN still owes -- counted, not discharged
cargo test                                           # 252 tests
./instrumente/mutiere-pruefer.py                                 # damage one rule at a time: 340 mutations, 372 anchors
./instrumente/pruefe-syntax.sh                                   # grammar against the corpus, zero build warnings
./instrumente/pruefe-klauseln.py                                 # declared, exported, never read
./instrumente/pruefe-widerruf.py                                 # sentences the folder has revoked, still standing
./instrumente/pruefe-konstrukte.py                               # constructs at which nothing has ever fallen
./instrumente/pruefe-englisch.py                                 # the surface of Gabbro is English
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
