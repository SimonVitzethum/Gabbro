# Gabbro

> **Already proven in Lean, not just proposed.** Gabbro is an actively developed systems
> programming language with a Rust implementation and a machine-checked Lean 4 formalisation
> of its core language model and safety properties: the goal theorem
> (`gabbro_ziel : GabbroZiel`) is proved over the model, with a witness on a real two-thread
> program. What that covers — and what it does not — is stated in §5.

> **The long-term usability goal is to make formally verified systems programming
> approximately as accessible as writing ordinary low-level software in languages such as
> Zig.** Users should not need a proof assistant for routine safety properties; the language
> design and the verifier discharge those, leaving programmers with application logic,
> explicit contracts, and named hardware assumptions. Verification does not become invisible —
> its practical cost comes down to something close to conventional systems programming.

**A systems language that carries the proof plumbing, so that verifying an operating system
costs a fraction of what it costs today.** One output: C11 plus inline assembly. The compiler
is safe Rust (`forbid(unsafe_code)`) with zero external dependencies.

The point is not to have another language. The point is to write an operating system in it —
**Caprock** — and then verify that system cheaply.

> **License: AGPL-3.0** ([LICENSE](LICENSE)) — what you write in Gabbro is not a derived work:
> your program, the generated C and the binaries are yours, under any license you like.
> **The condition applies only if you call the result formally verified or secure**: then the
> generated files say which checker said so. Claim nothing and you owe nothing.
> Details in [LIZENZ-ZUSATZ.md](LIZENZ-ZUSATZ.md).

> **How this repository is written — AI agents, and where the human stands.**
> Implementation, checking and coordination are done by AI agents; the idea, the planning, the
> priorities and the oversight rest with one human — Simon decides what counts as reached, what
> is refused, and what gets merged. Every commit names its model (`Co-Authored-By`).
> **Nothing counts as done because an agent said so:** every reported number is re-measured at
> merge time, guardians run in both directions, and a claim bigger than its proof gets sent back.

---

## 0. Check the central claim yourself — two commands, five minutes

**Everything below is a claim. This section is how you stop taking it on trust.** The one
sentence this project stands on is proved in Lean 4 over a model of the language:

```bash
git clone https://github.com/SimonVitzethum/Gabbro && cd Gabbro/grammatik
lake build Grammatik.Zielsatz.Beweis Grammatik.Zielsatz.Proben Grammatik.Zielsatz.ProbenW1
lake env lean NachpruefungZiel.lean     # prints the axioms of every sentence named below
```

**Measured, not estimated** (2026-09-15, 16 cores, from an empty build directory): the build is
**4 min 33 s** wall clock (90 modules, peak **2,3 GB**); the check itself takes **0,16 s**.
`elan`/`lake` come from [leanprover/elan](https://github.com/leanprover/elan); the toolchain
(Lean 4.33.1) pins itself from `grammatik/lean-toolchain`. **No mathlib, no other dependency.**
The full library (`lake build`, 249 modules incl. translation validation) takes **5 min 06 s**
and peaks at **6,51 GB** — it fits on an ordinary laptop. (Before 2026-09-15 it needed
25 minutes and 72 GB; cause and repair are in [`dokumente/OFFEN.md`](dokumente/OFFEN.md) O13.)

What the second command prints, and what each line is worth:

| Printed line | What it means |
|---|---|
| `Zielsatz.gabbro_ziel depends on axioms: [propext, Classical.choice, Quot.sound]` | the goal theorem uses **only Lean's standard three** — no `sorryAx`, no axiom of ours. **A `sorryAx` here would mean it is not proved** |
| `…gabbro_ziel_zeuge…` | a two-thread program that moves memory satisfies it, so the sentence is not empty |
| `…probeA_widerlegt_gilt…`, `…probeD_…`, `…w1_abgelehnt…` | programs the checker **refuses** — a checker that accepts everything would make the theorem worthless |
| `…schlusssatz…`, `…kette_104_zeuge…`, `…kette_108_zeuge…`, `…K124.schlusssatz_124…` | translation validation, source text → model → emitted C (needs the full build, not the cheap check) |

**What those lines do NOT say:** an axiom list proves a *proof* valid, not that the *statement*
is the right one — that is a reading job. The statement is written to be read:
[`grammatik/Grammatik/Zielsatz/Spec.lean`](grammatik/Grammatik/Zielsatz/Spec.lean), whose header
carries the one assumption list and the NOT-CLAIMED list. The honest sentence is
**"the goal theorem is proved over the model, with a witness and non-degeneracy"** — not
"Gabbro is verified". The checker in the theorem is the **Lean** checker; the Rust tool is
bridged to it by translation validation, closed for three programs and open for the rest (§5).

---

## 1. The problem

seL4 is the honest reference point: a verified microkernel at roughly **20 lines of proof per
line of code** — single-core, no DMA.

Most of such a proof is not the interesting part. It is **plumbing**: index bounds, overflow,
aliasing, framing, lock order, data races, termination, phase, leafness, publication,
refinement. The same eleven classes in every kernel ever written.

Gabbro's claim is that plumbing belongs to the **language**, not to the proof:

> **Gabbro's goal: the user proves only their own logic and named hardware assumptions; the
> language carries the rest — on a multicore kernel with DMA.**
>
> What is proved today is narrower, and it is stated in exactly one place: the header of
> [`grammatik/Grammatik/Zielsatz/Spec.lean`](grammatik/Grammatik/Zielsatz/Spec.lean).
> Where this README and that header disagree, the header wins.

**Multicore and DMA are set, not optional.** The pairing (`publishes`/`awaits`) is load-bearing,
and the `dma` space carries real statements — a statement against the most convenient of all
simplifications.

## 2. Why this is not a solver problem

The other way is an SMT solver: annotations plus Z3 (Verus, Dafny do that well). Gabbro does
not, for two reasons.

**A refusal is better than a timeout.** Where a solver gets slow, a grammar says which
construct it will not carry and why, by name. The compiler ships **472 diagnostics** and no
search procedure.

**A template falls once, not per program.** Every carried construct turns into one generator
obligation — proved a single time, over the semantics — instead of one obligation per program.
That amortisation is the whole economic argument, and it is measurable rather than rhetorical.

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
writes what, what it costs, and that the token moves exactly once — the rest follows from the
grammar.

## 3. How the proof works: the checker is not trusted

The Rust checker and emitter — around 110 000 lines — will **not** be verified. Instead the
compiler is treated as untrusted and made to show its work: **for every program it accepts, it
emits a certificate, and Lean checks that certificate.** Today that holds for the programs
listed CERTIFIED in
[`grammatik/Grammatik/Zertifikat/REGISTER.txt`](grammatik/Grammatik/Zertifikat/REGISTER.txt);
every other accepted program is listed there by name as not claimed, and a test fails if one is
neither. The closing theorem the design aims at:

> **Lean accepts the certificate ⟹**
> **(1)** the source text parses to a program `P`, and
> **(2)** `P` satisfies the model — types, safety, lock order, and
> **(3)** the emitted C refines `P`.

So every run of the C corresponds to a run of `P`.

**The failure mode is one-way.** A broken checker can only reject good programs. It can never
let a bad program past. (The two real defects this project shipped both sat *in the emitter* —
see [`dokumente/BEWEIS.md`](dokumente/BEWEIS.md). Certificate checking is the structural answer
to that class.)

**Trust base:** the Lean kernel, the C compiler, the hardware profile, and named assumptions
about devices and the scheduler — as premises *inside* the theorem, not prose beside it.

### The five pieces

| | what it establishes | status |
|---|---|---|
| **T3 — Parser in Lean** | source text → `P`, so the certificate starts from the source | lexer, expressions, statements and items are in; generics and the print/parse round-trip are in flight |
| **T1 — Model certificates** | `P` satisfies the typing and safety rules, per constructor | all 40 expression and all 50 statement constructors carried in Lean; Rust prints statement certificates for 47 of 253 bodies |
| **T4 — Semantics of the emitted C** | what the generated C means: memory model, integer semantics, UB list, one lemma per form | 48 of 73 emitted forms have their lemma; a guardian goes red the moment the emitter produces a form without one |
| **T2 — Correspondence re-checker** | *this* C program consists of exactly those correspondences | built as `korrOk` (`KorrespondenzAllg.lean`): 23 expression arms plus block structure, each with a planted-defect check; wiring it per program is open |
| **T5 — Proof templates** | each recurring obligation gets a soundness theorem over the real semantics | 12 of 23 machine-checked (`gabbro schablonen`); the rest is still an abstract core |

### The concurrent half: model done, C chain open

The model is concurrent, and since 2026-09-26 the emitted C is too (runtime `start` / `child`
lowered to threads via our own raw `clone` + `futex`, no libc threading). DRF-SC is proved
over a weak memory model for the fragment, under the named assumptions in the `Spec.lean`
header. Open: the correspondence between a model run and a C run with interleaving — the
largest single open piece.

### Order of work

1. Finish the parser: generics, round-trip.
2. Close the C gaps — tagged unions, error-reason numbering, the most frequent uncovered forms.
   Some will end as named assumptions: inline assembly and device reads have no C semantics.
3. Wire T2 per program.
4. Bind the remaining templates to the semantics.
5. The concurrent half.
6. The closing theorem with a witness on a real program, then on a program with real sharing.

## 4. Status

Every figure carries the command that produced it; every one can be re-run. Figures without a
fresh date were last fully measured on the date beside them.

| | | |
|---|---|---|
| **Compiler** | 12 passes, 3 complete, **9 carried with a named residue**, 0 partial, 0 open | 472 diagnostics · `gabbro paesse` |
| **Grammar** | **188 EBNF rules**, closed and reachable | vocabulary covers every terminal, 242 / 242 |
| **Pass register** | **198 sentences over 12 passes — 190 measured, 2 ARGUED, 6 CONJECTURED, 0 proved**, claiming 419 diagnostic codes. *A written sentence is not a proved one* | `gabbro paesse --je-satz` |
| **Proof templates** | **23, of which 12 are machine-checked**; all **15** Isabelle theories also exist in Lean (`grammatik/Grammatik/Isabelle/`, checked by every build); new proofs go to Lean only | Isabelle2025-2, [`beweise/`](beweise/) |
| **Corpus** | 152 clean examples, 838 poison files *(file counts 2026-09-30; 942 tests counted 2026-09-14, lane 177)* | `cargo test --no-fail-fast` |
| **Emission** | **250 of 250 units emit and compile** under `cc -std=c11 -Wall -Wextra -Werror`, at `-O0` and `-O2`, with the same result; 37 are also executed against a handwritten version *(run 2026-09-14)* | `./instrumente/pruefe-emission.sh` |
| **Guardians** | 56, *(count 2026-09-30, plus the server lane's `pruefe-seiten-zurueck.sh`; 55 on 2026-09-29; 52 on 2026-09-28, plus the GabbroV lane's `pruefe-beweis-tor.sh`, `pruefe-sperre-beweis.sh` and `pruefe-vorlagen.sh`)* each with deadline, two-way speech test, red on abort, pinned locale, and work quantity beside the verdict | `./instrumente/abnahme.py` |
| **Mutation** | **386 of 413 anchors hold**, and a run catches 375 of 376 valid mutations *(measured 2026-09-14)* | `./instrumente/mutiere-pruefer.py` |
| **Blind spots** | **73 blind · 175 covered · 24 poison-only · 12 no cell** *(of 285 pairs)* — poison-only is a hint, not a proof | `gabbro blindstellen` |
| **Usability** | 7.5 % of the teaching corpus and 12.7 % of real code **may fall** — split derivable / redundant / load-bearing | `gabbro zeremonie` |

The 15 theories in [`beweise/`](beweise/) hold 3 512 lines of Isar — the amortisation argument
as a *measurement*: the figure falls when a proved construct gets used, and rises when one gets
proved ahead of use.

## 5. What is not true yet

This section exists because the alternative is that a reader has to find it out.

- **No pass has been proved individually.** 198 written sentences, 190 of them *measured* —
  a poison probe falls or a mutation is caught. That measures the implementation on checked
  cases, never the rule, and never all cases.
- **What IS proved is the goal theorem over the MODEL** — and only there. `theorem gabbro_ziel :
  GabbroZiel` (statement
  [`grammatik/Grammatik/Zielsatz/Spec.lean`](grammatik/Grammatik/Zielsatz/Spec.lean), proof
  `Zielsatz/Beweis.lean`, tag `milestone-2026-09-15-gabbro-ziel`), with a witness on a
  non-degenerate two-thread program. `#print axioms gabbro_ziel`: `propext`, `Classical.choice`,
  `Quot.sound`. Six review rounds repaired P1–P3 (empty obligation, free parameters, payload
  races), F1–F3 (float stop, global deadlock, stop classes), G1 (decoding of sums/floats/fn
  pointers) and W1 (answers at empty types); round 6 found *"the goal with named gaps — no
  unnamed gap found"* (tag `milestone-2026-09-15-zielsatz-bestaetigt`, SATZKARTE §22–§25).
  - The checker in the statement is the **Lean** checker; the Rust checker's bridge to it and to
    the binary is translation validation (T1–T5), and it is open.
  - What may be said: *the goal theorem is proved over the model, with a witness and
    non-degeneracy.* Not: *Gabbro is verified.*
- **The chain is closed for five programs, by ONE generic theorem** (`schlusssatz`,
  single-threaded; `beispiele/104` and `108` by hand, `130`, `69` and `73` through the generic
  `ketteAllg` over table-free units, `bruecke/Bruecke/Quelle.lean`). Every other program is open —
  chain count 5 of 148 (`instrumente/zaehle-kette.py --lean`, 2026-09-30). Concurrent translation
  validation (stage b) is closed for one program (`schlusssatz_124`) and open in general.
- **GabbroV's proofs reach the goal theorem for five programs, and for every source the Lean
  front end accepts the statement is COMPUTED, not printed.** For a unit the Lean parser
  elaborates (`beispiele/104`, `108`, `130`, `69`, `73`; 5 of 148, `instrumente/zaehle-bruecke.py`),
  premise (b) is *derived* in Lean from GabbroV's duties (`bruecke/`,
  `messung/GABBROV-BRUECKE-REPORT.md`, `messung/PARSER-LANE-REPORT.md`), so chain and bridge are
  both closed end to end (5 of 148). The general statement is `nutzer_aus_quelle`
  (`bruecke/Bruecke/Quelle.lean`, axioms standard): `Pflichten src` is computed in Lean from the
  source text and `gabbro prove --template --source` writes a person's file from it. For every
  other program (b) is still an assumption; units with a shared atomic are not bridged.
- **Most accepted programs are not judged in Lean at all.** Of 199 accepted programs under
  `beispiele/`, 23 have a generated certificate; the other 176 are refused by the exporter and
  listed by name in
  [`grammatik/Grammatik/Zertifikat/REGISTER.txt`](grammatik/Grammatik/Zertifikat/REGISTER.txt).
  Even a certified program rests on the unverified exporter and, outside the closed chains, on
  the reading that the model is the C.
- **The proof-to-code ratio has no measured value** — and a number without a source list does
  not belong in a document.
- **Caprock is not written in Gabbro yet.** Fragments are, with origin and verdict in
  [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md). Full Caprock with a green run is the
  acceptance criterion, and it is not close.

## 6. Try it

Zero external dependencies: the three crates depend on `std` and on each other, and on nothing
else.

```
git clone https://github.com/SimonVitzethum/Gabbro
cd Gabbro
cargo install --path crates/gabbro-cli     # `gabbro` into ~/.cargo/bin
gabbro check beispiele/01-tabelle.gab
```

**Rust 1.86 or newer** (`f64::next_up`/`next_down` became stable there).
**`cc` is needed at run time, not at build time** — only `gabbro build` calls it.

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

## 7. How to read this folder

**Every number in these documents carries the command that produced it.** A number without a
source list is not wrong — it is uncheckable, and that is the more expensive state.

| File | Role |
|---|---|
| [`TODO.md`](TODO.md) | open items only, cut by the stages of the plan |
| [`DONE.md`](DONE.md) | finished items only — every entry carries its evidence |
| [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) | the language: mechanisms, declaration rules, pairing, entry, boot, induction |
| [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) | the grammar, and what deliberately does not exist |
| [`dokumente/BEWEIS.md`](dokumente/BEWEIS.md) | the proof architecture — and the emitter's failure record, in full |
| [`dokumente/PLAN.md`](dokumente/PLAN.md) | the way there: phases with two-sided gates |
| [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md) | everything that was run |
| [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md) | Caprock areas in Gabbro, with origin and verdict |
| [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md) | what was already wrong about this design, with the lesson |
| [`dokumente/WERKZEUGKASTEN.md`](dokumente/WERKZEUGKASTEN.md) | working rules from our own mistakes, each with the damage it was paid for |

Three sentences this folder keeps coming back to:

> **A number without a source list does not belong in a document.**

> **A rule with no mutation against it is not covered, it is undamageable.**

> **Not refused is not confirmed.**

## 8. Versions and language

```
0.0.1    now, the first tag
0.1.0    beta
1.0.0    alpha
```

*That names `1.0.0` "alpha" after `0.1.0` "beta" — the reverse of the usual order, and intended.*

The working language of this repository is **English** — sources, documents, commit messages and
diagnostics. Identifiers inside the example corpus are German and stay that way; they are data
for the grammar, not prose.
