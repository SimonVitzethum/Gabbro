# Gabbro, ATS and Ada/SPARK — what differs, exactly

*Status 2026-09-17. This note compares architectures, not maturity: SPARK
ships certified systems, ATS is an academic lineage, Gabbro is pre-product
(Caprock is not written in it yet). The comparison is load-bearing anyway,
because the three make opposite bets on the same question: who proves
what, and what happens when the proof fails.*

*Read the Gabbro column as the architecture, not as the state of the build.
What is proved today is the goal theorem over the Lean model, with a witness
and non-degeneracy; "Gabbro is verified" is NOT a sentence this project may
say (`AGENTS.md` §1, README §6). Where the build stands, it is said below.
(Corrected 2026-09-21, review G13: the first version stated the architecture
in the present tense.)*

## 1. The one-paragraph version

- **Gabbro** carries the plumbing in the language and is built to check the
  *compiler's work per program*: an untrusted Rust compiler emits C plus a
  certificate, and Lean checks the certificate (source parses to P, P
  satisfies the model, the C refines P). The goal theorem says that a user
  proves only their own logic plus named hardware assumptions, over the
  model and for the Lean checker Bool. **Today that chain is closed for
  three programs** (104 and 108 single-threaded, 124 concurrent in stage
  (b)); for every
  other program the Rust checker and emitter are trusted, and the exporter
  reaches only a small part of the corpus (`TODO.md` §1).
- **ATS** (Hongwei Xi, ATS2/Postiats lineage) carries memory safety in
  *linear types* and expects the user to write proofs as terms (props,
  dataviews) for the rest; the compiler emits C that nothing re-checks.
- **Ada/SPARK** (SPARK 2014, GNATprove) proves the *source* against
  contracts the user writes (pre/postconditions, invariants) by generating
  verification conditions discharged with SMT solvers; the Ada toolchain
  itself is trusted, and the output is machine code, not C.

## 2. Who proves what

| | Gabbro | ATS | Ada/SPARK |
|---|---|---|---|
| Memory safety, race freedom, framing, lock order, overflow, bounds | the language (grammar + passes); refused by name where unwritable | linear/dependent types; manual proof terms where types do not reach | language restrictions (no aliasing of tasking state, SPARK subset) + flow analysis; the rest is contracts |
| Functional correctness of the user's logic | the user (`NutzerPflicht`: bodies at every budget + start duty), checked as Lean obligations per program | the user, as proof terms and props inside the program | the user, as contracts + loop invariants + ghost code, discharged per program by solvers |
| Hardware and foreign code | named assumptions with stated interfaces (the ONE list in `Zielsatz/Spec.lean`), inside the theorem as premises | `extern` declarations, trusted without check | `Import` + contracts, trusted; driver boundary is prose, not a premise |
| Time and costs | in the language: `costs` bounds, `held` lock bounds, deadlines, checked by the Rust checker. The goal theorem carries only the syntax-computed bound `ZeitAb`; declared `costs` are not in `Deklaration`, and the exporter drops `deadline` | not carried | not in the language (separate timing tools, uncertified) |

## 3. What happens when the proof fails

This is the sharpest difference, and it is deliberate on Gabbro's side:

- **Gabbro refuses by name.** Some four hundred diagnostics, no search
  procedure, no solver in the checking loop. A wall says which construct
  is not carried and why. There is no timeout, no "unknown", no
  may-be-proved-tomorrow: the answer is yes, or no with a code. A
  Lean-checked certificate behind the yes is the design; today it exists
  only where the chain is closed (see §1). (`MUSE-REPORT` culture: a wall
  that only yields by weakening is recorded as a finding, never bypassed.)
- **SPARK answers through solvers** (Alt-Ergo, Z3, CVC4 family). The
  failure modes are timeout, unknown, and unproved-but-possibly-true —
  the user then reshapes code, adds asserts, or writes ghost helpers
  until the solvers go through. Powerful, and genuinely used at scale;
  but the verdict depends on solver behavior, not only on the program.
- **ATS answers through types plus manual proof.** Where the type system
  does not reach, the user writes the proof term; a missing proof is a
  type error. No timeout class, but the proof burden is inline and
  per-program, with no amortization mechanism comparable to templates.

## 4. Proof amortization: once vs per program

Gabbro's economic argument: every construct the language carries becomes
*one* generator obligation, proved a single time over the semantics,
instead of an obligation per program that uses it. The state of that
argument: 21 templates, of which README §5 counts 10 machine-checked, and
only 5 are bound to the real semantics; the other 16 are still an abstract
core (README §4, `TODO.md` §0d). The per-program remainder is the
user's own logic, counted by `gabbro obligations` rather than discharged
by the tool.

SPARK amortizes differently: the *prover* is reused, but every program
pays its own verification conditions, loop invariants and solver time.
ATS amortizes least: proof terms are written per program, though libraries
of lemmas can be shared.

## 5. Concurrency and DMA

- **Gabbro is concurrent-first by requirement**: multicore and DMA are
  set, not optional. Race freedom (every carrier except atomics) is a
  conjunct of the goal theorem over the model; atomics are ordered by an
  axiom, and the C side assumes DRF-SC and is closed for one concurrent
  program (124). Locks carry invariants and floors, the pairing
  (`publishes`/`awaits`) is load-bearing, and thread start is runtime
  (assumption A4) moving into the language. **Not covered by the goal
  theorem:** one start running on several threads (the Rust checker admits
  pool-safe duplicates since lane 245, beyond the theorem; `OFFEN.md` O17,
  O18), same-core interrupt preemption (`OFFEN.md` O19), and DMA, which is
  a checked address space in the language but has no leg in `Zielsatz/`.
- **SPARK does Ravenscar**: a restricted deterministic tasking profile
  (fixed tasks, protected objects with ceiling locking, no dynamic
  tasking). Race freedom comes from restriction, DMA has no language
  story.
- **ATS has no verified-concurrency story** at comparable depth: threads
  exist as library/pthreads-level programming, without a proved race
  discipline.

## 6. Output and trust base

- **Gabbro emits C11 plus inline assembly** and is built to distrust its
  own emitter: each recurring C form is meant to get a correspondence
  lemma (a guardian names each form as lemma, assumption or uncovered),
  and the per-program certificate is meant to be re-checked in Lean. What
  stays trusted where that chain is closed: the Lean kernel, the C
  compiler, the hardware profile, named device and scheduler assumptions.
  **Where it is not closed, which is almost everywhere today, the Rust
  checker, the exporter and the emitter are trusted as well.**
- **ATS also emits C — unchecked.** The translation is trusted along
  with the compiler; there is no per-program artifact a second tool
  verifies.
- **SPARK emits no C.** Ada compiles through GNAT to machine code; the
  certification story (DO-178C, qualification kits) qualifies the
  toolchain instead of checking its output. There is no independent
  re-checker for a single build's claims.

## 7. Ghost code and erased material

All three erase: SPARK `Ghost` entities, ATS proof terms and views,
Gabbro ghost tokens (`linear ghost type`) and certificates. The
difference is what erasure is FOR: in SPARK and ATS it guides the prover;
in Gabbro the certificate is meant to be the product a second checker
verifies (today: for the programs of §1), and the ghost token is the ownership argument the grammar moves.

## 8. What is NOT claimed (Gabbro, read first)

`Zielsatz/Spec.lean` carries the NOT-CLAIMED list inside the reviewed
statement: termination and waiting bounds under fairness, stack depth,
the C and the hardware, weak memory beyond DRF-SC, unguarded publish/await
payloads, floats beyond the kernel IEEE model, starvation freedom,
invariants at entry, one start on several threads, and linking of
separately compiled units. Probabilistic statements and dynamic unbounded
structures are out of scope by decision, but are not in that list.
SPARK's and ATS's boundaries are documented differently (SPARK: what the
subset excludes, e.g. dynamic allocation and tasking outside Ravenscar;
ATS: what the user must prove by hand), but the honest comparison is
statement-to-statement, and Gabbro's statement is the one written to be
read.

## 9. When to pick which

- Pick **SPARK** to ship a certified system today, in Ada, with an
  established qualification path and industrial prover support.
- Pick **ATS** to experiment with linear/dependent types and proof terms
  inside one language, compiling to C, with no concurrency or timing
  story.
- Pick **Gabbro** if the bet holds that plumbing belongs to the language:
  multicore plus DMA, time as a first-class bound, refusals instead of
  timeouts, and a per-program certificate a second tool checks (the
  target; three programs today) — with
  the price stated up front (README §6, `OFFEN.md`, and §8 above):
  the chain is built program by program, and what is not yet carried is
  refused by name rather than promised.
