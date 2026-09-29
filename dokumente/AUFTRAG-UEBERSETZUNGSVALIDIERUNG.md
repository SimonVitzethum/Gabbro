# Assignment: translation validation — close the chain from source to C

*Written 2026-09-29 for a contributor joining the project (Simon's friend, possibly working with
an AI assistant). Self-contained: read this file first, then the files it names. The deep
reference is `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` (the plan, ~1,200 lines, with every
past measurement); this file is the entry point and the rules of the work.*

---

## 1. What translation validation is

Gabbro is a systems language whose safety guarantees (memory safety, race freedom, contracts,
lock discipline, …) are **proved once, for the language**, in Lean 4: the goal theorem
`gabbro_ziel` (`grammatik/Grammatik/Zielsatz/Spec.lean`) says that every program the checker
accepts behaves well **on the Lean model** (machine G).

But nobody runs machine G. What runs is the C that the Gabbro compiler (Rust, `crates/`) emits,
compiled by a C compiler. Between the proved model and the running code stand three programs
nobody has verified:

```
source text  --(Rust parser + exporter)-->  model program P in G   (the goal theorem speaks here)
             --(Rust emitter)------------->  emitted C              (this is what runs)
```

**Translation validation does not verify those Rust programs.** Instead, for each program, the
compiler prints *certificates*, and Lean re-checks them. When the check passes, a Lean theorem
holds for that one program:

1. **Parse fidelity** — the source text, parsed *in Lean*, is the program `P` the goal theorem
   talks about (the Rust parser is not trusted).
2. **Model judgement** — `P` is accepted and satisfies the goal theorem's premises.
3. **Emitter fidelity** — every run of the emitted C corresponds to a run of `P`, up to named
   assumptions (C compiler front end, hardware profile).

This is the generic **closing theorem** `schlusssatz` (`grammatik/Grammatik/Schlusssatz.lean`).
A program for which a Lean-checked instance of it exists has a **closed chain**.

The Rust compiler stays untrusted on purpose: a wrong compiler can only make a check *fail*
(a refusal), never make a wrong program pass. Directly verifying the Rust code was priced at
~700k proof lines and rejected (plan §0).

## 2. What it brings

- **Without it**, "Gabbro guarantees X" means "X holds for the Lean model of your program, if
  the Rust compiler is correct". **With a closed chain** it means "X holds for the C that
  actually runs, and the compiler's correctness was checked, not trusted" — only the named
  assumptions remain (§6).
- It turns a 170k-line Rust trusted base into a small set of Lean *definitions* a reviewer
  must read (the C semantics, machine G, the goal predicate).
- It is the difference between "verified language design" and "verified programs". It is also
  the strongest single piece of evidence for outside readers (e.g. a grant review).

## 3. Where it stands (measured; re-measure before you trust a number)

| Measure | Value | Command |
|---|---|---|
| **Chain count** (the ONE headline metric) | **2 of 129** programs: `beispiele/104`, `beispiele/108` (2026-09-26) | `./instrumente/zaehle-kette.py --lean` |
| Emitted C forms | 83 forms: 51 with a correspondence lemma, 4 named assumptions, **28 without semantics** (2026-09-28) | `./instrumente/pruefe-cformen.py` |
| Concurrent stage (b) | closed for ONE program (`beispiele/124`, `schlusssatz_124`), with `DRFSC` as a named premise | plan §7 |
| Correspondence checker T2 | built: `korrOk` (`KorrespondenzAllg.lean`), 23 expression arms + block structure | plan §6.2 |

**Where the other programs stop.** The chain is a series of *sieves*; a program must pass all of
them, so coverage is multiplicative:

| Sieve | What must succeed | Stopped there (last census, 2026-09-15/16) |
|---|---|---|
| **(a)** | the source parses and elaborates **in Lean** (`uebersetzeAllg`) | **~111 of 113 — the binding sieve**: 20 at the Lean parser (10 × `reserved head forall`), ~90 at elaboration (most: an item with no G form; 12 a unit without a table; 7 the type `bool`) |
| (b) | `gabbro lean-g` exports the program (diagnostic) | 15 pass |
| (c) | `gabbro certificate` prints every body (diagnostic) | 15 pass |
| (d) | every emitted C form has a lemma or is a named assumption | 55 pass |
| (e) | the generic correspondence certificate (`gabbro corr-lean`, `KCert`) prints with no refusal and matches the instance | 2 pass |

**Read this table carefully, it decides where to work:** the C forms (sieve d) are NOT what
keeps the count at 2 — **sieve (a), the Lean parser and elaborator, is.** A lemma for a C form
moves the chain count only for a program that already passes (a)–(c). Measured rule of the
project: *a first-refusal count is not a count of programs you would gain* — removing one wall
often reveals a second one behind it. Always measure with the chain counter, never estimate.

## 4. How to proceed

### 4.1 Setup

```bash
git clone https://github.com/SimonVitzethum/Gabbro.git && cd Gabbro
# Rust (stable, via rustup), a C compiler (gcc or clang), Lean via elan:
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
cargo build --release                                  # the compiler: target/release/gabbro
cd grammatik && lake build && cd ..                    # the Lean library (toolchain from lean-toolchain)
cd programmlogik && lake exe cache get && cd ..        # mathlib cache (needed by `cargo test`)
cd grammatik && lake env lean Nachpruefung.lean && cd ..   # prints the axioms of the goal theorem
```

The first `lake build` of `grammatik/` is long (it was measured at over an hour cold); later
builds are incremental. Machine: 16 GB RAM is comfortable; run ONE heavy job at a time
(`lake build`, `cargo test`, the chain counter) — a job killed by memory looks like a failure
and is not one.

### 4.2 The loop (every work item follows it)

1. **Measure first**: `./instrumente/zaehle-kette.py --lean` (per-program columns (a)–(e) and
   the chain count) and `./instrumente/pruefe-cformen.py`. If a tool says `ABBRUCH: the binary is
   OLDER than N source file(s)`, run `cargo build --release` — the guardian is right, it refuses
   to measure a stale compiler.
2. **Pick the wall** that the measurement shows blocks the most programs *at their first
   stopping sieve*, and check (by skipping it in a probe) what stands behind it.
3. **Build the smallest general fix** (a parser rule, an elaboration arm, a `korrOk` arm over an
   existing lemma, a C-form lemma) — never a fix keyed to one program's name.
4. **Prove it with a witness**: every new theorem whose premise quantifies over syntax gets a
   non-degenerate `…_zeuge` (a concrete program where the premise holds and the conclusion says
   something), and every new check gets a **planted defect** that it must reject (see
   `KorrespondenzWeitZeuge.lean` for the style: a positive probe AND a wrong one per arm).
5. **Re-measure** the chain count and the C-form census; write both numbers, with the command,
   into your report and into `TODO.md` §2.
6. **Close a chain** when a program passes (a)–(e): add a `Kette` instance with the marker
   `CHAIN-INSTANCE <program> <name>`, the source pinned byte for byte, and a file that applies
   `schlusssatz <name>`. Model: `Kette108.lean`. The counter only counts it when Lean re-checked
   it (`--lean`).

### 4.3 The work, in order (each item has a measurable finish)

**Stage A — sieve (a), the binding one** (`grammatik/Grammatik/Parser/`, the elaborator in
`Schlusssatz.lean`'s `uebersetzeAllg`, lowering `lowerAllg`)
- A1. Re-measure sieve (a) over today's corpus (TODO §2, first two items).
- A2. The Lean parser: the `forall` head (10 programs last time), the missing `;`/`{` shapes,
  `@version`. Finish: 0 programs stop at `parse:`.
- A3. The elaborator: the item kinds that have no G form yet, tables-less units, `bool`,
  `requires`. Each kind is one arm; measure which programs move past (a) and what stops them
  next.
- A4. T3 round trip for statements (`SAnw`), Parser/Rundlauf files (TODO §2).

**Stage B — the C side for the programs that now pass (a)–(c)**
- B1. `korrOk` arms for `if`, `traverse`, compound assignment, globals, `let` of a call,
  arithmetic — each over an existing lemma (TODO §2).
- B2. The C forms without semantics (`pruefe-cformen.py`, `KNOWN_UNCOVERED`): start with the
  small ones (`expr:neg`, `stmt:compound-other`, `expr:byte-reader-other`), then the big group
  that most others depend on — **structs and pointers in the memory model**
  (`CSpeicher.lean`: `stmt:store-field`, `stmt:store-deref`, `stmt:decl-ptr`, the aggregate
  forms). Decide the memory-model extension in writing *before* adding forms (plan §2: do not
  rewrite form semantics halfway). Finish: 0 forms in state (iii), or each remaining one turned
  into a named assumption with its reason.
- B3. A2 of the plan: a Lean C parser for the emitter's subset (`CParser/`), so every chain
  parses the emitted TEXT instead of a hand transcription (done for 104/108 — generalise).

**Stage C — generic closing, fewer hand-written parts**
- C1. Take the `Einheit` of a chain from the exporter instead of writing it by hand.
- C2. Discharge the "no model error" condition (the `abstieg` depth residue, TODO §2).
- C3. Export the arena (`OFFEN.md` O14).

**Stage D — concurrent programs (research-sized, only after A–C move the count)**
- The open items of plan §7.6 / TODO §2 stage (b): region serialisability, footprint soundness,
  the ticket lock as a proof, lock calls inside loops/branches, atomics.

**Realistic target for a first period:** Stage A plus B1, and the chain count moved from 2 to a
double-digit number — measured, with every new chain Lean-checked. That alone would be a
strong, reportable result.

## 5. Rules of the tree (non-negotiable; reviews reject violations however green the build)

- **No `sorry`, `admit`, new `axiom`, `native_decide`.** `#print axioms` of every theorem must be
  exactly `propext`, `Classical.choice`, `Quot.sound` (`Nachpruefung.lean` shows how).
- **Never weaken a statement to make it provable.** A theorem that became easier because its
  conclusion got weaker is a regression. The goal theorem's statement (`Zielsatz/Spec.lean`) is
  NOT yours to change — if you think it must change, write down why and ask Simon.
- **Witnesses** for every ∀-over-syntax theorem; **planted defects** for every new check.
- **Measure, don't estimate.** Every number in a report carries the command that produced it.
  A guardian that aborts (`ABBRUCH`) measured nothing — look for the numbers it no longer
  prints.
- **English** for code comments, documents and commit messages.
- **Emitted C is pinned byte for byte** in the chains. If you change `emit.rs`, the pinned texts
  of 104/108/124 change — re-measure every chain after any emitter change.
- **What you own:** the C-side Lean files (`CSemantik`, `CSpeicher`, `CFormen*`, `CParser/`,
  `KorrespondenzAllg`, `Korrespondenz*`, `Kette*`, `Schlusssatz*`, `Parser/`), the printer
  `crates/gabbro-check/src/corrlean.rs`, and the two counters. **Coordinate before touching:**
  `Zielsatz/` (the goal theorem), `programmlogik/` and `crates/gabbro-check/src/beweis.rs`
  (the GabbroV work, another contributor), `emit.rs` (shared with everyone).
- `cargo test --no-fail-fast` must stay at zero failures (without `--no-fail-fast` it reports
  only the first failure and hides the rest).

## 6. What translation validation does NOT cover (say this whenever you report a result)

- **The C compiler's back end**: a closed chain proves the emitted C *text* refines the model;
  that gcc/clang compile it correctly is an assumption (front end: "reads the subset as
  `parseC` does"). Removing it needs an ISA model and binary validation — a separate project.
- **The hardware**: `Profil.lean` and the device assumptions (`GerAnnahme`) stay named
  assumptions.
- **Concurrency beyond DRF-SC** on the C side (`DRFSC` is a premise of stage (b)).
- **The runtime** (thread creation, the lock primitive) enters as `LaufzeitC`.
- **The user's own logic proofs** — that is GabbroV (`programmlogik/`), a separate track.

## 7. How to hand in work

- Fork on GitHub, work on a branch, open a pull request against `master`. Keep PRs small: one
  wall or one arm per PR, each with its measurement (chain count and C-form census before/after,
  with commands) in the description.
- Write a short report per larger step into `messung/` (see existing `messung/*.md` for the
  style: what was measured, how, what changed, what is still open).
- Update `TODO.md` §2 (tick the item, put the measured number next to it) and, for new theorems,
  `dokumente/SATZKARTE.md` (a new section at the end).

## 8. Reading list, in order

1. This file.
2. `README.md` — what Gabbro is.
3. `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §0, §3, §5, §6.1–6.3 (the statement and the
   census), then §6.5 onwards as needed.
4. `grammatik/Grammatik/Schlusssatz.lean` (the theorem), `Kette108.lean` (a complete chain),
   `KorrespondenzAllg.lean` (the checker `korrOk`), `KorrespondenzWeitZeuge.lean` (probe style).
5. `instrumente/zaehle-kette.py` (header: exactly what counts as a closed chain) and
   `instrumente/pruefe-cformen.py` (the three states of a C form).
6. `TODO.md` §2 (the open items, kept current).
