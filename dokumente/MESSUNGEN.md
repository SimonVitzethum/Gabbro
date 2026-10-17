# Gabbro — the measurements

**What was measured, what it decided, and the command that measures it again.** The diary of how
these measurements were made (protocols written in advance, gates, invalid runs, corrections) is
in `git log`; this file keeps the *lasting* figures and verdicts. **What is not here is not
measured**, and a figure without a command is marked as a dated record.

## 0. Rules for a number in this file

1. **A live figure names the command that re-derives it** (§2). A figure that fell stays where it
   fell, with its date; no recorded figure is pulled up to a later state. That is a promise about
   the records, not about the file.
2. **A record is not a claim about today.** The tables of §6 are frozen results of one day. They
   have no command on purpose: giving a record a command turns it into a claim and would create
   two registers over one subject (W7). `instrumente/pruefe-zahlen.py` carries each of them in its
   `UNBEWACHBAR` register *with a written reason*, and a reason that no longer points at a line
   falls — so these tables are read by a guardian and must not be reworded.
3. **Every ratio names its denominator**, and the denominator of a population count is stated with
   the command that counts it (W11). A tool that cannot count says *not measured*, never zero.
4. **Gates are set in advance and not moved after the run** (R2); the verdicts below are
   *passed*, *missed* or *invalid*, and *invalid* means the measurement itself broke, not that the
   result was unfavourable. The rules `R1`–`R18` and `W1`–`W29` are in
   [`WERKZEUGKASTEN.md`](WERKZEUGKASTEN.md).
5. **Foreign corpora are read-only**: `../caprock-messbasis` (Caprock at `a1bf707`, x86-64 only),
   the Linux tree (`kernel/`, `mm/`), seL4's `l4v`, an external renderer. Nothing is copied into
   this repository, and a figure measured there has no command *here* (§6, "foreign corpora").

## 1. Verdict table — the thesis measurements

The language was built on a thesis: *a user proves only their own logic; the plumbing falls out of
the language.* Each row is a measurement that tested it. "Result" is the lasting outcome.

| # | Question (date) | Result | Verdict |
|---|---|---|---|
| M1 | Does the plumbing/logic split of 10 hand-translated fragments (74 obligations) support the design? (2026-08-14) | 19 of 57 plumbing obligations hang on the programmer (33 %); the 74 had no site list and was replaced | **refuted at 19 named sites** — an escalation: eleven classes, each given its construct |
| M2 | Reassignment, with sites: 239 obligations over the ten fragments (2026-08-17) | 173 plumbing (K), 66 logic (L); hanging H = 36 against a bar of 0; one disputed row | **gate missed**; the ratio L : K is the wrong statistic, **H is the measurand** (§3.1) |
| M3 | Is `narrow` (the emergency exit) frequent? (2026-08-14/15) | Rust count **invalid** (classifier error 40–60 % in one direction); over Gabbro source N = 2 in 791 lines, one of two is a checker limitation | count valid, **gate missed by the letter** (the protocol hung a gate on a quantity it declared non-measuring); the measurand became `N_ritus` / `N_folgenlos` (§3.2) |
| M4 | Where do indices take their bound from? (2026-08-14) | 268 sites in three files: `index into T` bounds 75.6 % (cap table) and 94.9 % (scheduler); the hard flow-sensitive class: 4 sites in 65 001 lines, all a bit position out of a word behind a zero check | **passes**; M1 needs one flow rule (a checked condition narrows the range in the branch afterwards) and a built-in `highest_bit` with a contract |
| M5 | Which kernel bodies cannot be written as a traversal? (B3, 2026-08-16) | 22 of 2 186 non-test bodies, 584 of 60 756 lines: **0.96 %**; **0 of the 571 `for` loops** run over a non-domain | **passed** (bar 5 %); a lower bound with four named reasons (§3.3) |
| M6 | Does `format` pay for itself in error frequency? (base rate, 2026-08-15) | 5 `repr(C)` formats in the tree, 5 commits touching one in 53 days, 0 occurred errors of the class (one documented near miss) | **the base rate does not carry `format`** — it earns its place by brevity and the near miss, not by frequency |
| M7 | Does the convergence bet hold (new constructs per area fragment fall)? (2026-08-16) | F7–F10: **0 new constructs**, but 3 changed meanings and 1 finding against the thesis | **holds in column 1** (vocabulary), **the trust surface grows** (column 2: «B37»–«B39») |
| M8 | How many closure uses need a construct? (2026-08-16) | the claimed 89 had no search path; reproducible population 64 (+ 441 closure literals, 270 in iterator adapters); the stored-handler class is **empty** | **gate void**; the item split into "callback with one implementation" (answered) and genericity |
| M9 | Where does the proof effort of seL4 sit? (l4v `f4940273`, ARM only, 2026-08-14) | 239 458 lines of functional correctness: invariants 32.1 %, abstract → executable 40.1 %, executable → C 27.8 %; plus 56 323 (+23.5 %) for security theorems | the "19.5 : 1" becomes checkable: ~40 % falls away structurally, ~28 % shifts into trust, ~32 % stays as invariant work (§3.5) |
| M10 | Does a second corpus agree? (K2: Linux `kernel/`+`mm/`, 2026-08-18) | `BUG_ON`/`WARN_ON` 2 034, `goto` 2 669, RCU 578 sites; 4 of 5 reconstructed fragments carry with no remainder | **found a class the first corpus never showed (RCU)**; independence disputed afterwards (`FRAGMENTE.md`) |
| M11 | Does the generated code lose to handwritten C? (C back end, 2026-08-20) | four loads, none over 25 %: format reader 1.244, `narrow … else` 1.062, `accumulates min` 1.02, table access 0.99 (Gabbro / hand) | **passes, narrowly**; two of my own set-ups were strawmen in my favour; legacy C back end — not a claim about the LLVM back end (§3.7) |
| M12 | How long does the Lean guardian take? (2026-09-01) | 457–482 s for 121 units (3.78–3.99 s per unit); the deadline of 600 s has 20 % room | **not a time reserve but a corpus reserve** (§3.8) |

## 2. Live counters — and how to measure them again

Every row is a command. The values are the last ones I know; *refresh them with the command, not
by editing the cell*. The guarded ledger of figures (`pruefe-zahlen.py` holds each against its
command) is [`messung/KENNZAHLEN.md`](../messung/KENNZAHLEN.md); this table is the map.

| Quantity | Command | Last value (date) |
|---|---|---|
| Poison probes / clean examples | `ls beispiele/gift/*.gab \| wc -l`; `ls beispiele/*.gab \| wc -l` | 898 / 170 (2026-10-17, measured while writing this) |
| Fragments clean / lowering / pierced | `./instrumente/zaehle-fragmente.py [--je-datei]` | 9 / 9 / 9 of 10; F3 is the exception (`FRAGMENTE.md` §3) |
| Mutation anchors that bite | `./instrumente/mutiere-pruefer.py --anker` (text counting, no build) | **388 of 422** (2026-10-17: 34 anchors measure nothing because the checker moved under them; the full run of 2026-09-03 caught 388 of 388 valid mutations, 375 of 376 under `cargo test` alone) |
| Mutation run over the whole checker | `./instrumente/mutiere-pruefer.py` (needs `crates/` clean; 13 min 20 s measured on 377 mutations, **not** re-measured for the later catalogue) | see CLAUDE.md for the booked catalogue size |
| Checking passes, pass sentences | `gabbro paesse` | 12 passes; **216 sentences: 208 measured, 2 argued, 6 conjectured, 0 proved** (2026-10-17) |
| Codes with / without a sentence | `./instrumente/pruefe-saetze.py` (ratchet: no new code without its sentence) | booked in `KENNZAHLEN.md` (198 sentences over 419 codes, 55 codes still without — 2026-08-31); not re-run today (the tool wants its own debug binary) |
| Template register | `gabbro schablonen` | **41 templates, 11 unproved, 30 machine-checked; 3 carried-unproved; 6 premises without a pass** (2026-10-17). `KENNZAHLEN.md` still books 23 entries / 11 unproved — that cell is stale against the command |
| Isabelle theories / Lean transfer | `ls grammatik/Beweise/*.thy \| wc -l`; `ls grammatik/Grammatik/Isabelle/ \| wc -l`; `./instrumente/zaehle-theorien.py` | 15 theories, 15 Lean files (2026-10-17); 3 512 lines, 101 sentences, 31 frozen proof searches (booked 2026-09-27) |
| Instruments | `ls instrumente/` | 95 entries: 54 `pruefe-*`, 22 `zaehle-*` (2026-10-17) |
| Number guardian | `./instrumente/pruefe-zahlen.py` | 80 figures with a command, 153 bold table figures without one (booked 2026-10-05; rewriting this file changes the second) |
| Hanging plumbing `H`, K/L columns | `./instrumente/zaehle-pflichten.py --haengend` / `--spalten` | H = 1, K = 173, L = 66 (booked, 2026-09-04) |
| `narrow` without effect | `./instrumente/zaehle-bereichspflichten.py` | `N_folgenlos` = 0 (§3.2) |
| Grammar | `./instrumente/pruefe-syntax.sh` | 189 rules, 0 open, 0 unreachable from `program` (`SYNTAX.md`) |
| Traversal bodies / duplicates | `./instrumente/zaehle-traversierungen.py` | 22 bodies, 0 duplicated (booked) |
| German comment lines in the checker | `./instrumente/pruefe-englisch.py` | 7 892 of 27 237 (booked 2026-09; a ratchet that falls) |
| Network stack against published vectors | `./instrumente/zaehle-netz.py` | 3 of 3 probes green |
| Format versions | `./instrumente/zaehle-formate.py` | 0 formats with a second version; 8 distinct `@version` declarations (16 text sites) |

## 3. The measurements, one by one

### 3.1 The obligation base — plumbing, logic and what hangs (M1, M2)

**The first split (2026-08-14)** over ten hand-translated fragments: 74 obligations, 17 logic,
57 plumbing, 19 plumbing hanging on the programmer (33 %). The 74 carried **no site list** and was
replaced, never repaired; `delete_leaf` had tipped from 3.6–6 : 1 to 1.75 : 1 on a recount (a
different counting unit). The assurance *"everything except the logic proof falls out by
construction"* was refuted at 19 named sites, by decision an *escalation* and not an abort.

**The paper gates before that (2026-08-13)**, on real Caprock code:

* the `device` block for `vtd.rs`: a factor of 15.1 against the whole 1 448-line file is
  *meaningless for the thesis* (it measures the size of the uncovered remainder); against what the
  block covers it is 3.2 (gate ≥ 5, **fallen**); 78.9 % of the file is not covered by a
  declaration; an honest Gabbro version of the whole file is ~1 353 lines (factor 1.07) — **the
  terseness thesis in its original form is refuted**, `device` is twice as terse on its own
  territory, which is a fifth of the file;
* `delete_leaf` twice: written out 3.6–6 : 1, above the abort mark of 3 : 1 (31 of 134 lines were
  not writable at all); over 67.3 % of the tree (44 832 lines) the pots were 15.1 % *expressible,
  obligation falls out by construction*, 65.1 % *expressible, needs a handwritten specification*,
  19.8 % *not expressible today* — the plan had reckoned with 10 % handwritten proofs; the
  assumption carrying the whole conditional yes did not hold;
* a metric built from unchecked assurances **rewards false assurances, because they are short**
  (an `ensures` that is wrong yet counted; the one functional property of a fastpath bound to no
  `ensures`; an `effects` list that forgets the foreign core's lock). Three rules without which
  nothing is measured: every counted `ensures` is held against the real code; a named property
  bound to no postcondition does not count; `effects` is checked against the actual accesses.

**The reassignment (2026-08-17)**, with a `file:line` per obligation
([`PFLICHTEN.txt`](PFLICHTEN.txt) holds the list; `./instrumente/zaehle-pflichten.py` finds the
candidate lines and the hand pass decides): 239 obligations, 173 plumbing and 66 logic
(recounted on 2026-08-30 — the first total of 238 = 171 + 67 had been wrong since the day it was
booked, and a split whose sum is right is never recounted). H = 36 hung. The measure that
mattered: **the ratio L : K is the wrong statistic.** Over the Rust original `delete_leaf` is
4 K / 7 L = 1.75 : 1; over the Gabbro fragment it is 13 K / 8 L = 0.62 : 1, because Gabbro
carries nine more plumbing obligations — it *writes them down*. A language that carries more
plumbing explicitly gets a worse ratio and a better H, and only the second is the direction the
thesis claims.

**How H fell** (each step a re-measurement with its reason; the count is read, not carried:
`zaehle-pflichten.py --haengend`): 36 → 35 (F7: a lowering) → 31 (the plumbing duties brought up to
date) → 29 (K100.1: two of the three hand-written `narrow … else` are *logic*, one is a ritual) →
24 → 18 (K100.3: five of the seven notation gaps listed as hanging were already closed — *the list
came from a frozen document, not from the subject*; a debt list that is too large looks like
diligence) → 17 → 15 → 12 → 5 (2026-08-28: device phases, `requires … else`, a false entry
retracted) → 1 (F3, 2026-09-04). Every closure was a *notation* or a *correction of a false
entry*; none was a handwritten proof. The ten fragments were chosen for their difficulty, so no
extrapolation to the core is carried as a measured value.

**Where the obligations are** (reassignment, by fragment): F6 is the worst carried (21 K, 5 L,
7 hanging) — measuring apparatus is almost pure plumbing; F3 is the only fragment with
L ≥ K (13 / 13) and one of the two that did not fit.

**The logic population measured twice (2026-08-15/16).** The Verus proofs of Caprock hold 8
invariants with 81 preservation theorems (capability system 16, IPC 29, scheduler 12,
notifications 7, DMA 6, loader 6, regions 5; `N_L`). A pre-registered classification of the 81 into
*K by construction / A descent statement / W value statement* gave K 28, A 13, W 40; the
population was then corrected to 73 (eight tool-artefact lemmas over raw `Seq` do not exist in
Gabbro's world), giving K 28, A 7, W 38 against a ceiling of 36.5 — **missed, and the gate tips on
the definition of the population**. The weight estimate needed the B3 share and was withdrawn
afterwards (a formula adding unlike things; the Isabelle side had no counter). *The metric
stays retracted; the three counts stand as counts.*

**Three templates through a prover (2026-08-16/17).** The first three register entries
(`table.induktion`, `table.indexschranke`, `consuming.ordnung`) were machine-checked, with a
negative control each (a false claim inserted fell). Result: of three checked entries **two
contained a false sentence** (M-1: *the index type covers exactly the occupied slots* — it does
not; K-2: *the ordering is preserved under the generated mutation* — one relinking makes a loop;
K-3: *leafness falls out* — it does not, it is an additional obligation on the generation). The
register of 17 entries is not a list of proof obligations, it is a list of drafts; editing all 19
entries marked 11 of them. The trust surface was not shrunk, it was surveyed for the first
time and grew in the process.

### 3.2 `narrow` — from "frequent?" to "ritual or check?" (M3, M4)

The first count over Rust died at its classifier (3 of 5 hand-sampled cases wrong, all in one
direction: the raw number is too high). The repeat over Gabbro source needs no classifier: remove
every `narrow` statement, run the checker, count `M101`/`M104` sites —
`./instrumente/zaehle-bereichspflichten.py`. The ten fragments plus other corpus files gave N = 2
in 791 lines (the Rust count had 150…317: Gabbro's types and V rules carry most obligations
without a `narrow`; what remains is only what needs the emergency exit). Of the three
hand-written `narrow … else` sites, one is a real check (a hostile device tree takes the branch),
one the deliberate second net (the bookkeeping invariant keeps the branch dead), one a ritual
(the bound falls out of the domain and M1 does not see it). Hence the measurand:
`N_ritus = 0` (judgement; today one site, F6) and its mechanical half:

> **Since 2026-08-20 the half that needs no judgement is measured:** `N_folgenlos` — a `narrow` whose removal changes nothing is decoration. Today
> **0**.

`N_folgenlos` is not `N_ritus`: an unreachable-`else` site still carries a duty, because M1 does
not see the bound. The reachability stays a judgement until a pass decides it (W19). The gate "at
most 24 `narrow` over the tree" was replaced because it weighed a real attack guard and a ritual
equally.

### 3.3 B3 — which bodies cannot be written as a traversal? (M5)

`./instrumente/zaehle-b3.py ../caprock-messbasis` (population: 105 files, 69 283 lines raw,
60 756 without test modules; 2 536 function bodies, 2 186 outside tests; 462 with a loop; 571 `for`
/ 146 `while` / 117 `loop`). Four versions of the tool: 0.03 % (saw only bodies with a loop),
4.36 % (read `for x in segs` as a non-domain — one body made 2 %), 0.74 % (missed three chain
kinds), 0.95 % reported; the discarded versions spanned a factor of 130 and **R14 is the only
difference** (W11). Result: **22 bodies, 584 lines, 0.96 %, bar 5 % — passed with a factor of 5**;
hand sample n = 13, 0 misclassified; **not a single `for` loop (0 of 571) runs over a non-domain**,
so the non-traversability sits in `while`, `loop` and loopless bodies. **The suspect list was
wrong**: all three candidates expected by name were guessed wrongly (two entirely, one half); the
largest item stood in none of the suspect areas (union-find, an edge-function chain, the device
topology walked upwards — «B41»); the number is a **lower bound** (four reasons) and holds only
while the class *Index* is carried: were that booking to fall the share would be 290 bodies,
12 558 lines, 20.67 % (gate fallen; row in §6). The tool would have ruined the measurement twice
(not the subject) — an unbalanced brace dropped two bodies silently (26 → 24) until the abort
counter existed.

### 3.4 Convergence (M7)

| Occasion | new constructs | changed meaning |
|---|---|---|
| F1–F6 stock | — | — |
| «B32» virtio ring counter, «B34», «B29» | 1, 0, 0 | — |
| `heldpred`, «B35» `Some`/`None` | 1, 1 | `Held` now carries its strength |
| F7 boot path | 0 | «B37»: *exactly once*, not *in this order* — a limit |
| F8 scheduler | 0 | «B38»: re-check *or* name a carrier |
| F9 page tables | 0 | «B39»: the axiom layer gets longer (hardware writers) |
| F10 parser | 0 | — (finding against the thesis: «B40») |
| B3 (whole kernel) | 1 (`ancestors of`) | «B41»: two more gaps, neither a construct |

Four never-written, hardest areas, zero new constructs and three changed meanings: the first real
evidence for the bet — and its price: two checker repairs (`mappings of` had no bound, a `walk`
was not known to the type system: `Unbekannt` ran along as an empty entry), one dead candidate
(`Stale(T)`), one finding against our own product argument. **Whoever quotes the convergence bet
quotes column 1 (vocabulary); the upkeep stands in column 2 (templates, axioms, semantics).**

### 3.5 Proof effort and trust (M9) — the seL4 breakdown

Foreign figures (`l4v`, one architecture so that numbers are comparable; the whole `proof/` tree
861 309 lines counts the number of architectures along), kept as records in §6. Gabbro's argument
*the refinement falls away because specification and implementation are one language* is the
67.9 % (abstract → executable 40.1 % + executable → C 27.8 %), but the two thirds behave
differently: the first falls away structurally (the Low\* arrangement); the second is **not
proved away but trusted away** (the flat lowering is an assurance; recoverable only via binary
verification, whose tool is small: 10 651 lines); the 32.1 % **invariant preservation does not
fall with the layers** — amortisable over `table … ops`, and only where all mutations are
generated (the K condition). Whoever expects 0.5 : 1 expects the 32 % to amortise completely and
the 28 % to be trustworthy; both were unevidenced. The "Verus line count" side: a seL4-style
comparison measures lines of model and proof (1 336 on this side, `KENNZAHLEN.md`), never the
effort per line.

**The second metric was retracted (2026-08-19).** A formula that summed unlike things (value
statements over Verus bodies against kernel-side lines) gave a number that moved neither with the
assumption "PLAN and TODO are finished" nor with the Isabelle side (no counter); a sensitivity
probe showed 8 of the 81 were library lemmas of a prover Gabbro does not use, and their removal
tipped the gate. Surviving the retraction: the counts, and the one figure resting on the prover
used (the ratio of Isabelle prose to proof).

### 3.6 Base rate, programs, the checker as an instrument (M6)

* **Formats** (`../caprock-messbasis`, 2026-08-15): 5 `repr(C)` formats, 5 commits that touch one in
  53 days (≈ 34 changes a year), 234 entries in `done.md`, 0 occurred errors of the class; the one
  near miss was avoided (a 12-byte virtio header under `VIRTIO_F_VERSION_1`, 10 in legacy).
  The zero is a zero in a curated document, not in the tree; 53 days are short.
* **Userland programs** (`programs/`, repetition 2026-08-15): 935 lines in four of nine files,
  6 endless loops, 7 `break`, 0 `dyn`/`Box`; the `virtio-blk` service loop hangs on volatile DMA
  stores and `forever` (zero atomics).
* **The architecture gap**: a number measured on one architecture is a lower bound for the language;
  `aarch64` was missing from the measured base and stays sealed (an unmeasured number is
  *missing*, not merely imprecise, and the honest version waits for a second tree). The
  neutral-architecture lesson: a corpus that the same author writes for the same language
  measures fit, not transferability.
* **The mutation probe on the checker** — first run 21 of 24 (the three that got through were the
  interesting ones), later 38 of 38 hand mutations (a statement about 38, not about the checker),
  then systematically generated mutations: a 40-site sample of 377 caught 7 of 39 (18 %), which
  exposed 15 real gaps; the catalogue then grew to 388 and the anchor check was added. *A surface with
  0 mutations is not covered but undamageable* (annotation emission, C emission and generator
  templates had 0 mutations on 2026-08-14; the emission surface was brought under mutation on
  2026-08-17, 67 → 87 mutations, 1 310 lines — 19 % — with none dropped to 0, and the
  catalogue exposed that a template ratchet's second tooth had been dead for a day and a pass
  could silently not run).
* **The paper test CapSpace/CDT** and the **sweep of connection invariants**: §4.

### 3.7 Speed of the generated code (M11) — C back end, historical

Two loads with the same computation on both sides and *equality of results checked before time*:
IP header (bitfields, byte order) 1.02 (i7-13650HX, GCC 16.2) and 1.24 (Ryzen 9 9950X, GCC 13.3);
table (4 096 slots, opaque index) 0.97 and 1.00. *One machine is no statement about the language*:
the two differ in two things (CPU and compiler version) and the gap was not located (two
hypotheses refuted: byte-wise reading, reloading the wrapper). `restrict` and `pure` together
gave about 6 % on the table load and nothing alone. Four loads on the second machine: format
reader 1.244, `narrow … else` 1.062 (a checked bound against none at all), `accumulates min` 1.02,
table access 0.99. **Two strawmen, both mine and both in my favour** (a `memcpy` per header made
Gabbro look 3.5× faster; Gabbro's C included into the driver while the handwritten version was a
separate unit): the tell was the same both times — *the own side won too clearly* (R11). One
`restrict` justification turned out to give **0** where it was proved: GCC already knows that a
`static` whose address is never taken cannot be reached by any pointer, so the proved rule stays
as machinery but is not booked as a speed statement. **Not measured:** the LLVM back end and
the direct-binary goals (80 % minimum, 110 % target of GCC -O3 are goals, not figures).

### 3.8 Run times of the guardians (M12)

| Guard | Measured | Note |
|---|---|---|
| `pruefe-lean-beweis.sh` on the build server (2026-09-01) | 482.4 s and 456.9 s, 121 units → 121 modules, 10 generated duties | 3.99 / 3.78 s per unit, against 2.72 s per unit under load 10–15 two days earlier (140 units): **load does not explain it**; the machine was never empty |
| deadline `FRIST_ABNAHME = 2 × FRIST = 600 s` | 78–80 % used | the deadline was *not* raised — it is the very latch that asks the question; at ~3.9 s/unit it is reached at about 155 units (121 today): a corpus reserve, and the corpus grows |
| `isabelle build -D beweise -o threads=12` | 10.1 s wall, 46 s CPU, fifteen theories | the proof side is not the problem, the Lean chain is |
| `pruefe-emission.sh` | 13.7 s (2026-08-20) | the 25 minutes once written as its cost had been a hang |

Unmeasured: why the cost per unit rose by 43 %; an idle-to-idle comparison; whether `lean` itself is
multithreaded under foreign load. The 2026-10-17 repository runs everything locally, so these
figures describe the old build server and must be re-taken before they are quoted.

## 4. Findings the checker and the template register cite

The checker's `fundstelle` strings and the template register's `quelle` fields name these results
by heading. Old German headings, as the code still spells them: *Papiertest CapSpace/CDT* = the paper test below, *SWEEP der Verbindungs-Invarianten* = the sweep, *ERGEBNIS III* = RESULT III, *B13-Nachpruefung* = the B13 re-check, *Nebenbefund N3* = side finding N3 of the paper test; the code comments will be rewritten to the English names.

### Paper test CapSpace/CDT (2026-08-14) — "locks ordered" dies
Three questions on the capability space against `arch/x86_64`: (1) the connection invariants K1
(occupied slot → occupied object), K2 (`refcount(o)` equals the number of slots pointing at it —
«B13» literally), K3 (occupied ⟺ `refcount > 0`) are *connection* invariants, K4–K7 structural,
and **already formalised by hand as one `spec fn cap_inv`** (the group template exists as a model:
`gruppe.ops` proofs are generated, not invented; the formal version is the source, the audit the
projection); (2) the group already exists as a structure (`Mdb` lies in the slot; both slabs in
one `CapSpace`) — `by ops` gives an existing architecture a grammar; the `refcount` field has
three write sites (install `1`, copy `+= 1`, delete `-= 1` with the zero check *afterwards* —
«B29»); (3) the lock imprint is ONE lock of a kind the language did not know (a reader-writer
lock, 33 `read()` against 44 `write()` sites). **Verdict: `locks ordered` dies** — there is not a
single repeated acquisition of one lock class in the tree (`system.rs:15`: *no path takes two
different `SCHEDS[*]` at once*; migration is take, select, release, then revalidate) — *the test
killed its own candidate*. Two real gaps found instead: **L-A** no shared lock acquisition (the
hottest path, cap resolution, was unwritable) → built the same day: `locks [shared] …`,
`shared held <= K ops`, refusals `H001`–`H004`, `E007`, `K004`, example `10-geteilte-sperre.gab`,
poison `38`–`41`, +5 mutations all caught; **L-B** handover with revalidation (`ghost Stale(T)`) →
carried as a *condition*, not a construct (F8, «B38»). **N1** (to Caprock, not Gabbro): the two
documented lock orders contradict each other (`MEM` as leaf versus `MEM` in the middle of a
chain): the class — two prose orderings nobody checks against each other — makes a declared
`rank` line structurally impossible. **N2** the atomic `FP_OWNER` is part of the deadlock
derivation (a column of its own in the ordering count). **N3 — side finding closed:** `held <= K
ops` is the exclusive case; on the shared side the quantity is the *writer waiting time under
reader pressure* — the cost pass needed a branch of its own (`shared held`). The speech test for
«B29»: a hand `zaehler -= 1` on a `table` with `ops` falls twice (`D001` and `M104`).
*Correction (2026-08-15):* the second copy of the kernel was a rename of the first (`R099`), not an
independent origin; the load-bearing justification is measured by `git log -L`: the line sequence
`-= 1`, zero check afterwards survived five rebuilds (two on release semantics) since 2026-06-23 —
**B29 is an attractor**, which carries the speech-test obligation better than independence.

### Sweep of the connection invariants (2026-08-16)
The quantifier of the proof rule — *every connection invariant in the tree has a group whose `ops`
close it* — needed more than one pair. Four found: V1 `refcount_matches` (one structure, one lock
`CAPS`); V2 reciprocity of the donation edges (`sc_donor`/`sc_donee`, one structure, one lock
`SCHEDS[core]`); V3 the queue marker against the ready list (one structure, one lock); **V4**
endpoint queue against thread state (`t ∈ ep.receivers ⟺ IPC ∈ tcbs[t].reasons`) — **two
structures in two crates and two locks with the declared order `EPS[i] < SCHEDS[core]`**: the first
imprint that is not a single lock, hence the first real test for the `locks` line of the group
grammar (the kernel hedges it itself: the fault hook sits where it sits because it would otherwise
take `EPS` under `SCHEDS`). The expected test case for `locks ordered` falls away, and the one found is
*two classes with an order across two crates*. **A filled map is no evidence of a complete map
(W12):** four found means four found; the search paths miss invariants whose two halves share
neither a name nor an index field (a sum condition over two tables); a mechanical sweep, not a
search path, would be needed to prove the quantifier. This led to the carrier group (pass 10,
`gruppe.rs`), five refusals (`U003` the one V4 needed), `U006`/`U007` (the third and fourth S17
obligations; a surviving mutation was the yield), and V4 stays the first imprint that requires the
`locks` line to carry an order.

### A1–A4 (2026-08-14)
**A1** `own` linear: green on the mechanism question — a borrow needs no new word (`consumes`
in the effect list), separation falls out of M2; but the chain has no **origin** (no address
operator, `locks` has no binder, a `table` has no creation form) — and that dissolved in
**"The origin"** below. **A2** dynamic calls: 67 `dyn` sites; the two dynamically used traits have
**one** implementation each (a layer boundary, not polymorphism: the trait object disappears);
the rest is 64 closures (the claimed 89 had no search path). *Superseded in part:* function
pointers do carry a contract since `N035`–`N037`. **A3** `table … count N`: `index into T`
inherits the bound from `count` (M4's number comes out of the language), and `index into` became a
`typeexpr`. **A4** the cost model fell twice: the implementation counted `if`/`return`/constant
loads in while the spec names four primitives (after the fix the declared numbers 4, 8, 8 held
exactly), then three of the author's own declarations were wrong (guessed 4 096 → computed 831 488;
64 → 1 032; 4 096 → 5 120 — *the sort of number the protocol was written against*); the most
valuable find was `K002`: a `PLANER` lock over a full traversal costs 3 072 ops against `held <=
300` — the lock belongs inside the pass, not a raised `held`.
Moved together: passes fully built 3 → 4 of 9, poison files 32 → 36, mutations caught 27 → 32 of 32.

### The origin (2026-08-14) — it dissolved instead of being closed
The ownership chain "has no beginning" was a problem only because the Rust original had a
`&mut CapSpace`: kernel state is one instance behind a lock. **A `table` IS memory** (its name is
its place, no pointer pair, no aliasing question); **the parameter list of a `device` IS its
constructor** (the address comes from data, not out of nowhere). F1 and F2 were written out without
one pointer through all five passes (`beispiele/09-ohne-zeiger.gab`). What remains are DMA buffers,
allocated regions and foreign memory — `own` pointers, consumed if `effects` names them under
`consumes`, otherwise borrowed. *A fragment that translates its original along brings that
original's constraints with it, and those then look like requirements of the new language.*

### RESULT III — three templates, and the yield has a category nobody provided for (2026-08-16)
See §3.1: 5 assumptions flushed out against a predicted 3–7 (flat middle), but the pre-registration
asked for *silent assumptions* and found **two plainly false sentences** (M-1, K-2) — a different
class. K-3: *a "falls out of it" in a proof obligation is the most expensive formulation: it
promises that at this place nothing more is to be done.* Booking: entries 17 → 19, proved 1 → 4,
unproved 16 → 15 (two entries split because half provable and half over a nothing:
`table.indexschranke` → `+ table.absenkung`; `consuming.ordnung` → `+ consuming.umhaengen`).

### B13 re-check (2026-08-17/18)
The counting rule for the bookkeeping invariant was broken by the first assignment (the aggregation
`refcount == count(s in slots : s.object == o)` and the sibling-chain mutuality were *logic*
obligations that the language could not even let the human write); `count x in <domain> : pred`
is in the grammar today (§2 of `FRAGMENTE.md`), the cross-table half never carried (a foreign table
name is a place).

### «B37» — linearity is not an order (F7, 2026-08-16/17)
A linear token enforces *exactly once*, not *in this order*; the first yes-statement was one fragment
all the way through (check, emit, `cc`, run). Closed by `order { … }` with `advances`, the stages
identifiers in one declaration; a boot-order guardian checks all of them.

### «OPT1» — a proved rule with no measured gain (2026-08-19)
`restrict_gerechtfertigt` (`Restrict_Alleinzugriff.thy`: from a complete effect frame and separated
roots follows the C11 6.7.3.1 assertion, and the converse theorems say *both* hypotheses are
needed); 36 `restrict` over the corpus, all twelve units still green including the `-O0`/`-O2`
equality that is the only thing that finds a wrong `restrict`. Measured on the shape the rule
unlocks (one pointer against a global table of the same type): factor **1.00** — GCC already knows
what the rule would tell it; the 2.85 holds for the other case (two pointers of the same type),
which hypothesis H2a excludes today: the price tag hangs on the `own` decision, not on the analysis.
It stays (proved, covered, free at run time, and the machinery the `own` decision will use) and is
*not* a speed statement.

### Other cited anchors
* **«B13»–«B41»** and `GP1`–`GP3` (the counter-check findings of the P0.4 probe were renamed from
  `G1`–`G3` on 2026-08-16 because they collided with the grammar findings of the same name): their
  status register is §2 of [`FRAGMENTE.md`](FRAGMENTE.md).
* **The anti-catalogue touchstone** (P0.4): of the 14 gaps in the `vtd` block a designer's grammar
  needed 3 additional words (RMW state bits, register bank at a run-time base, conditional
  compilation — 335 `cfg(feature)` sites), *not twelve* — passed, with the caveat that four of the
  "0-word" rows were changes to `device`, the construct he left unchanged.
* **Gate P2 (lexer and parser)**: first run 1 of 6 fragments (six holes the parser found, none by
  reading), **reached 6 of 6 on 2026-08-15**. A counter-check beside it found 16 files with real overflows that
  got through the checker and had to fall (the sentence that was wrong stood in the specification, not only in the source), two parser errors, and a coverage number the suite could not give. **Gate P3** (M1 and the three flow rules): the pass
  *reproduced a finding the folder had found by hand*; coverage is the number without which a
  green run says nothing.

## 5. Withdrawn and invalid measurements — what did not survive

Kept so that nobody repeats them. *Invalid* means the measurement broke, not that the result
was unfavourable.

| Measurement | Why it fell |
|---|---|
| The 74-obligation split (17 / 57) | no site list; replaced by the reassignment (§3.1) |
| `narrow` over Rust (150–317 sites) | the classifier failed the protocol's own hand sample |
| Count of 17 logic obligations | invalid by its own condition (the assignment was not in the folder) |
| The 89 closures | no search path; reproducible 64 (and the gate void) |
| Plumbing classes, first fresh count `N_neu = 5` → 4 → 3 | refined by reassessment of *Race and Publication* and *Frame*; population gate missed |
| The weight formula / second metric | retracted 2026-08-19 (§3.5) |
| `H = 0` as a coverage claim | an adversarial audit and an independent re-judgement (2026-09-04) refuted the split criterion that bought it (`FRAGMENTE.md`) |
| `Unbekannt` as "no finding" for a literal wider than `i128` | an acquittal that read like caution (`M139`) |
| "The comparison of two counts of 'before and after'" in the guardian register | a Vorher/Nachher row is an event, not a state |

## 6. Booked records — frozen tables that the number guardian reads

*Do not reword and do not recompute.* Each table is the result of one day; the guardian
`instrumente/pruefe-zahlen.py` lists every row below in its `UNBEWACHBAR` register with a written
reason (a record, a foreign tree, an ordinal or a judgement) and demands that the row still stands
here. The *living* figure beside each is measured elsewhere (named in the caption).

### 6.1 The reassignment of 2026-08-17 (the living split: `PFLICHTEN.txt`, `zaehle-pflichten.py --spalten`)

| | | |
|---|---:|---|
| Obligations in total | ~~238~~ **239** | ~~228~~ **229** anchored at a line + 10 lowering |
| **Plumbing (K)** | **173** | 73 % |
| **Logic (L)** | ~~65~~ **66** | 27 % |
| **hanging** | **50** | of which **36 K** |
| disputed | **1** | 0,4 % — the gate allowed up to 10 % |

*(Recounted on 2026-08-30 from the rows: F4 has 31 rows, not 30 (24 K, seven L), the total is 239 = 229 anchored + 10 lowering rows, and the true split is 173 K / 66 L — neither earlier pair, 171 / 67 nor 173 / 65, was right, and both summed to 238, which is why nobody recounted. `K = 173` held, so the gate was untouched; only the logic column moved.)*

| | | |
|---|---:|---|
| K, carried by construction | **137** | 79 % of all plumbing |
| **K, hanging — H** | **36** | 21 % |

137 + 36 = 173 is the starting position of K100 and must not move.

### 6.2 Template register states (the living state: `gabbro schablonen`)

| | before | after |
|---|---:|---:|
| entries | 17 | **19** |
| proved | 1 | **4** |
| **unproved** | **16** | **15** |

Three formalisations, and the number of the unproved fell by one. Later states the register held
that day:

| What stood | became (2026-08-17) | command |
|---|---|---|
| 19 templates, 4 machine-checked | **20, 9** | `gabbro schablonen` |

### 6.3 The mutation catalogue and the clause guard (the living figures: `mutiere-pruefer.py --anker`, `pruefe-klauseln.py`)

| | before | after |
|---|---:|---:|
| checker lines | 6 823 | 8 163 |
| **lines with zero mutations** | **1 310** (19 %) | **0** |
| mutations | 67 | **87** |

| Clause guard, class counts of 2026-08-18 | | |
|---|---|---|
| ZUSAGE | **17** | eine Aussage über Verhalten, die kein Pass hält |

| What the sample run drew (2026-08-15, 40 of 377 sites) | |
|---|---|
| drawn (deterministic, fixed seed) | **40** |
| **caught** | **7** |
| **escaped** | **32** |

| Mutation surface at the first catalogue (2026-08-14) | Mutations | |
|---|---|---|
| **checker** (refusals) | **32** | built, mutable |
| **annotation emission** — the wished-for-form channel | **0** | **not built, hence not damageable** |
| **C emission** | **0** | not built |
| **generator templates** | **0** | 16 entries, mostly designed — what is not code catches no mutation |

### 6.4 Booking corrections of one day (2026-08-18 / 2026-08-30)

| Number | stood | is | where | command |
|---|---:|---:|---|---|
| Prämissen ohne Pass | 7 | **9** | `PLAN.md`, «NL» | `gabbro schablonen` |
| **ZUSAGE ohne Leser** | 13 | **0** | `PLAN.md`, «NL» | `./instrumente/pruefe-klauseln.py` |

| | Reassignment | Lane B | merged |
|---|---:|---:|---:|
| Mutationsanker | 332 | 335 | **340** |

| Theory split at its measuring day (the living: `zaehle-theorien.py`) | Lines | Share |
|---|---:|---:|
| **Prosa** | **1 062** | **45,8 %** |

### 6.5 Foreign corpora — measured in trees that this repository does not hold

*Caprock (`../caprock-messbasis`), seL4 `l4v` and published figures; no command here.*

| Caprock: factor of a `device` block against the file (2026-08-13) | Value | Gate ≥ 5 | |
|---|---|---|---|
| the **whole file** (1 448) | **15,1** | passed | "how much smaller is a declaration than a file that is mostly something else" — **meaningless for the thesis** |

| The aggregate of the first split | |
|---|---|
| Proof obligations in total | **74** |

| `l4v` at `f4940273`, ARM only (2026-08-14) | Directory | Lines | Share |
|---|---|---|---|
| **Invariant preservation** over the abstract model | `proof/invariant-abstract` (neutral + ARM) | **76 873** | **32,1 %** |
| **Refinement** abstract → executable | `proof/refine` | **95 915** | **40,1 %** |
| **Refinement** executable → C | `proof/crefine` | **66 670** | **27,8 %** |
| **functional correctness, ARM** | | **239 458** | 100 % |

| Beside it | | |
|---|---|---|
| security theorems (item 5) | `proof/infoflow` + `proof/access-control` | **56 323** = **+23,5 %** |

| Caprock `programs/` (2026-08-15) | Lines | endless loops | `break` | `dyn`/`Box` |
|---|---:|---:|---:|---:|
| `trusted/fs` | 365 | 3 | **5** | 0 |

| Caprock Verus proof files (preservation theorems, 2026-08-15) | | |
|---|---|---|
| capability system | `capability-system/proofs/cap_space.rs` | **16** |
| IPC | `ipc/proofs/endpoint.rs` | **29** |
| scheduler | `scheduler/proofs/runqueue.rs` | **12** |

| The substitution trap of the second metric | share | estimate by the same formula |
|---|---:|---:|
| **obligation side** (Verus bodies, `w = W_zeilen/F`) | 0,341 | **1,90** |

| B3, were the class *Index* booking to fall (2026-08-16) | Bodies | Lines | Share | Surcharge | Gate (bar 5 %) |
|---|---:|---:|---:|---:|---|
| **were the Index booking to fall** | **290** | **12 558** | **20,67 %** | **+1,03** | **FALLEN** |
