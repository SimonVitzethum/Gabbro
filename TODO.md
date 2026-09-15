# Gabbro — open items

*Rewritten from scratch on 2026-09-15, after the goal theorem was confirmed. The previous file
(5,441 lines, stages 0–9 from August) is in the git history at commit `1434efba`. Everything it
listed is one of four things:*

- *done;*
- *superseded by the goal-theorem track;*
- *recorded as a known absence in `dokumente/OFFEN.md`;*
- *deferred (last section).*

*Its guardian-booked figures moved verbatim to `messung/KENNZAHLEN.md`. How the work is run —
machines, lanes, merge scripts, number ranges — is in `AGENTS.md`.*

**Where we are.** `gabbro_ziel : GabbroZiel` is proved over the Lean model and was confirmed by
two independent reviews in round 6 (tag `milestone-2026-09-15-zielsatz-bestaetigt`). Following
the owner's end sequence, the work now is:

1. transfer into the checker and the emitter (§1);
2. translation validation (§2), whose one headline metric is the **chain count**, from
   `instrumente/zaehle-kette.py`. It stood at 1 of 101 on 2026-09-14 and at 2 of 111 after
   stage (a) (programs 104 and 108).

Each item names its owner (lane or agent) where one is running.

---

# 1. Transfer into the checker and the emitter  ⟨A⟩

- [ ] **The exporter produces a full `Einheit`** — lane 198 (running). `gabbro lean-g` writes:
  - the real `requires`;
  - the declared starts with their arguments;
  - the declared initial memory as `sp0`;
  - the lock-invariant family `S`;
  - `def gE : Einheit gD`.

  `gabbro obligations --g` states `NutzerPflicht gE` and derives the per-program theorem from
  `gabbro_ziel`, with the checker premise closed by `decide`. The demonstration covers 104 and
  one concurrent program.

  *2026-09-15, the middle link closed:* the stated duty is now PROVED for both, over the
  regenerated export — `GenOblig104.lean` + `Pflicht104.lean` (`oblig_nutzer`, `oblig_ziel`)
  and `GenOblig108.lean` + `Pflicht108.lean` (`p108_nutzer`, `p108_ziel`, two declared
  starts), standard three axioms, and `instrumente/pruefe-genlean.py` holds both generated
  files against their generator byte for byte. What is still open here is the WIDTH: 104 and
  108 are two programs, not the corpus.
- [ ] **The Rust checker computes the whole Lean checker Bool `Akzeptiert`** — lane 196
  (running; codes N315–N319). It works component by component: the call-graph closure, lock
  floors, `sperrOrte`, `einzeln`, and whatever else has no Rust counterpart yet. The
  differential test `instrumente/pruefe-akzeptiert-diff.py` compares the Rust verdict with the
  Lean Bool on every exported corpus program. Every disagreement is a finding.
- [ ] **The exporter covers the concurrent programs.** Of 07, 59, 108, 109, 124 and 125, only 108
  exports today. 124 needed a hand model (`Korpus124.lean`, `kP`). Widen `lean-g` for locks,
  `held` sections and multiple starts, measured by how many of the six export.
- [ ] **`beispiele/124`'s `setze` promises too little** (`dokumente/OFFEN.md` O12). With the
  source's contract, the release check in `hauptA`'s locked section fails, so the user
  obligation does not hold as written. Two steps:
  1. Fix the example's contract.
  2. Decide how the tool chain surfaces a user obligation that fails: `gabbro obligations` and
     `gabbro counterexample` should show it, since the checker cannot refuse user logic.
- [ ] **The C read correspondence for nested arrays** (lanes 170 and 185 built the rule side,
  N285–N289). The emitted reads of `[[T; n]; m]` still need their correspondence lemma.
- [ ] **The certificate printer prints the simulation certificate for stage (b).** `sim124` is
  built by hand. A printed certificate, plus a Lean checker that turns it into the simulation,
  is what makes stage (b) scale beyond one program.

# 2. Translation validation  ⟨D⟩

**Stage (a) — single-threaded, generic** (`Schlusssatz.lean`, `KorrespondenzAllg.lean`; plan §6).

- [ ] **Sieve (a), the elaborator** — lane 199 (running). 89 of 111 programs stop there: 69 have
  an item without a G form, 12 a unit without a table, 7 use `bool`, 1 uses `requires`.
- [ ] **Sieve (a), the Lean parser** — lane 200 (running). 20 programs stop there, 10 of them at
  `reserved head forall`.
- [ ] **`korrOk` arms** for `if`, `traverse`, compound assignment, globals, `let` of a call, and
  arithmetic. Each is one arm over an existing lemma. Measure each by the chain count it moves.
- [ ] **Discharge the "no model error" condition** of part 4 from the model judgement, instead
  of carrying it.
- [ ] **Re-instantiate the link between the single-thread machine and `rufAt`** inside the
  closing theorem. Today it is the adequacy chain, outside it.
- [ ] **Take the `Einheit` of a chain from the exporter** (depends on lane 198) instead of the
  chain author writing it.
- [ ] **Export the arena** (`OFFEN.md` O14, `SATZKARTE.md` §32). The specification carries
  `alloc`/`reset` since 2026-09-15 (`Grammatik/ArenaZucker.lean`: a table of `count = hi` slots
  beside a `used` global); `lean_g.rs` refuses the DECLARATION by name instead of building that
  pair, so `beispiele/98` and `99` stop at sieve (b). Read an `ArenaDecl` into a `TableModel` +
  `GlobModel` and lower the two statements. *The reservation `lo` does not travel — it is the
  checker's static count (`N212`), and the model-side consequence is already proved.*
- [ ] **T3 round trip for statements** (`SAnw`), and for full `gutPlatz` index payloads. Lane 195
  closed the expressions through level 6 (`Parser/Rundlauf4.lean`).
- [ ] **A2: a Lean C parser for the emitter's subset** (`parseC text = some prog` by `decide`).
  It replaces the hand transcription of the emitted C by "the compiler's front end reads the
  subset as `parseC`", which is part of A1.
- [ ] **A3: the missing lemma** that the C semantics reads a `RecLay` only through the pinned
  numbers.
- [ ] **T4/T5 coverage.** Every form `pruefe-cformen.py` lists as uncovered gets a lemma or
  becomes a named assumption. The remaining T5 templates.

**Stage (b) — concurrent** (`CNebenlaeufig.lean`, `Schlusssatz124.lean`; plan §7). It is closed
for 124 with `DRFSC` and `LaufzeitC` as named premises. Open, by plan §7.6:

- [ ] **Region serialisability inside DRF-SC.** It needs a C semantics with one step per memory
  access.
- [ ] **General footprint soundness.** It needs an access-instrumented `Exec`; the key lemma
  `ev_zform_blk` is proved.
- [ ] **The runtime's ticket lock behaves as `sperrAbstrakt`** (a proof, not a premise).
- [ ] **A simulation-certificate checker** (see §1, printer).
- [ ] **Exporter support and parse fidelity for 124** (§1, and sieve (a)).
- [ ] **Semantic extensions:**
  - lock calls inside loops, branches and callees (today only at the top level of a root
    function);
  - atomics as a source of ordering and as exempt from race freedom;
  - volatile and foreign calls inside blocks.

**Beyond the single unit** (PLAN-ZIELSATZ §10):

- [ ] **The linking theorem.** If each unit's certificate checks and the units' ABI interfaces
  match (decidable from the `_Static_assert` pins), the linked C refines the composition of the
  programs.
- [ ] **Inline assembly: a small ISA semantics** for exactly the stub patterns the emitter
  writes, so each stub gets a correspondence lemma instead of `AxCorr`.

# 3. The goal statement — follow-ups  ⟨D⟩

- [ ] **The liveness assumptions go into the ONE list in `Spec.lean`'s header**: `LaufzeitAnnahme`
  (FIFO lock and fairness window `F`) and `HardwareImAbschnitt`. Today they sit in
  `Lebendigkeit.lean`.
- [ ] **The external human review** of the review package (PLAN-ZIELSATZ §5): the definitions
  the kernel cannot judge. That is the machine G, the good-run predicates, `KoerperGutS`, the
  goal predicates, and the C semantics core.
- [ ] **The final double verdict over the whole chain.** One Muse lane and one Opus agent,
  independent, once stage (a) covers the corpus: "is the goal reached for the product, not only
  the model?"
- [ ] **Keep README §6 true** after every merge that moves the chain count or a stage.

# 4. Extensions and named gaps  ⟨D⟩

*Rules for every extension: PLAN-ZIELSATZ §8. The criterion is counted per obligation, there is
one assumption list, and the number is booked before and after.*

- [ ] **Linearizability** of lock-free structures. SPSC ring first, then the Treiber stack and the
  sequence counter, then RCU. External and helping linearization points are a separate, later
  extension. Opus-sized, more than a week.
- [ ] **WCET as a named interface with proven inputs.** Export the flow facts (loop bounds, paths,
  call graph, `deadline`) as a certificate; the processor timing model is a named assumption.
  About 8–10 working days.
- [ ] **Noninterference: declassification** (delimited release). It decides whether the flow rule
  is usable. The customer sentence stands in NICHTINTERFERENZ.md.
- [ ] **Timing channels.** A constant-time discipline as an extension of the flow rule. After
  declassification.
- [ ] **Waiting bounds that fit a data sheet.** Use dominance, per-lock contenders from the call
  graphs, and computed block costs instead of the declared `held`
  (`messung/WARTESCHRANKEN-2026-09-15.md`: nested bounds are astronomical from three levels).
- [ ] **`bv_decide` axioms.** Each per-computation axiom goes into the ONE assumption list by name,
  with an independent re-check as the ratchet (lane 181 measured the mechanism).
- [ ] **Checker robustness.** One register sentence per pass: it terminates on every input, with
  the measure. Where no proof exists, a fuzz run as evidence.
- [ ] **Float accuracy (error bounds)** stays named, not claimed. Pick it up only if a kernel
  needs it.
- [ ] **The people gap.** A tutorial path from a first program to a proved `ensures`, with
  `gabbro obligations --g` and `gabbro counterexample` (lane 180) as the everyday interface.
- [ ] **Tool maturity** (LSP, localisation, profiling). After the goal.

# 5. Simplicity without losing a guarantee  ⟨E⟩

*Measure (PLAN-EINFACHHEIT §0): `gabbro zeremonie` goes down AND the pass register stays
constant.*

- [ ] **Lever 3: `gabbro fmt --explicit` / `--elide`** — lane 197 (running). Pure views: same
  diagnostics, same register, byte-identical C, round-trip idempotent.
- [ ] **Lever 2: defaults with a named escape.** Design the rule set first (rank order, phase,
  `pure` on spec functions), with one register sentence per rule, then build.
- [ ] **Lever 6: tactics** (`gabbro_simp`, `gabbro_wf`, normalisation) and better handed-over
  goals. Measure by lines per obligation.

Levers 1, 4 and 5 are done: derivation (lane 191, demanded effects 616 → 277), fix-its (lane 187)
and contextual keywords (lane 188, the residue is irreducible).

# 6. The measurement layer  ⟨Q⟩

- [ ] **Pre-existing red guardians.**
  - `pruefe-todo.py` and `pruefe-zahlen.py` carried findings before this rewrite; the lane
    reports list them as pre-existing.
  - `zaehle-gifttreffer.py` exits 1 with a stable finding set.

  Re-measure each on fisch with `./instrumente/abnahme.py --voll`, and rebook or repair them, one
  guardian at a time.
- [ ] **`messung/KENNZAHLEN.md` is German where the old TODO was.** Give each pattern in
  `pruefe-zahlen.py` / `pruefe-todo.py` its English alternative, then translate the ledger
  lines (patterns first, document second).
- [ ] **The README headline numbers** (diagnostics, sentences, mutations) move with every merge.
  Rebook them in one pass after the transfer lanes land.
- [ ] **Re-measure the time of the mutation run.** CLAUDE.md quotes the time for 377 mutations;
  the catalogue is past 400.

# 7. Deferred, with reason  ⟨Z⟩

- **`aarch64`** is second-rate and later. When it starts, the "sealed" note in CLAUDE.md changes
  first.
- **GPU** support belongs in the standard library (SPIR-V payloads, the GPU driver as a named
  assumption), after the chain.
- **Probabilistic statements and dynamic unbounded data structures** are out of scope (owner,
  2026-09-14). They are not claimed and not worked on.
- **Nonlinear arithmetic over unbounded integers** stays user logic with hand lemmas. It is the
  one place the oracle-plus-certificate pattern does not reach.
- **The bootstrap chain** (Gabbro written in Gabbro) is deferred, with the measured reason in the
  old TODO (commit `1434efba`, "DIE BOOTSTRAP-KETTE").
- **Known absences** O1–O14 are recorded, with what would close each, in `dokumente/OFFEN.md`.
