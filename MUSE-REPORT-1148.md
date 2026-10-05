# MUSE-REPORT-1148: Independent exact review of candidate 1147

CANDIDATE: 1147 206a3d84d6449f79588e127ce01c3fa88793c6ac
VERDICT: ACCEPT

## Identity and method

- Reviewer clone verified: `/home/simon/Dokumente/gabbro-muse/a1148`, branch
  `muse/1148` (matches lane task; no STOP condition).
- Candidate pinned from `.tmp/review/SNAPSHOT.json`: author 1147, HEAD
  `206a3d84d6449f79588e127ce01c3fa88793c6ac`, base
  `48a4be7c1c333a602ce0d0816979d154ae1bd959`, `clean: true`, files exactly:
  `MUSE-REPORT-1147.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/HwWordAtomicity.lean`.
- Read-only review of the snapshot (`PATCH.diff`, candidate file, author
  report, `BUILD-EVIDENCE.json`). The author clone itself was never touched.
- Independent checks in this clone:
  - `./lean-probe .tmp/review/author-1147/grammatik/Grammatik/X86/HwWordAtomicity.lean`
    on the EXACT candidate bytes: `== 0 error(s) in the COMPLETE output; exit 0`
    (elaborated against this clone's newer dependency base, so base drift is covered).
  - `./lean-bau`: `Build completed successfully (601 jobs).`
  - Grep checks: forbidden tokens, candidate-name uniqueness in `grammatik/`,
    referenced accepted names present, silicon text in the supplied SDM.

## Checklist result

- No `sorry`/`admit`/`native_decide`/`sorryAx`/`axiom`/*unsafe*: clean
  (word-boundary grep over the candidate file; only false-positive substring
  `admits` in prose, no tactic/term use).
- `#print axioms` standard: every candidate theorem depends on `[]`,
  `[propext]` or `[propext, Quot.sound]` — verified in my own probe output,
  matching the author's evidence. Within the goal axiom set; no
  `Classical.choice` needed, none smuggled.
- Existing files untouched except one import line: `PATCH.diff` shows exactly
  one added line `import Grammatik.X86.HwWordAtomicity` in
  `grammatik/Grammatik.lean`, no deletions, no other existing-file edits.
- Every premise used: inspected each theorem; `h`/`hwf` both consumed in
  `adapterWort1147_wf`; `hfl` plus the head equation in the embedding;
  all guard/readability/trace/membership/emptiness/exclusion premises
  threaded into the lifted lemmas; `d` (observing core) pins the conclusion
  of both foreign-observation theorems; `kein_hw_wort_bruecke` consumes its
  hypothesis by cases. No `intro _`, no `have _ :=`, no `Prop`-typed premise.
- Family evaluator lifted, not copied: the adapter runs the accepted
  `hwWortAusgabe` by `rfl`-agreement; observation/frame/tearing theorems are
  exact lifts of `wort_gruppe_liest_zurueck`, `wort_gruppe_rahmen`,
  `verflochten_erster_schritt_reisst`; all referenced accepted names
  (`WortGruppe`, `FremdFrei`, `DrainSpur`, `hwWortAusgabe`,
  `hwTeilwort_keine_gruppe`, `ausrichtung_allein_verweigert`,
  `wI0`/`wI1`/`wI10`/`wI_trace`/`wOv`/`vA`/`vB`/`fByte`/`zeugenWort` and the
  `wI_*` lemmas, `projZustand_speicher`, `setTso_wf`, `flush_leer`,
  `tsoAnsicht_puffer`) confirmed present in this tree. New items are only the
  required adapter/event/wrapper/assumption/gap-marker definitions.
- Planted refusals really refuse: drain-on-empty via `flush_leer`;
  partial buffer via the accepted structural lemma; overlap via
  `ausrichtung_allein_verweigert.2` (alignment admits what the exclusion
  check refuses — genuine, on the concrete `wOv` state); `hw_ausrichtung_vA`
  by `decide` on `vA = 0`.
- Witness non-degenerate: `hw_verflochten_zeuge` joins every premise of the
  guarded observation on the interleaved two-core drain (core 0 drains the
  exact eight-entry group at aligned `vA`, core 1 issues/flushes a disjoint
  byte; both buffers empty at end; both memories observably change;
  owner-only forwarding vs foreign stale read; real foreign issue+flush
  facts; `HwWf`). `hw_riss_zeuge` is a real `HwSchritt.spülung` machine step
  installing byte 0 while byte 1 stays old, with a `decide`d memory change.
  Memory-changing steps on two cores: satisfied.
- Silicon facts: no silicon redefinition attempted. The single-copy rule is
  stated as the named OPEN assumption `HwWortAtomar`, never inhabited,
  assumed-as-premise, or discharged (confirmed: used nowhere). Substance
  matches the supplied Intel SDM edition 093 text (aligned quadword access
  guaranteed atomic; see observation O2 below on the section number).
  Word stores are modelled as eight `issueByte` events, LOCK stays refused —
  no false hardware correspondence.
- CUTS honest, no claim larger than proof: end-state whole observation plus
  disjoint-frame preservation only; mid-trace mixture explicitly admitted
  (`hw_erster_schritt_reisst`, `hw_riss_zeuge`); `HwWortBruecke` empty with
  `kein_hw_wort_bruecke`; no W/GX, source, checker, contract, entry, timing,
  or liveness claim. The report's correction of the task sentence
  ("observed whole ... no mid-drain mixed word" is unprovable for the grouped
  word itself) is accurate and the delivered weaker true statement plus named
  assumption is the correct handling — not a silent weakening.
- Inhabitation spirit (rule 13): no program-syntax premises and no `ZEUGE:`
  line in the owner task; the two joint witnesses cover all premises of the
  guarded observation on non-degenerate machine runs.

## Observations (non-blocking, no repair)

- O1: file header comment cites `HwWortAtomAnnahme`; the defined name is
  `HwWortAtomar`. Doc-only inconsistency.
- O2: CUTS cites the aligned-access single-copy rule as "Intel SDM Vol. 3A
  §8.1.1"; in the supplied edition 093 the Guaranteed Atomic Operations
  section is numbered §11.1.1 (Vol. 3A). Substance identical; citation number
  is edition-dependent. Explicitly NOT checked as provenance by the author —
  that honesty is correct.
- O3: `BUILD-EVIDENCE.json` contains intermediate red `lean-probe` runs
  (normal development trace: rewrite miss, constructor mismatch, unknown
  identifiers, an unsolved-goal repair). Final probe 0 errors and final
  `lean-bau` 601 jobs green; history does not taint the pinned HEAD.

## Integration note

The candidate file was probed standalone (exact bytes, green) rather than
merged into this clone's tree, so the single appended import line was not
rebuilt here. Residual risk is negligible and stated: all ~30 new names are
verified unique in `grammatik/` (zero collisions), the existing-file diff is
one appended import with no deletions, and the author's `lean-bau` (601 jobs)
covered the integrated build on its base. My `./lean-bau` line below is the
green baseline of this clone.

## Last build results

- `./lean-probe` (exact candidate bytes):
  `== 0 error(s) in the COMPLETE output; exit 0`
- `./lean-bau`: `Build completed successfully (601 jobs).`

## Open

Nothing open on this review. Candidate 1147 is accepted as reviewed at the
pinned HEAD above; integration may proceed through the normal serial merge
gate (sorry-scan, axiom check, full build).
