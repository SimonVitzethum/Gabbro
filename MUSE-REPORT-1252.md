# MUSE-REPORT-1252: Exact review of candidate 1251 (TsoGxChecker)

CANDIDATE: 1251 83738fee920549a89dfc333ebf1aa75532993acc

## Clone / branch

- Clone: `/home/simon/Dokumente/gabbro-muse/a1252`, branch `muse/1252` (verified).
- Owned file only: `MUSE-REPORT-1252.md` (this report). No other file touched.
- Candidate: lane 1251, pinned HEAD `83738fee920549a89dfc333ebf1aa75532993acc`,
  base `515546d0e2430c0d416ede74e3add0166e88e2de`
  (from `.tmp/review/SNAPSHOT.json`).
- Reviewed artefact: `.tmp/review/author-1251/PATCH.diff` (215 lines, read in full),
  `.tmp/review/author-1251/grammatik/Grammatik/X86/TsoGxChecker.lean` (125 lines),
  `MUSE-REPORT-1251.md`, `BUILD-EVIDENCE.json`, `OWNER-TASK.md`.
  The author clone itself was not accessed (HARD RULES isolation).

## What was checked

New file `grammatik/Grammatik/X86/TsoGxChecker.lean` with five theorems:

- `abgK_von_akzeptiert` — checker Bool gives `AbgK E.P fs.1 (reachB E.P fs.1 w)`
  via `Pruefer.korrekt` (`.abg` field). Bool-to-Prop step, not a restatement.
- `fussSX_von_akzeptiert` — same Bool gives
  `FussSX E.P E.S (lokW E.P fs.1 E.ws) (GeteiltV E.P E.ws) f` via the accepted
  embedding `akzeptiertSpecX_of_spec` (`Zielsatz/AtomarAkzeptiert.lean:47`).
- `kein_geteiltV_von_akzeptiert` — with complete member list, same Bool gives
  `¬ GeteiltV E.P E.ws c` via accepted `geteiltV_leer`
  (`Zielsatz/BeweisAtomar.lean:459`, itself via `geteiltA_leer`).
- `checker_liefert_wgx_pruefer` — the three jointly.
- `checker_liefert_wgx_pruefer_zeuge` — joint witness on the two-thread unit:
  concrete checker `akzeptiert_pruefer` accepts `Zielsatz.mE` (`mP_akzeptiert`,
  definitionally the same Bool since `akzeptiert_pruefer.akzeptiert` unfolds to
  `Akzeptiert E.P E.S fs ls cs E.ws` per `Zielsatz/Akzeptiert.lean:647`),
  member lists complete (`mFs_voll`, `mLocks_voll`, `mCs_voll`), plus
  `TraegerSchreibt mHauptA (.inl MTab.privA) = true` by `rfl` (same conjunct is
  proved by `decide` in accepted `PoolZeuge.lean:205`).

Accepted-lemma signatures verified against the live tree in this clone:
`akzeptiertSpecX_of_spec`, `geteiltV_leer`/`geteiltA_leer`, `mP_akzeptiert`,
`akzeptiert_pruefer`, `Pruefer.korrekt` (`Zielsatz/Spec.lean:1624`), `mE`
(`Zielsatz/SpecProben.lean:137`), `zweiFaeden_bewegt_gilt` (`Zielsatz/Proben.lean:223`).
Consumer fit verified against `X86/TsoGxRefine.lean` (present in this clone):
the three delivered facts match the `brueckenSchrittGx`/`brueckenLaufGxGeteilt`
premises `hAbg`/`hFuss`/empty-`Tg` (hence vacuous `hTA`); `GutO`/`StartExklusiv`
stay explicit, `hWurzel`/`hlokK` stay with the consumer — none claimed here.

Review criteria:

- No `sorry`/`admit`/`axiom`/`native_decide`/`sorryAx`/`unsafe` in the full diff.
  No `intro _`, no `have _ :=`, no `forall rho`/`forall v`, no Prop-typed premise.
  Every premise (`hC`, `hvoll`) is used by its proof.
- `#print axioms` for all five theorems present in the file; author build evidence
  shows exactly `[propext, Classical.choice, Quot.sound]` for each (standard).
- Existing files untouched except one appended import line in
  `grammatik/Grammatik.lean` (`import Grammatik.X86.TsoGxChecker`). File list matches.
- Accepted evaluator lifted, never copied: no definitions duplicated, no machine
  steps added, no `HwAdapter` instantiated; reuse is `Pruefer.korrekt`,
  `akzeptiertSpecX_of_spec`, `geteiltV_leer` unchanged.
- Planted refusals: N/A — the file introduces no Bool and no machine steps, and
  claims none. No refusal owed.
- Witness non-degenerate: all premises instantiated JOINTLY on concrete values
  (concrete checker, concrete unit, complete lists) plus a table-write fact on the
  two-thread program (`hauptA` writes `privA`). The `mE`-vs-`Merkmal` name clash
  was hit and fixed with explicit `Zielsatz.mE` (visible in build evidence:
  one 12-error probe, then 0 errors). Two-core/forwarding/step-run boilerplate
  from the hardware-family MECHANISM does not apply (no machine steps added);
  the witness cites `zweiFaeden_bewegt_gilt` for the memory-changing run without
  conjoining it — acceptable for checker-premise theorems under HARD RULE 13
  (no run-statement premises; table-write fact present), noted as a suggestion only.
- Silicon facts: none stated, none owed; CUTS says so explicitly.
- CUTS honest, no claim larger than the proof: CUTS lists exactly what is proved
  and leaves `GutO` (FINDING 1, hardware assumption leg (c)), `StartExklusiv`
  (FINDING 2, `Laufzeit` leg (d)), the machine side, the per-access target-to-W/GX
  simulation and the full bridge OPEN. No hardware-correspondence and no W/GX
  closure claim. The theorem name `checker_liefert_wgx_pruefer` delivers only the
  three checker premises, matching its statement.

## Last build result

- `./lean-bau` in this review clone (base without the candidate file, OWN ONLY):
  `Build completed successfully (653 jobs).`
- Candidate build evidence (author side, not independently reproduced here by
  design): final `./lean-probe grammatik/Grammatik/X86/TsoGxChecker.lean`
  `== 0 error(s) in the COMPLETE output; exit 0`, `./lean-bau`
  `Build completed successfully (644 jobs).` (653 vs 644 is the base drift:
  this clone already contains `X86/TsoGxRefine.lean`, which the candidate base
  lacked; the candidate adds a disjoint new path plus one import line.)

## What remains open

- Consumer-side premises (`hWurzel`, `hlokK`, start-anchored bridged run,
  LOCK-leg assembly, `valX86_sound`) stay with lane 1215's `TsoGxRefine` line,
  as both CUTS blocks state.
- Suggestion (non-blocking): conjoin `zweiFaeden_bewegt` (or cite the reached
  memory-changing step as a proved conjunct) in a future joint witness so the
  non-degeneracy is a checked step rather than a syntactic write fact plus citation.

## What in the task is wrong

- The lane-1252 brief pins the candidate as `1251 <full pinned HEAD>` with the
  hash slot empty; the actual pinned HEAD came from `.tmp/review/SNAPSHOT.json`.
- The CONTEXT/MECHANISM paragraphs (`HwAdapter`, `HwWf`, two-core forwarding
  witness) are hardware-family boilerplate and do not apply to this checker-side
  discharge, as the author report already records. Judged against the TASK
  paragraph (discharge or FINDING, assume nothing), which is fully delivered.

## Verdict

VERDICT: ACCEPT
