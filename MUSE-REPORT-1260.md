# MUSE-REPORT-1260: Exact review of candidate 1259 — full review on delivered files

CANDIDATE: 1259 9fd9fe2603bdfec61d70b0bb92ad7e1e9338c0e4

VERDICT: ACCEPT

## Assignment

Lane 1260: independent exact review of candidate 1259 ("Pipeline work: taken-path
bound and per-round loop correspondence"). Report-only; own file is
MUSE-REPORT-1260.md only.

## Verification done

- Clone: `/home/simon/Dokumente/gabbro-muse/a1260` — matches.
- Branch: `muse/1260` (`git rev-parse --abbrev-ref HEAD`) — matches.
- `./lean-bau` on this clone (unchanged tree): last result line
  `Build completed successfully (658 jobs).` — green.

## Re-review note (new snapshot)

The previous report pinned the superseded head `231b3e93789ec55e20f01a847e8eedd2dcf790a4`
(itself superseding `1650a2899f5eeea3db5883139ea47231fd605707`). Those verdicts
are stale: the author has repaired again and the coordinator pinned a NEW head
`9fd9fe2603bdfec61d70b0bb92ad7e1e9338c0e4` (same base
`515546d0e2430c0d416ede74e3add0166e88e2de`, same file list:
`MUSE-REPORT-1259.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/PipelineWorkPath.lean`, clean true). This report
reviews the candidate as delivered under `.tmp/review/author-1259/` (full
664-line file read, diff, owner task, build evidence) and reaches its own
substantive finding below. Neither stale head is approved anywhere in this
report.

## Method (correction applied)

Per the corrected review instructions, the author clone and pinned commit are
not readable from this clone, and "bad object" was never treated as a finding.
The candidate was reviewed AS DELIVERED under `.tmp/review/author-1259/`:

- `SNAPSHOT.json`: author 1259, head
  `9fd9fe2603bdfec61d70b0bb92ad7e1e9338c0e4`, base `515546d0e...`, files
  `MUSE-REPORT-1259.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/PipelineWorkPath.lean`, clean true.
- `PATCH.diff` (812 lines): exactly three hunks — new report, one appended
  `import Grammatik.X86.PipelineWorkPath` line in `Grammatik.lean`, and the
  new 664-line file. Diff tail and delivered file match line for line.
- `OWNER-TASK.md` (lane 1259 task), `MUSE-REPORT-1259.md` (127 lines),
  `BUILD-EVIDENCE.json` (logged probe/build outputs incl. honest
  intermediate red states).
- The new Lean file read in full (all 664 lines), plus content scans for
  banned constructs, undeclared axioms, `Prop`-typed premises and contract
  quantification.

Earlier blocked rounds of this lane (no candidate material, process-level
repair verdicts against dispatch) are superseded by this substantive review
and serve as history only. No stale snapshot is approved.

## Findings (checklist of `.tmp/LANE.md` line 23)

- Banned constructs: none. Content scan over the new file finds no `sorry`,
  `admit`, `axiom` (declaration), `native_decide`, `unsafe`, `split_ifs`,
  `norm_num`, `ring_nf`, `TODO`/`FIXME`/`XXX`, `intro _` or `have _ :=`.
  The only `sorry|admit`-family hits are the prose word "admitted" (4x,
  comments) and the 29 `#print axioms` lines. No premise has type `Prop`
  itself; no `forall rho`/`forall v` contract quantification.
- Axioms: standard. The file ends with `#print axioms` for all 29
  definitions/theorems. The logged outputs (BUILD-EVIDENCE) show every item
  within propext/Classical.choice/Quot.sound (`genommenArbeit` and `wpWs`
  axiom-free), inherited from reused lemmas; no new axiom is declared.
- Scope discipline: `Grammatik.lean` gains exactly one appended import line;
  no other existing file is touched; `OptimizationRules.lean` /
  `OptimizationWitnesses.lean` untouched; no checker/Spec/goal/emitter file
  touched.
- Premise use (traced per proof): `laufBytes_genommen` consumes
  `hprog` (subst), `hg`/`hlauf`/`hc`/`hf`-via-`hfs`/`hrip` through the
  lifted `Pipeline.lauf_zu_laufBytes`, plus `arbeit_decodiert` and an
  arithmetic close. `deckung_pfad_chunk` feeds `hflach`/`hchunk` into
  `senkStmt_flach_laenge`, `hprefix` by subst, `hsrc` stays in context for
  the closing `omega`. `runde_einzel` consumes `hLese`, `hBisStabil`,
  `hBed` (both branches via `hbv`/`hbv1`), `hWeiter`, `hEnde`,
  `hUeberlauf` (final `absurd`). `schleife_pfad_bytes` feeds `hr`/`hwx`/
  `hcode` into `schleife_bytes` and the simulation premises into
  `schleife_korrekt_endlich`; the `st`-named binders avoid the `s`-capture
  the author documents. `wpWeiter`/`wpEnde` split on both `Rep` cases and
  discharge each with the matching hypothesis. No conclusion restates a
  premise; no discarded hypothesis.
- Lifted, not copied: the family evaluator and bridges are referenced by
  name — `lauf_zu_laufBytes`, `schleife_korrekt_endlich`,
  `schleife_bytes`/`relax_laufBytes`, `arbeit_decodiert`,
  `pipeSummary_expand`, `senkStmt_flach_laenge`,
  `schleife_verweigert_schlechten_koerper`,
  `schleife_verweigert_ret/sprung` — never redefined. The file's only new
  definitions are `genommenArbeit`, `wpWs`, `wpBild`, `wpMem`, `wpPost`.
  Runs are the real `lauf`/`laufBytes`/`laufL`/`laufBytesI`/`retryLauf`;
  no second semantics, no second IR, no new cost model.
- Refusals really refuse: `gift_pfad_ret`/`gift_pfad_sprung` close by the
  lifted refusal lemmas on concrete bodies; `gift_pfad_knapp` and
  `gift_pfad_verlaengerung` close by `decide` / the prefix-refusal lemma
  on concrete data. All four are computation-checked by typechecking, as
  are both `_zeuge` refusal companions.
- Witnesses non-degenerate and joint: `laufBytes_genommen_zeuge` and
  `deckung_pfad_chunk_zeuge` conjoin `PipePaket` (the accepted package:
  one table its contract writes); `runde_einzel_zeuge` runs one real
  `retryLauf ... 1` round to `.ok`; `schleife_pfad_bytes_zeuge` conjoins
  `zwV.schreibt () = true` with the memory-changing round facts
  `(zwSigma0.slots () 0 ()).n = 0` and
  `((zwSigma1 zwSigma0).slots () 0 ()).n = 1`, all closed by `rfl`
  (true by computation, not asserted). Every syntax-premise theorem has
  its `_zeuge` companion even though the owner task carried no fixed
  target lines.
- Silicon honesty: no new hardware fact is stated anywhere. The witness
  image reuses the `isaSpeicher` shape, `read64` comes from the accepted
  memory model, flag effects come from `bedingung`, byte correspondence
  is the reused `relax_laufBytes`. No encoding, fault-class or ordering
  claim beyond the reused definitions.
- CUTS honest, claim not larger than proof: the CUTS block (lines 571-632)
  lists exactly what is proved and marks fragment/open territory —
  straight-line prefixes and shallow chunks only, no `forever` budget, the
  one-round simulation premise stays per-producer, no block-size
  induction, no exhaustion timing, admission beyond `CodeAt`/`WX` left to
  `PipelineImage`/`PipelineEntry`, no TSO/concurrency claim, instruction
  counts not silicon latencies. In particular no hardware-correspondence
  beyond the model-internal leg and no W/GX claim.

## Probe limitation (stated plainly)

The instructed in-clone probe step (copy the candidate file into this
clone's `grammatik/` and run `./lean-probe`) could not be executed: file
creation outside the owned report is denied by tool policy and the copy
command is refused by the permission classifier. Compilation evidence is
therefore the author's logged outputs in BUILD-EVIDENCE.json — final
`./lean-probe` 0 errors with the full `#print axioms` listing, final
`./lean-bau` green (644 jobs) — cross-checked against the delivered file:
every theorem named in the logged axiom output exists in the file with a
matching statement, the log's intermediate red states are consistent with a
genuine multi-commit session, and my full read found nothing the green log
could not explain. This lane's own `./lean-bau` on the unchanged tree
remains green (`Build completed successfully (658 jobs).`). No Lean change
by this lane; owned file only.

## Verdict rationale

ACCEPT because the delivered candidate passes every item of the exact-review
checklist on its own merits: no banned construct, standard axioms with full
`#print axioms` coverage, minimal scope (one import line), every premise
traced into its proof, accepted evaluators and bridges lifted by name rather
than duplicated, four poison probes plus two refusal witnesses that fire by
computation, joint non-degenerate witnesses with memory-changing facts for
every syntax-premise theorem, no new silicon fact, and CUTS that state the
fragment boundary honestly with no hardware-correspondence or W/GX overclaim.
The single residual — no independent in-clone compilation, blocked by sandbox
permissions rather than by the candidate — is disclosed above and does not
change the verdict: the logged build evidence is complete, internally
consistent, and matches the reviewed file statement for statement. This
verdict approves exactly the pinned head named in the machine-readable line
and nothing else.

New definitions/theorems by this lane: none (report-only review).

## Remaining open (not defects)

- The per-round simulation premise stays per-producer by design (CUTS);
  scheduling/timing, TSO/concurrency, and whole-program induction belong to
  other lanes, as the file states.
- The author report's remark that the owner task names a nonexistent
  `PipelineWorkBranches.lean` file is a task-text imprecision the author
  handled correctly (worked against `PipelineWork.lean`); no candidate
  change needed.

## Believed-wrong in the task (resolved by the correction)

- The lane file's `<full pinned HEAD>` placeholder and the "read the diff in
  the author clone" instruction conflicted with HARD RULE 1; both are
  superseded by the delivered-files correction (pinned `SNAPSHOT.json` plus
  `PATCH.diff` and file copies under `.tmp/review/author-1259/`), which this
  review used.

## Open work

- None for this lane: the exact review of candidate 1259 at the pinned head
  is complete with the verdict above.

Co-Authored-By: muse-agent-1260 <muse-agent-1260@noreply.invalid>
