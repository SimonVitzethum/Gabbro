# MUSE-REPORT-1259: taken-path bound and per-round loop correspondence

## What was done

New file `grammatik/Grammatik/X86/PipelineWorkPath.lean` (≈590 lines) plus one
`import Grammatik.X86.PipelineWorkPath` line appended to `grammatik/Grammatik.lean`.
Follow-up of the pipeline work layer: the taken-path bound is now connected to the
executed `lauf` prefix of the byte-level run (instead of the static whole-list
length), and the per-round loop body correspondence plus the labelled-to-bytes leg
with `PipelineLoops.lean` are proved. All existing definitions reused unchanged;
no file besides the two owned ones touched; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`.

Definitions: `genommenArbeit`, `wpWs`, `wpBild`, `wpMem`, `wpPost`.

Theorems (each with `#print axioms`, all within
propext/Classical.choice/Quot.sound, most with no axioms at all beyond the
reused lemmas):

- Taken path: `laufBytes_genommen` (fetched run of `T.length` steps retires
  exactly the taken prefix `T` of the static program; retired work is `T.length`;
  taken length within static length), `deckung_pfad_chunk` (executed prefix of a
  shallow lowered chunk covered by the admitted `pipeSummary`), both with joint
  `_zeuge` on the accepted witness chunk (`PipePaket`: one table its contract
  writes, source slots `7 -> 35` / `9 -> 6` through actual `execBlock`,
  fetched-byte run observably changing memory).
- Loops: `schleife_runde_zerlegung` (budget split into one body segment plus the
  rest), `runde_einzel` (one continuing source round is the one-round labelled
  segment to the end label, explicit `laufL_add` anatomy, bound read through
  `hBed`), `schleife_pfad_bytes` (finished source run is the fetched-byte run of
  its relaxed image via `schleife_korrekt_endlich` + `relax_laufBytes`), with
  `wpWeiter`/`wpEnde` (one-round simulation at the loaded `adrL` map) and joint
  witnesses on the loaded witness image with a memory-changing round `0 -> 1`.
- Refusals (pipeline_refuses_* style) + 4 poison probes, all firing by
  computation: `pfad_verweigert_schlechten_koerper`, `pfad_verweigert_verlaengerung`,
  `gift_pfad_ret`, `gift_pfad_sprung`, `gift_pfad_knapp`, `gift_pfad_verlaengerung`,
  plus `_zeuge` for both refusal theorems.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineWorkPath.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (644 jobs).`
- Commits on `muse/1259`: skeleton+import, prefix bridge, dynamic Deckung,
  per-round correspondence, fixtures, leg, refusals/CUTS (7 commits).

## What remains open

Per the file's CUTS: taken-path coverage is straight-line prefixes and shallow
chunks only; `forever` has no finite taken budget; the one-round body simulation
premise stays per-producer; no block-size induction to whole-program `src`;
no exhaustion timing; admission beyond `CodeAt`/`WX` composes through
`PipelineImage`/`PipelineEntry`; no TSO/concurrency claim; counts are
instruction counts, not silicon latencies.

## Review response (lane 1260, blocked review)

The independent review (lane 1260, candidate `1259 1650a2899f5eeea3db5883139ea47231fd605707`)
returned VERDICT: REPAIR with a precise blocker: the reviewer clone never received
the author branch, so no candidate diff was read and no Lean code was examined.
The REPAIR is directed at review dispatch, not at these proofs: it makes zero
substantive findings against `PipelineWorkPath.lean`, axioms, witnesses, silicon
facts, or CUTS. There is therefore nothing to repair in the deliverable, and
nothing was weakened, restated, or re-scoped in response. The candidate stands
unchanged and re-presentable.

Self-audit performed instead (same checklist an exact review would apply):

- Forbidden tokens: `grep` for `sorry|admit|axiom|native_decide|unsafe|TODO|FIXME|XXX`
  over the new file returns only benign substring hits (`admitted` in prose,
  `#print axioms` lines). No `sorry`, `admit`, `axiom`, `native_decide`,
  `unsafe`, no placeholders.
- Axioms: full `#print axioms` output re-verified (see probe output); every
  theorem is within propext/Classical.choice/Quot.sound, inherited from reused
  lemmas; no new axiom, no `Prop`-typed premise.
- Premise use: every hypothesis of every new theorem is consumed by its proof
  (`hBed` steers the `runde_einzel` case split via `hbv`/`hbv1`; `hBisStabil`
  feeds the exit agreement; all lowering/validator equations feed their
  bridges). No conclusion restates a premise; no `forall rho`/`forall v`
  contract quantification; runs are the real `retryLauf`/`lauf`/`laufBytes`/
  `laufL`/`laufBytesI`, never a second semantics.
- Silicon honesty: no new hardware fact is stated. The witness image reuses
  the `isaSpeicher` shape, little-endian `read64` comes from `Speicher.lean`,
  flag effects come from `bedingung`, and byte correspondence is
  `relax_laufBytes` reused, not re-proved.
- Owned files only: `grammatik/Grammatik/X86/PipelineWorkPath.lean`,
  `grammatik/Grammatik.lean` (one import line), `MUSE-REPORT-1259.md`. Nothing
  else touched.

Fresh verification for this report:

- `./lean-probe grammatik/Grammatik/X86/PipelineWorkPath.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (644 jobs).`
- No Lean change was needed or made for this review round; only this report
  section was appended.

## Task remarks (things believed wrong or imprecise)

1. The task names lane 1233's file `PipelineWorkBranches.lean`; no such file
   exists in the tree. The actual work layer is `PipelineWork.lean` (header says
   lane 1165). I worked against `PipelineWork.lean`; if a branches file existed
   elsewhere it was not visible from this clone.
2. The task text's `s`/`st` capture trap: in `schleife_pfad_bytes` the
   `hWeiter`/`hEnde` premises must bind the state variable under a fresh name
   (`st`), otherwise `s.rip` in the address map is captured by the inner
   quantifier and the map is no longer fixed. Fixed that way, no extra premise.
3. No `ZEUGE:` lines were in the task, so there were no fixed target statements;
   `_zeuge` companions were still provided for every syntax-premise theorem.
4. Display caution: file-read output rendered `Vertrag` lowercase in one place;
   the Lean error plus a case-sensitive `grep` gave ground truth (capital).
   Cost a few turns, no build impact.
5. Resource bottleneck (genuine, for the record): one `./lean-probe` hit the
   600 s timeout on the shared single Lean slot and passed on retry with a
   longer budget; contention with other lanes, not the file (unchanged small
   file, fast on retry).
