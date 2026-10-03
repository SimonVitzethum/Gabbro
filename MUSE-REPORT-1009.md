# MUSE-REPORT-1009: Exact review of author 859 (region-ceiling closing)

## CANDIDATE

CANDIDATE: 859 7191caf341e969ac272c99ebb86e43f0579541e0

## VERDICT

VERDICT: ACCEPT

Acceptance is bounded — see scope section below; the substantive verdict is
unchanged.

## What was reviewed

- Pinned snapshot: base `b040b155` (= this clone's HEAD, verified), 3 files:
  `MUSE-REPORT-859.md`, `grammatik/Grammatik.lean` (one appended import line),
  `grammatik/Grammatik/X86/ComposeRegionCeil.lean` (new, 232 lines).
- Owner task (region-ceiling composition closing, ZEUGE:
  `ComposeRegionCeil_verbindung` + companion
  `ComposeRegionCeil_verbindung_zeuge`), author report, BUILD-EVIDENCE.json,
  and every referenced accepted definition/theorem in the base tree at the
  pinned base.

## Independent checks performed

1. Identity: clone path and branch `muse/1009` verified; snapshot base equals
   clone HEAD (`b040b155`); evidence commit log shows `7191caf3` directly on
   `b040b155`, matching SNAPSHOT.json.
2. Banned constructs: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
   `intro _`, or `have _ :=` in the candidate (only prose "admitted inputs").
   No premise typed as `Prop` itself.
3. Name/signature resolution against the base tree — all resolve with matching
   arity and argument order:
   `Regionen.reserviere/freiReserviere/ausricht/alleUnten`,
   `reserviere_voll_verweigert`, `freiReserviere_kann_scheitern`,
   `freiReserviere_ohne_statik_gebunden`, `zeugenStart/zeugenRegion`,
   `RegionSeparation.trennungOk/allePaareDisjunkt`,
   `RegionFresh.frisch_zwei_verdikt/frisch_schreibt_rahmen`,
   `frischRegionZwei/frischSpeicher/frischRegionUeberlapp`,
   `frisch_zwei_verdikt_zeuge/frisch_schreibt_rahmen_zeuge`,
   `frischUeberlapp_verweigert`, `zeugenReserviere_voll`,
   `TableLayout.zeugenU_schreibt` (statement identical to the witness
   conjunct), `Ausfuehrung.zeuge_speicher_aendert_sich` (`.2.1` selects
   exactly the memory-bytes-42 leg the witness needs).
4. Proof-term shape: every premise of the TARGET is consumed (reservations
   feed verdict + frame, gate values feed both refusals, `B`/`hB` feed the
   bound-loss existential via `freiReserviere_ohne_statik_gebunden`); the
   `rw [deckellos_benannt_offen]` steps bridge the gate to the accepted
   `freiReserviere` at exactly the used flag values; the witness `obtain`
   patterns match the cited witnesses' component counts (7-tuple from
   `frisch_schreibt_rahmen_zeuge`).
5. Non-degeneracy: real table `konto` with writer `setze`; reached run with
   byte 42 at 8192 from zero; nonzero `write64` with observed byte change
   and preserved neighbour read; planted refusals (8192-vs-4KiB
   refuse-on-full, overlap refusal, default refusal, loud opt-in failure).
6. No guarantee weakening: the gate carries `scheitert` and the lost static
   bound through (never removes them); default refusal preserved; the
   `basis + len <= 2 ^ 64` physical bound is restated, not dropped.
7. Architecture scope: the file defines no decoder, executor, byte form, or
   TSO/atomicity claim; sequential-footprint limitation and the TSO-bridge
   owner (567/TSOHistory), image owners, and lane 570 are named in CUTS.
   No invented determinism over undefined hardware state.
8. Hygiene: owned files only; no new diagnostic/gift/example/CLI numbers; no
   MARKE_EMIT changes; no source/checker/Spec/goal/emitter edits; no
   friend-reserved optimiser files. Axioms per evidence are subsets of the
   `gabbro_ziel` standard (`[propext, Quot.sound]` max).
9. Build evidence consistency: 511-job green build with per-theorem axiom
   prints matching the file's `#print axioms` block; `lean-probe` 0 errors.

## Bounded-acceptance notes (not repairs)

- The companion witness conjoins the TARGET's conclusion legs on one shared
  concrete chain (premises discharged inside the cited accepted witnesses)
  rather than literally applying `ComposeRegionCeil_verbindung`. Joint
  inhabitation holds on identical values; a literal application would add no
  semantic force.
- The three middle lemmas are thin compositions restating accepted theorems;
  that is the assigned composition-closing shape, not a rule-4(a) violation
  (no premise is renamed as a conclusion; each conclusion is derived through
  a named accepted theorem).
- No independent rebuild was run: reproducing the build would require placing
  the candidate into `grammatik/`, which this report-only review does not own.
  Acceptance rests on static verification plus the internally consistent build
  transcript (exact commit, job count, per-theorem axiom lines).

## Scope of acceptance

Composition of the accepted ceiling allocator with the accepted separation
verdict and fresh-region frames, plus the named ceilingless opt-in gate with
default refusal. Full source-to-final-bytes validation, per-access TSO
refinement, loader/image, decoder/semantics/cost/budget/entry work, and
source-to-allocator correspondence remain OPEN per the file's CUTS.

## Last build result

No build run by this reviewer (report-only review; no source touched).
Author evidence: `./lean-bau` `Build completed successfully (511 jobs)`;
`./lean-probe grammatik/Grammatik/X86/ComposeRegionCeil.lean`
`== 0 error(s) in the COMPLETE output; exit 0`.

## Task assessment

Nothing in the owner task appears wrong. The target needed no extra premise.
This review found no defect requiring REPAIR.
