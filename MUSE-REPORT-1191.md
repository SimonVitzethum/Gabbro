# MUSE-REPORT-1191: Pipeline spill code generation with privacy

## Task
Follow-up of lane 1167 (`PipelineRegAlloc.lean`): a spilled live variable was
refused there for lack of spill code. New file
`grammatik/Grammatik/X86/PipelineSpill.lean` (+ one import line in
`grammatik/Grammatik.lean`) adds spill/reload code in the private frame region,
a decided validator, and theorems that validated spill plans preserve the source
meaning while touching neither a source table nor another spill slot
(`ComposeSpillPrivacy.lean` vocabulary). No existing file edited except the
import line; `OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched;
no second IR, no second source interpreter. Rust out of scope.

## What was done
- Spill fragments over the accepted pilot shape (address materialisation
  `movImm64 adr slotAddr` + zero-displacement `store64`/`load64`, the shape the
  accepted `senkStmt` uses): `spillSaveCode`, `spillLoadCode`,
  `spillSave_gerade`, `spillLoad_gerade`, and per-sequence `lauf` meaning
  `spillSave_lauf`, `spillLoad_lauf` against the canonical `schritt` lemmas
  (`schritt_movImm64`, `schritt_store64_erfolg`, `schritt_load64_erfolg`,
  `effAddr_null`, `lauf_anhang`).
- Decided validator `spillPlanOk` (in-frame slots, `Nodup` slots, frame off the
  code and inside 64 bits, every slot disjoint from every declared table
  extent) with one projection per leg: `spillPlan_inRahmen`,
  `spillPlan_nodup`, `spillPlan_offCode`, `spillPlan_schranke`,
  `spillPlan_offDaten`.
- Privacy: `spill_slot_ohneUmbruch`, `spill_schlitze_getrennt` (distinct slots
  are footprint-disjoint via `disjunkt_von_intervallen`), `SpillVonTabellenGetrennt`
  + `spillPlan_tabellenGetrennt` (validated slots over a table-free frame avoid
  every placed source slot; reuses `PipeRahmenGetrennt`, `schlitzNat_schranke`).
- `spill_rundreise_privat`: reached save reloads through the token-threaded
  step with permission preservation and disjoint foreign stability, composed
  from the accepted `ComposeSpillPrivacy_verbindung`, plus pairwise slot
  separation over the plan.
- `spill_haelt_bedeutung`: validated pipeline bytes (`pipeline_correct`) plus a
  validated spill plan give the fetched run with world/environment represented,
  slot-vs-table privacy, pairwise slot separation, and slot-vs-extent
  separation. Style matches `pipe_alloc_haelt_bedeutung` / `pipeline_correct`.
- General refusals `spill_verweigert_tabelle`, `spill_verweigert_aussen`,
  `spill_verweigert_kollision` (each through its validator leg).
- Probes: `spill_probe_pos` (validates), `spill_probe_tabelle` (+
  `spill_probe_tabelle_satz` through the refusal theorem),
  `spill_probe_aussen`, `spill_probe_kollision`, `spill_probe_code`
  (witness frame `spillR0 = <16384, 16>`, slots `spillP0 = [0, 1]`, extents
  `spillD0 = [8192, 8200]`).
- Witnesses: `spillR0_getrennt` + `spill_haelt_bedeutung_zeuge` (joint on the
  pipeline witness program `pwSrc`: rows 7 -> 35, 9 -> 6, non-degenerate and
  memory-changing) and `spill_rundreise_privat_zeuge` (reached save of `42`
  with observable memory change beside writer program `zeugenU`).
- CUTS block + `#print axioms` for every main theorem: all within
  `[propext, Classical.choice, Quot.sound]` (most use fewer).

## Verification
- `./lean-probe grammatik/Grammatik/X86/PipelineSpill.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (620 jobs).` (whole project green)

## Open / not claimed
As listed in the file CUTS: interleaved lowering with live-range splitting
(fragments save/reload whole named slots; no variable-homing decision is made
here); callee-saved restore and argument passing (inherited fragment limits);
TSO freshness beyond the reused `SpillFrisch` vocabulary; read-trace
representation; full loaded-image connection (`pipeline_correct_loaded` shape).

## Task feedback
Nothing in the task was wrong. One note: the first table-extent probe I wrote
named datum `8192` against slots at 16384 and the validator correctly accepted
it (disjoint) — the probe, not the validator, was wrong; fixed to datum
`16384`, which genuinely overlaps slot 0. Also `PassKind`/`BlockCert`
unqualified resolve to a different namespace in this file's open set, so the
closing theorem qualifies them as
`OptimizationRules.PassKind`/`OptimizationRules.BlockCert`.
