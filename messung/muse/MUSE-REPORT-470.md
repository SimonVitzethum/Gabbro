# MUSE-REPORT-470: Independent exact-candidate review of 422

## Scope

- Candidate: lane 422, pinned HEAD `1402750e058b76c5c377099212577676440670bf`
  (base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`), files
  `MUSE-REPORT-422.md`, `grammatik/Grammatik.lean` (one additive import line),
  `grammatik/Grammatik/X86/ReleaseAcquire.lean` (new, 291 lines).
- Sources inspected: `.tmp/review/SNAPSHOT.json`, `.tmp/review/author-422/OWNER-TASK.md`,
  `PATCH.diff`, supplied candidate file `.tmp/review/author-422/grammatik/Grammatik/X86/ReleaseAcquire.lean`,
  `MUSE-REPORT-422.md`, `BUILD-EVIDENCE.json` (all 197 lines read).
- Reference models in own clone: `grammatik/Grammatik/Speichermodell/Sicht.lean`
  (`Ordnung`, `beitrag`, `nachricht`, `Sicht.verein/eins/setze`, `verein_rechts`,
  `setze_anders/selbst`), `grammatik/Grammatik/X86/TSO.lean` (`issueByte`, `loadByte`,
  `flushKern`, `zaunBereit`, `neuestens`, `issue_anderer_kern`, `issue_kein_speicher`,
  `issue_erhaelt_berechtigungen`, `issue_haengt_an`, `flush_schreibt_kopf`,
  `flush_entfernt_kopf`, `load_nach_issue`, `load_ohne_eintrag`, `zaunBereit_iff_leer`,
  `sbStart/sbX/sbEins/sbNach1/sb_schritt1`). All 12 reused lemmas/defs exist with
  matching signatures; no invented behaviour.

## Reproduction (own clone, temporary staging, restored afterwards)

- Staged only the supplied candidate file plus the one umbrella import line, then:
- `bash ./lean-probe grammatik/Grammatik/X86/ReleaseAcquire.lean`:
  `0 error(s), exit 0`, all 15 axiom lines printed, each `[propext]` or none.
  Exact match with the author's claimed probe log.
- `bash ./lean-bau`: `Built Grammatik`, `Build completed successfully (416 jobs)`
  (author measured 393 jobs on its older base; job-count drift is master drift,
  not a defect). Green with the candidate staged.
- Scratch axiom check `AxCheck470.lean` (removed afterwards):
  `gabbro_ziel depends on axioms: [propext, Classical.choice, Quot.sound]` — standard three, unchanged.
- Cheat scan on candidate file: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- Off-limits scan: no `OptimizationRules`/`OptimizationWitnesses`, no Spec/Zielsatz,
  no emitter/checker/Rust, no Typen/codec touches. Friend paths untouched.
- Restored afterwards: candidate file removed, `grammatik/Grammatik.lean` restored
  byte-identical from backup; `git status --short` clean before this report.

## Semantic checks

- Source side: all five theorems unfold to the actual `Sicht.lean` definitions and
  hold for the stated reason (`freigabe` contribution is `m.sicht verein eins`,
  so `le_max_left`; `nachricht freigabe` is `v.setze x ts`, so off/on-location facts
  follow from `setze_anders/selbst`; `entspannt` is `eins`, so off-location is 0;
  transfer chains the first with `verein_rechts`). Correct, local, no payload safety claimed.
- Target side: all six theorems derive from the actual TSO ops via the cited accepted
  lemmas, with every Prop premise used in the proof body
  (`freigabe_braucht_flush` uses all four: issue step, core separation, foreign miss,
  permission preservation). All facts are LOCAL to the acting core's buffer; no
  foreign-buffer drain is claimed. `CUTS` states this boundary explicitly.
- `ReleaseSchreiben` (`ReleaseAcquire.lean:23-25`) is a thin alias for a plain
  `issueByte` success, not a duplicated IR/executor. No second machine.
- `SeqCstTotal` (`:186`) is an empty inductive with `kein_seqcst_total` its vacuity
  proof. This carries no semantic content by construction, but the author labels it a
  stated non-claim and claims no total order, so it is honest documentation rather than
  a forged evidence item. Not counted as bridge evidence.
- Witnesses: `freigabe_braucht_flush_zeuge` and `freigabe_sichtbar_zeuge` reuse the
  accepted `sbStart/sbNach1/sb_schritt1` run; the `by decide` steps (stale foreign load,
  byte inequality after flush, fence-readiness) all elaborate green in my probe, so the
  memory-changing behaviour is reproduced, not asserted. `freigabe_entspannt_zeuge`
  concretely separates acquire (inherits 2) from relaxed (contributes 0) on one message.
- Minor note (no repair): the stored-value parameter `w` in
  `freigabe_nachricht_traegt_sicht`/`_eigen` is used in the statement's `nachricht`
  term but not in the proof body, since views drop payloads. That is the correct
  semantics (and exactly why no payload claim is made), not a discarded Prop premise.
- No safety weakening: contracts, atomic rely, race/memory guarantees untouched; no new
  refusal, diagnostic, or emission behaviour.

## Bounded claim accepted

Generic source/target acquire-release facts over the actual accepted definitions, with
explicit non-claims (no lowering, no foreign drain, no multi-byte atomicity, no seq_cst
total order, no payload safety, no progress/timing/cost, no interrupt/device/code claim).
Full compiler closure, source lowering, W/GX simulation, hardware or performance claims
are neither made nor accepted.

## Open

- None for this candidate. End-to-end message passing (flag seen implies data seen across
  cores), per-access TSO-to-W/GX simulation, and granularity bridging remain with the
  bridge, as the author's `CUTS` states.

CANDIDATE: 422 1402750e058b76c5c377099212577676440670bf
VERDICT: ACCEPT
