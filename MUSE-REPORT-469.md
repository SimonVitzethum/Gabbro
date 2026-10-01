# MUSE-REPORT-469: Independent exact-candidate review of 421

## Clone / branch verification
- Clone `/home/simon/Dokumente/gabbro-muse/a469`, branch `muse/469`: MATCH (verified via `git rev-parse` + `git branch --show-current`).
- Candidate snapshot `.tmp/review/SNAPSHOT.json`: author 421, pinned HEAD `87f15ba98b807321e2ec2023058bcf86e460bd28`, base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`, files `MUSE-REPORT-421.md`, `grammatik/Grammatik.lean` (one additive import), `grammatik/Grammatik/X86/WordAtomicity.lean` (new). `clean: true`.
- Reviewed the exact supplied material: `author-421/OWNER-TASK.md`, `PATCH.diff`, `WordAtomicity.lean`, `MUSE-REPORT-421.md`, `BUILD-EVIDENCE.json`. No other clone read. No network, no push.

## Reproduction in own clone
- Staged ONLY the supplied candidate files temporarily (new `WordAtomicity.lean` + one additive umbrella import line), ran `./lean-probe grammatik/Grammatik/X86/WordAtomicity.lean`, then fully restored (candidate file deleted, `Grammatik.lean` restored from backup; `git status` clean before this report).
- Probe result: `== 0 error(s) in the COMPLETE output; exit 0`. All `#print axioms` are subsets of `[propext, Quot.sound]` (several dependency-free); no `sorryAx`. Matches the author's claimed `0 errors, exit 0` exactly.
- Full `./lean-bau` not re-run: the author's BUILD-EVIDENCE.json already contains the relevant control experiment (pristine tree with the import stashed aborts identically at the umbrella `Grammatik.lean` olean step with `failed to create thread`, exit 134, under documented swap exhaustion), and the module-level green is established by the probe above, which elaborates the file with all its imports. Re-running a full contended build would add no signal.
- `gabbro_ziel` impact: none by construction. The new file is a leaf imported only by the umbrella; nothing in `Zielsatz/` imports it and it imports nothing from `Zielsatz/`, so it is outside `gabbro_ziel`'s import closure. No checker, Spec, goal, Rust, emitter, or codec file touched. `OptimizationRules.lean`/`OptimizationWitnesses.lean` untouched.

## Semantic checks against accepted models (all names resolved in this tree)
- Every applied lemma exists with a matching signature: `lockSchritt_xadd_erfolg` (LockedOps.lean:117), `read64_nach_write64` / `read64_rahmen` / `write64_rahmen` (Speicher.lean:327/362/347), `paket_reisst` (TSO.lean:459), `addrOff_ne8` (Speicher.lean:65), `disjunkt_von_intervallen` (Speicher.lean:183), witnesses `lockStart`/`lockAddr`/`lockNach1`/`lockEv1`/`lock_schritt1`, `sbStart`/`sbNach1`/`sbX`/`sbY`/`sbEins`/`sb_schritt1`/`sbX_ne_sbY`, `zaunStart`/`zaun_start_fremd`.
- No new executor: the only `def`s are the guard `WortGuard`, the observation alias `WortBeobachtet`, addresses `wortFern`, and concrete states `wortRiss2`/`wortRiss3`. Every transition step invokes the accepted `lockSchritt` / `issueByte` / `flushKern`. No assumed word atomicity; per-byte tearing is proved, not hidden (`wort_fuss_reisst` specializes accepted `paket_reisst` with correct single-core shape).
- No HARD-RULES violations: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (two grep hits are English prose "admit"); no `Prop`-typed premise (only `Prop`-sorted defs); every premise of every theorem is used by its proof (checked theorem by theorem, including `hles` in the read-back and `hdis`/`hread`/`haussen` in the frame lemmas); no conclusion restates a premise; no discarded premises; English only; CUTS block and `#print axioms` per main theorem present.
- Witnesses are joint, concrete, and memory-changing where applicable: `wort_schritt_liest_zurueck_zeuge` (LOCK step on `lockStart`/`lockAddr` with `decide`-checked byte change), `wort_fuss_reisst_zeuge` (single-core tear with `decide`-checked change), `wort_bleibt_unter_disjunkt_zeuge` (disjoint word at 8192 preserved while first word changes), both refusal witnesses on concrete addresses/states. `WortNachW` empty inductive + `kein_wort_nach_w` honestly marks the bridge OPEN instead of claiming it.
- Claim scope is exactly the bounded task: thin consumer layer over accepted `Speicher`/`TSO`/`LockedOps`, XADD shape only, frame/disjoint facts, refusals, tearing witness, open bridge. No source RMW closure, no hardware/timing/decode/ABI/checker/goal claim; CUTS states each exclusion.

## Observations (not defects, no repair required)
- `wort_rahmen_byte` (byte frame outside the LOCK footprint) overlaps the last conjunct of the already-accepted `lock_xadd_atomar` (LockedOps.lean), re-derived from the same accepted lemmas rather than applied from it. Harmless redundancy, sound, no second executor. A future lane may route it through `lock_xadd_atomar`; not a merge blocker.
- `WortBeobachtet` is a thin alias for `read64 m a = some v`; used consistently by the read-back theorem and witness. Fine as a consumer vocabulary name.
- Everything else (`wort_schritt_liest_zurueck` read-back, `read64_braucht_lesbar`, `write64_braucht_schreibbar`, `wort_bleibt_unter_disjunkt`, all three `lock_verweigert_*` refusals, `wort_fuss_reisst` specialization) has no accepted duplicate (verified by grep over `Speicher`/`TSO`/`LockedOps`).

## What remains open
- Per the file's own CUTS: no W/GX refinement, no silicon/timing correspondence, no decode/ABI/entry coverage, no source lowering. The author's report states all of this plainly. Nothing in the task is silently dropped.

CANDIDATE: 421 87f15ba98b807321e2ec2023058bcf86e460bd28
VERDICT: ACCEPT
