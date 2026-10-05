# MUSE-REPORT-1312: exact review of candidate 1311 (second capstone union)

## VERDICT: ACCEPT

CANDIDATE: 1311 `984842f1f63dde5fc81d65e9054430405f5a3a0d`
(base `f92c2649c25c822f0ff7791f82dfecad9c7d4c31`).
Files: `MUSE-REPORT-1311.md`, `grammatik/Grammatik.lean` (one import
line), `grammatik/Grammatik/X86/HwKapsteinZwei.lean` (new, 852 lines).

## What was checked

Clone `/home/simon/Dokumente/gabbro-muse/a1312`, branch `muse/1312`
verified. Pinned author hash never touched (no `git show/log/diff` on
it); review worked from the delivered FILES
(`.tmp/review/SNAPSHOT.json`, `.tmp/review/author-1311/PATCH.diff`,
mirrored paths, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`).

- Scope: PATCH touches exactly the 3 listed files; the only existing
  file change is `+import Grammatik.X86.HwKapsteinZwei` in
  `grammatik/Grammatik.lean`. No reserved numbers taken (no N codes,
  gifts, examples) — correct, no new refusal is minted.
- Banned tokens over the candidate file: no `sorry`, no `admit`
  tactic (the 4 `admit` hits are English "admit no/nothing" in
  comments), no `axiom` declaration, no `native_decide`, `sorryAx`,
  `unsafe`, `split_ifs`, `norm_num`, `ring_nf`.
- Independent `./lean-probe` on the delivered candidate file in this
  clone (no copy needed; imports resolve via the project LEAN_PATH):
  `== 0 error(s) in the COMPLETE output; exit 0`. So the candidate
  elaborates against this clone's (newer) family APIs, not just the
  author's base.
- `#print axioms` (independent probe output, all 37 prints):
  every theorem in `[propext, Quot.sound]` or fewer
  (`kap2_tags_disjoint`, `kap2_verweigert` axiom-free). Standard.
- `./lean-bau` on the clean base in this clone:
  `Build completed successfully (693 jobs)` (base moved past the
  author's 688; candidate was probed standalone, full integration
  build stays with the merge gate).
- Lifted, not copied: the file defines no family vocabulary
  (no `def`/`abbrev` of any adapter, evaluator, event or witness
  name); new are only `Kap2Ereignis`, `HwVollSchritt2`, `kap2Tag`
  plus theorems. All 15 family modules exist in this clone and every
  cited lemma name resolves here (`adapterRot_wf`,
  `adapterCarry_wf`, `adapterBitTest_wf`, `adapterBitScan_wf`,
  `fpStoreAdapter_wf`, `adapterPf_wf`, `ctxSchritt_wf`,
  `adapterWc1287_wf`, `hwAvx2Schritt_wf`, `adapterAvx2Tor_wf`,
  `kap_wf`, `kap_basis_embedded`, `carryWit_add_rax`,
  `rotHw_rol_rax`, `bsHw_bsf_rax`, `ctxWit_buf`,
  `fp32Wit_weiterleitung`, `fp32Wit_aendert`, `hwWitStart_wf`,
  `avxWit_eigen`, …).
- Exact embedding: `kap2_alt_embedded` + 13 per-family iffs, each
  both directions by constructor/inversion (read). No new behaviour
  behind any tag. The three paging iffs are vacuous through the
  accepted refusals — stated exactly, not dropped.
- `kap2_wf`: every arm via its accepted preservation lemma; the
  AVX2-gate helper `kap2_adapterAvx2Tor_wf` discharges the gate
  premise by open/closed split with `adapterAvx2Tor_verweigert`.
  Every premise is used; no `intro _` / unused hypothesis.
- Refusals really refuse: `kap2_verweigert` cites
  `adapterSeiten_verweigert`, `adapterGross_verweigert`,
  `adapterUebersetz_verweigert`, each verified in this tree as
  `….schritt m c q = none` proved by `rfl`.
- Witness non-degenerate: `kap2_zeuge` joins 15 reached union steps
  (10 flat-family steps through their own adapters/relations, 5
  boundary base observations via `.alt`), the paging refusal,
  two-core value pins (carry core 0 = 22 / core 1 = 12, context
  260 / 260), owner-only forwarding
  (`fp32Wit_weiterleitung`, eigen `0x40` vs fremd `0`) with a
  memory-changing drain (`fp32Wit_aendert`: `mem.bytes … ≠`), and
  `HwWf` of every witness machine. Memory change + two cores where
  the family touches memory: satisfied.
- Silicon / vendor neutrality: no new semantics, evaluator, encoding
  or timing fact is defined; all values flow from the families' own
  witnesses. Nothing new to check against the SDM extracts; no AMD
  provenance claimed. No hardware-correspondence or W/GX claim is
  made — CUTS explicitly disclaims both.
- CUTS honest: proved part (union shape, 14 exact embeddings, `HwWf`
  preservation, disjointness, refusals, joint witness) vs open part
  (walk/fault legs, segment/TLB beyond observation, YMM legs,
  decoder priority, HW correspondence, W/GX bridge). Claim is not
  larger than the proof.
- Finding accepted as task-sanctioned: `Avx2Ops` contributes no arm
  (pure 256-bit evaluators, no `HwAdapter`/`HwSchritt` embedding in
  its file by design); coverage rides `Avx2Join`/`Avx2State`/`Avx2Mem`.
  Observation (not a defect): `kap2_step_seiten` and
  `kap2_step_gross` prove letter-identical propositions on
  `hwWitStart`; the report/CUTS openly state the three paging
  boundary steps share one machine and one observation.

## No REPAIR reasons found

No unsupported desired-correctness premise, no weakened guarantee,
no fake closure, no duplicated model, no pinned undefined behaviour.

## Process note

One `cp` + probe attempt was refused by the tool permission gate;
retrying `./lean-probe` directly on the delivered path worked with
0 errors, so no clone copy was needed and the tree was never dirtied
— this commit owns only `MUSE-REPORT-1312.md`.
