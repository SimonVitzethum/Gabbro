# MUSE-REPORT-733: Exact review of lane 732 hardware-integration coverage organisation

CANDIDATE: 732 44ef732ab16cf3a4d50f0223ca66c26a0fd0b567
VERDICT: ACCEPT

Clone: `/home/simon/Dokumente/gabbro-muse/a733`, branch `muse/733` (verified
before work). Owns only this report. No other file touched; working tree was
clean before this report and contains only it now.

## Scope of review

- Owner task (`lanes/732.md` in this clone) matches the snapshot
  `.tmp/review/OWNER-TASK.md` line for line (task section identical).
- Snapshot pins author 732 HEAD `44ef732a`, base `9fc15bf4`, files
  `MUSE-REPORT-732.md` + `dokumente/x86/HARDWARE-INTEGRATION-COVERAGE.md`,
  clean tree. The base commit exists in this clone and is an ancestor of this
  clone's HEAD `587ed8d9`.
- `PATCH.diff` (497 lines) contains exactly two new files, both owned. No
  Lean, Rust, registry (`DIRECT-COMPILER.md`), lane-prompt, or root/private
  file is touched. The deliverable is organisation-only, as tasked.

## Independent verification (all against this clone's accepted tree)

- Common architecture (§1): `HardwareExecution.lean` is 902 lines;
  `HwSchritt` cases `reg/lade/gibAus/spuele/fehler` at :173-190 with `reg`
  stepping via `stepExt` over `ExtInstr` (:174-175); projection agreement
  theorems at :63-79; `hwWf_aus_zugelassen`; adapters `adapterLocked662`,
  `adapterInteger666`, `adapterFp668`, `adapterFault670`,
  `adapterInterrupt672` over exactly the old vocabularies claimed
  (`SperrBefehl`, `ExtInstr`, `FpDecodiert`, `MulDivDecodiert`, `Unit`) —
  two register-path plugs, three explicit refusals. Accurate.
- Producer rows: `IntHwOp` :24, `intHwWert` :33, `intHwFlagsLogik` :58,
  `inthw_logik_af_none` :68, `inthw_b64_agrees` :73, `inthw_b32_clears`
  :103, 1544 lines — all exact. `vecShlQ_satt_vs_maske` at :226 — exact,
  and the saturate-vs-mask divergence is real. `cas_fehlschlag_stottert`
  exists in `LockedOps.lean` (:249) with the failure-stutter reading the
  document gives. `osXmm : Bool` in `FeatureProfile.lean` (:46, inside the
  cited :42-63). `af : Option Bool` in `Typen.lean` (:30). `hwWortAusgabe`
  exists with buffer-only grouping. `s32Rechne` :168, witnesses :185-231,
  1853 lines, CUTS :1805 — exact.
- Consumer-gap claims reproduced verbatim from committed prompts:
  `lanes/724.md` defers "future binary32/SSE integer/AVX producers plug in
  later" (F-B32/F-VEC gap is real); `lanes/718.md` carries "No second
  competing executor" plus the proved-obstruction/discriminator duty.
- Registry states (§3) match the recorded baseline exactly: at `9fc15bf4`,
  672 is committed-candidate/review-pending, 704 is committed-candidate on
  both sides, 690/708 wait on dependencies, 696/698 are agent-working, and
  733 is "scheduled". (This clone's newer HEAD has since added a
  gate-rejected qualifier to 704 and moved 690 to "Prepared" — registry
  drift after the author's baseline, not a candidate defect; noted for the
  coordinator only.)
- "Eight decoder families" (§6.1) is defensible: of the nine modules named
  in `lanes/718.md`, eight own or reuse a byte decoder
  (`ArchitecturalFlags` holds flag identities only, no decoder).
- Manual provenance: `.tmp/` is gitignored (`.gitignore` line 62), this
  clone's `.tmp/` holds no `HARDWARE-REFERENCES`, and accepted module
  headers (e.g. `MulDivWidthHardwareForms.lean`) cite the clone-local
  snapshot path — the document's "provenance lives in producer reports and
  module CUTS, not re-asserted here" is corroborated, and no manual fact is
  re-asserted or silicon claim made.
- Negative checks: no `sorry/admit/axiom/native_decide` surface (no Lean);
  no percentages or counts presented as effort coverage (`grep %` empty;
  line/theorem counts are explicitly disclaimed as locating evidence only);
  no completion or source-to-final-bytes closure claimed (CUTS block states
  6B remains OPEN and mandatory); English throughout; producer ACCEPTs
  explicitly limited to exact delivered claims; no second interpreter
  invented; no guarantee weakened.

## Findings requiring repair

None. Two non-blocking observations for the coordinator: (a) the registry
drift on 704/690 noted above — a future touch-up may re-date §3, but the
document pins its baseline hash explicitly, so it is not stale by its own
terms; (b) `HwAdapter` line range reads `:815-854` while the adapter defs
sit at :829-854 (structure opens just above) — harmless looseness.

## Build evidence

`./lean-bau` not run: the candidate adds zero Lean/Rust files (verified via
the PATCH file list), so no build, axiom, test, emission, or key-scan state
can change through it. The serial integration gate rebuilds before any
merge regardless. No suspicious Lean case existed to reproduce.

## What remains open (not this lane's)

F-B32/F-VEC/F-AF/F-DEV/F-RET/F-AVX/F-6B are proposals with dependency
gates, correctly stated as unscheduled. Full typed-carrier TSO bridge and
source-to-final-bytes validation remain OPEN per the document's own CUTS.
