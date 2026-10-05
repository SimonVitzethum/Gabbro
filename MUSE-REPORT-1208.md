# MUSE-REPORT-1208: Exact review of author lane 1207 (HwDrainGeneric) — NEW pinned snapshot

CANDIDATE: 1207 fa8d003107bb1ea5b663286f041963caef5e067d
VERDICT: ACCEPT

## Assignment and scope

Lane 1208: independent exact review of lane 1207 ("Generic drain-equals-write64 induction",
NEW FILE `grammatik/Grammatik/X86/HwDrainGeneric.lean`). Own only `MUSE-REPORT-1208.md`.
This supersedes my stale blocked review of the previous pin (`b903e3cf`, dispatch-side
REPAIR: no reviewable diff). The new pin (`fa8d0031`) ships full in-clone evidence
(`.tmp/review/author-1207/`: PATCH.diff, both Lean files, author report, owner task,
build evidence), so a substantive review was performed. The two pins differ only by the
author report (build evidence shows the last commit adds `MUSE-REPORT-1207.md` only, no
Lean change, over the bau-green `b903e3cf` tree), so the Lean content under review is the
fully verified one. Nothing stale is approved: every check below is against the new pin.

## Pinned snapshot (from `.tmp/review/SNAPSHOT.json`, read inside my clone)

- author: 1207
- head: `fa8d003107bb1ea5b663286f041963caef5e067d`
- base: `4ed3590d85cf770cb098132aed8ee9752e29e013`
- files: `MUSE-REPORT-1207.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/HwDrainGeneric.lean`
- clean: true

## Evidence inspected

1. `PATCH.diff` (1185 lines): exactly the 3 snapshot files. `Grammatik.lean` hunk is one
   appended import line (`import Grammatik.X86.HwDrainGeneric` after `PipelineLinkMulti`,
   end of file at base). New file 1021 lines. Report 143 lines.
2. `grammatik/Grammatik/X86/HwDrainGeneric.lean`: read in full (lines 1–1021).
3. `MUSE-REPORT-1207.md` (author report) and `BUILD-EVIDENCE.json` (probe/bau command log).
4. Context in my clone: `TSO.lean`, `WordAccessGrouping.lean`, `HardwareExecution.lean`
   (adapter pattern), `HwStackCalls.lean`, `HwForwardingGeneric.lean`, `Speicher.lean`,
   and my `Grammatik.lean` tail.

## Checklist findings

- Bans: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file (grep over the
  evidence dir hits only the English word "admits" in comments and quoted task text).
  No `split_ifs`/`norm_num`/`ring_nf`. Intermediate broken states in the build log (one
  transient `sorryAx` on the way) are not in the pinned file.
- Axioms: final probe dumps every main theorem at `[propext]` or `[propext, Quot.sound]`,
  joint `drainGeneric_zeuge` at `[propext, Classical.choice, Quot.sound]` — standard set.
  `DrainEreignis` depends on no axioms. `#print axioms` per main theorem present.
- Existing files: untouched except the single appended import line. No weakened theorem
  (nothing existing edited).
- Lifted, not copied: the adapter is built from accepted `hwWortAusgabe`, `flushKern`,
  `issueByte`, `stapelLadeWort`, `setTso`; every agreement/refusal/prefix theorem cites
  accepted lemmas (`hwWortAusgabe_puffer`, `setTso_wf`, `flush_leer`, `issue_verweigert`,
  `issueListe_cons_none`, `stapelPop_unlesbar`, `flush_entfernt_kopf`, `flush_rahmen`,
  `flush_anderer_kern`, `issue_anderer_kern`, `issue_kein_speicher`, `drain_installiert_aux`,
  `wortEintraege_kopf`, `addrOff_ne8`, `fuss_mem_offset`, `wortEintraege_laenge`,
  `writeBytesN_hit`, `wort_gruppe_liest_zurueck`, `fwd_wortByte_bytesWort3`, the accepted
  603 drain `grpS2..grpS10` with `grp_hgrp/grp_spur/grp_hend/grp_hempty/grp_hstoer/grp_hles`).
  I verified each of these names exists in the accepted modules in my clone. No accepted
  definition is redefined; the new names are all fresh (`DrainEreignis`, `drainAdapter`,
  `drain*`, `ov*`, `drainWit*`, `drainGrp*`).
- Premise use: read every theorem; all premises feed the proof (adapter cases rewrite the
  step hypothesis; `hgrp`/`hspur`/`hstoer`/`hend`/`hleer` all feed the prefix induction;
  `hles` feeds the accepted read-back; `hwr` feeds the store equation; the joint witness
  is one exact tuple over jointly proved facts). No `intro _` / `have _ :=`.
- Refusals genuine: guard-store, dark-observation and empty-drain refusals are `= none`
  facts over concrete fixtures, proved through the generic refusal theorems (not asserted).
- Witness non-degenerate: two cores (core 0 stores/forwards 42, core 1 reads old 0 then
  new 42), 8-entry buffer fact, memory-changing run (address byte 0 at start by
  `drainWit_anfang_null`, 42 after drain observed from both cores), owner-only forwarding
  pair, adapter drain step 8→7, generic footprint/`write64` fires plus mid-trace prefix,
  beside the three refusals and the overlap break. All premises joined in
  `drainGeneric_zeuge`.
- Negative genuine: `ov_flush` by `rfl` computation, exclusion failure proved,
  footprint/read-back breaks proved (`decide` on concrete bytes: footprint byte three 7
  vs `write64` 5).
- Scope honesty: the author proves the footprint-scoped equation (not whole-memory
  equality, which is false under disjoint foreign flushes) and documents exactly this in
  the file CUTS and the report task critique. No silicon correspondence is claimed (CUTS:
  no SDM extracts consulted in the lane, ordering facts reused from accepted modules, no
  silicon proof) and no W/GX bridge is claimed. No statement outruns its proof.
- Build: author evidence ends with full `./lean-bau` green on the content-identical tree
  (`Built Grammatik (2.0s)`, `Build completed successfully (627 jobs)`); earlier
  identical failures were thread-creation resource aborts (`failed to create thread`,
  exit 134), plausibly apparatus, and probe was 0-error throughout. The pin delta is
  report-only, so the pinned Lean content is the verified one.
- Previous findings: my only prior finding was dispatch-side (unreachable diff); cured by
  this evidence drop. No author-side repair was or is required.

## Observations (not verdict-changing)

- Probe still prints linter warnings naming the `hstoer`/`hbuf` binders of
  `drainUninstalliert_bleibt_aux` as unreferenced; both are semantically used (exclusion
  threading, buffer-shape rewrites). Cosmetic.
- `drainZwischen_praefix` destructures the group as `⟨hbufl, _hff⟩`, ignoring the second
  conjunct; the exclusion half arrives via the trace hypothesis instead. Legitimate, noted.
- CUTS honestly records scope overlap with the 603 `verflochten_*` wrappers (citation,
  no duplication).
- Integration note for the coordinator: master moved past the base (my `Grammatik.lean`
  now ends at `HwNestedInterrupts`, 637 lines); at merge the import must be re-appended
  at the new file end (mechanical union, no semantic conflict).

## New definitions/theorems (mine)

None. Report-only review lane; I added no Lean code.

## `./lean-bau` last result line (my tree, unchanged tracked sources besides this report)

`Build completed successfully (634 jobs).`
