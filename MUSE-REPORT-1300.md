# MUSE-REPORT-1300: Exact review of candidate 1299 (HwTranslate join)

Clone: /home/simon/Dokumente/gabbro-muse/a1300, branch muse/1300 (own files only: this report).
CANDIDATE: lane 1299, pinned head e2265f20b2d5bfa2c227ae022950970c0319292a, base 234f2728.
Delivered files reviewed in full: `.tmp/review/author-1299/PATCH.diff` (887 lines),
`grammatik/Grammatik/X86/HwTranslate.lean` (768 lines, read completely),
`OWNER-TASK.md`, `MUSE-REPORT-1299.md`, `BUILD-EVIDENCE.json` (15 completed steps).

## Checks performed

- **Scope**: PATCH touches exactly `MUSE-REPORT-1299.md` (new), `grammatik/Grammatik.lean`
  (one appended import line, applies cleanly after `HwMemTypesWC` at line 679 of my clone),
  `grammatik/Grammatik/X86/HwTranslate.lean` (new). No existing file edited or weakened.
- **Forbidden tokens**: grep for `\b(sorry|admit|native_decide|unsafe)\b` and `^axiom` over the
  candidate file: zero matches (the 15 `admit`-pattern hits are English "admits", not the tactic).
  No `split_ifs`/`norm_num`/`ring_nf` issues seen; tactics used are `simp`/`rw`/`decide`/`omega`/`cases`.
- **`#print axioms`**: present for every new definition/theorem (58 lines, 709-766). CUTS block present
  and honest: claims only the lifted join, refuses large pages / SMEP-SMAP / fault delivery,
  names silicon assumptions, claims no W/GX, no timing, no hardware correspondence.
- **Lift, not copy**: `walkLesen` instantiates `seitenGang` (HwPaging.lean:654) as the
  `SeitenDurchlauf` parameter of `tlbAufloesung`/`tlbAufloesung_trifft`/`tlbAufloesung_verfehlt`
  (HwSegTlb.lean:246/258/265); INVLPG/CR3/locality lift `tlbNachEntfernen_geht_durch`,
  `tlbCr3Spuelung_leert`, `tlbEntfernen_lokal`, `tlbEntfernen_sucht_verfehlt` (all verified present
  in my clone); flat bridge uses `FlachStimmt`, `gangOk_flach_lesbar/schreibbar` (HwPaging.lean);
  joint witness reuses `witTab`, `witSeitenSteuer`, `wit_lese_rw_ok`, `hwWitStart`/`hwWitStart_wf`,
  `hwWit_weiterleitung`/`hwWit_fremd_alt`/`hwWit_spuelung_aendert_speicher`,
  `hwWitLoadEigen`/`hwWitNachFlush` (all verified present). No accepted definition redefined.
- **Premise use**: every theorem's premises are consumed (spot-checked all sections; e.g. the write
  bridge carries both read-probe and write-walk premises into `uebersetze_frisch_ok` and
  `gangOk_flach_schreibbar`; `hwUebersetzSchritt_wf` cases consume the step and `hwf` per branch).
  No `intro _` / `have _ :=`; no `Prop`-typed premises; no conclusion restating a premise.
- **Stale exception (task core)**: proved as `uebersetze_stal_unabhaengig` (hit resolves identically
  under two table states) plus the §6 exhibit (`witUebersetz_veraltet` admits via stale entry while
  `witUebersetz_neu_pf`/`witUebersetz_walk_fehl` show the changed walk faults, and
  `witUebersetz_nach_invlpg_fehl` shows post-INVLPG fault). Matches the requested proof shape.
- **Witness**: mapping change in memory (`witUebersetzTab1` clears the RW leaf `16*512+1`),
  stale access (`witUebersetz_veraltet_schritt`, reached self-loop), INVLPG step with miss
  afterwards (`witUebersetz_invlpg_schritt`), faulting access, core locality pin, and the joint
  `hwUebersetz_zeuge` conjoining old-walk admission, changed-walk fault, stale admission,
  INVLPG re-fault (resolution + reached steps) with the accepted two-core memory-changing TSO run
  (drain 0 -> 42). Non-degenerate. The judgment call (memory-changing leg via the reused TSO run,
  since translation steps never touch `HwMaschine` memory) is explicitly stated and matches lane
  1283 precedent; the translation-side state change (cleared leaf, differing walk outcomes) is proved.
- **Silicon**: INVLPG page-granular, PCID-off CR3 flush, no globals via lane-1285 `tlbGlobal`;
  consistent with Intel SDM 325462-093US §§ cited. No silicon fact contradicted; no correspondence claimed.
- **Refusals really refuse**: large-page / control / GP outcomes invert to `¬ ...zugriffOk/pf` by
  equation rewriting; hit-vs-fresh and miss-vs-stale exclusions by miss/hit contradiction. Genuine.
- **Build evidence**: BUILD-EVIDENCE.json shows `lean-probe` 0 errors on the final file and
  `lean-bau` green (`Build completed successfully (677 jobs)`, axiom samples within
  `[propext, Quot.sound]`).

## Blocker (honest partial status)

`default.bash` is denied by the permission classifier in this session (one attempt rejected), so
`./lean-probe` (copy-into-clone + probe) and `./lean-bau` could not be re-run here. Build
verification therefore relies on the author's recorded evidence above, plus complete static review
of all 768 candidate lines. No content concern was found that would require a re-run to resolve.

## VERDICT: ACCEPT

Candidate 1299 meets its task with no weakened guarantee and no fake closure. Merge-eligible as far
as this review can determine; merger still runs the standard gates (build, axioms, probes, keys).
