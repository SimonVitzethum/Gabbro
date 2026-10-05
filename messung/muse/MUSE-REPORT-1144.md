# MUSE-REPORT-1144: TSO to W bridge fragment READS — independent exact review

CANDIDATE: 1143 11b769097b2ac4011122b14ac07de2c404c0ab75
VERDICT: ACCEPT

Lane 1144. Report-only exact review of lane 1143 (TSO to W bridge: fragment READS).
Owned file only: this report. No Lean source changes made.

## Review basis (no stale snapshot)

- Pinned snapshot `.tmp/review/SNAPSHOT.json` (read in-clone): lane 1143 at full HEAD
  `11b769097b2ac4011122b14ac07de2c404c0ab75`, base
  `48a4be7c1c333a602ce0d0816979d154ae1bd959`, files `MUSE-REPORT-1143.md`,
  `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/TsoReadBridge.lean`.
- Reviewed content: the full candidate diff and file copies under
  `.tmp/review/author-1143/` (`PATCH.diff`, 1691-line new file read in full;
  `MUSE-REPORT-1143.md`; `OWNER-TASK.md`; `BUILD-EVIDENCE.json`) — i.e. exactly the
  newly pinned material, not the earlier round.
- Delta analysis: the newly pinned HEAD is a report-only commit on top of `115b285c`
  (`Lane 1143: report review response`, confirmed by the build-evidence log tail);
  the Lean source is unchanged from the source built green there. The previous review
  round recorded a procedural non-acceptance because no candidate content was
  accessible; that blocker is lifted by the in-clone evidence, and every prior
  finding is superseded by the substantive checks below. Nothing from the old round
  carries over as an open defect.
- Honest limitation: the candidate was not rebuilt in this clone. Applying its patch
  here would modify `grammatik/` files outside the owned report file, which the lane
  ownership forbids. The verdict rests on a complete static review of the full
  candidate content plus the author's per-step probe logs (final 0-error probes for
  every piece, full `./lean-bau` green at 601 jobs on the identical source).

## Checks performed and outcome

1. Files touched: exactly the three owned files. `Grammatik.lean` gains one import
   line (`import Grammatik.X86.TsoReadBridge`); no existing file is otherwise edited
   and no existing theorem is touched. New file is purely additive.
2. Forbidden tokens: own grep over the candidate source copy for `sorry`, `admit`,
   `axiom` declarations, `native_decide`, `unsafe`, `sorryAx`, `intro _`,
   `have _ :=`, `split_ifs`, `norm_num`, `ring_nf` — zero matches. (The remaining
   `sorry` strings in the evidence directory are prose in the author report and
   intermediate red-probe excerpts in the build log, all resolved before the final
   green probes.)
3. Axioms: the file ends with `#print axioms` for all 11 main theorems
   (`hwLade_erhaelt_wf`, `hwLade_trifft_speicher`, `beitrag_tabelle_le`,
   `lesespur_assignSlot`, both `schrittW_aus_lesefragment_*`, both `*_kein_globaler_wert`,
   all three `*_zeuge`). Final probe logs show at most `propext, Classical.choice,
   Quot.sound` — the standard set, no `sorryAx`.
4. Evaluator lifted, not copied: the proofs apply accepted lemmas
   (`hwSchritt_wf`, `load_ohne_eintrag`, `rep_schritt_bleibt`, `blattFragment_voll`,
   `wLesbar_aus_gruppe`, `wLesbar_aus_weiterleitung`, `wort_gruppe_liest_zurueck`,
   `gruppenwert_rep`, `zahlWort_wortZahl`, `ereignisse_eq`, `RufSchrittG.blatt`,
   `SpurSchritt.flush`, `spurStart_inv`, `spurSchritt_inv`, `erbtW_start`,
   `fremdFrei_aus_leer`, `eigen_fremd_gleich`, `gruppe_reisst_fremd`,
   `traegerGleich_refl`, …) and redefine none of them. New definitions are witness
   vocabulary only (`rdSig`, `rdD`, `rdV`, `rdO`, `rdI`, `rdE`, `rdSigma`, `rdSL`,
   `rdA2`, `rdZero`, `rdNine`, `rdM9`/`rdM9'`, `rdS2`–`rdS11`, `rdSF`, `rdF8`,
   `rdW1`, `rdNA10`, `rdNB11`, `rdProg`, `rdS`, `rdRest`, `rdRahmen`, `rdFaden`,
   `rdMachine`). No model is duplicated.
5. Every premise used: traced all premises of both main theorems to their uses in
   the proofs (including `hNe` via the zero-contribution lemma, `hTraegerR`/`hWert`
   via the value links, `hInvN`/`hErbt` via the freshness bounds, `hs`/`hhead` via
   the leaf step and the no-start case split). Minor observation, not blocking: a
   local helper `hExec0` is proved but never referenced afterwards in either main
   proof (dead local, not a discarded premise — every theorem premise itself is used).
6. Planted refusals really refuse: `stale_kein_globaler_wert` exhibits concrete
   accepted state `sbNach2`/`sbY` where two cores load different bytes, and
   `gruppe_kein_globaler_wert` exhibits torn-assembly divergence at `hS3`, both
   closed by `decide`. The stale case is stated honestly with no global value
   claimed.
7. Witness non-degenerate: two-table declaration `rdD` whose contract writes both
   tables; a reached one-step copy run changing the source slot `9 → 0`
   (`rd_hExecFull`, `rd_hBefore`, post-step fact) and the target bytes
   (`rd_hBytes`: nine-word to zero-word); an eight-flush drain with a real foreign
   issue on core 1 (`rdS4`, `rdBuf1_4`) and cross-core stale divergence beside it.
   All three joint witnesses (`schrittW_aus_lesefragment_gruppe_zeuge`,
   `schrittW_aus_lesefragment_weiterleitung_zeuge`, `lesespur_assignSlot_zeuge`)
   apply the main theorems to fully concrete joint instantiations.
8. Silicon: no new hardware definitions, encodings, fault classes, or timing
   claims anywhere in the file; machine observations reuse the accepted
   `HwSchritt.lade`. There is nothing new to check against the SDM extracts.
9. CUTS honest, claim matches proof: the CUTS block states exactly what is proved
   and leaves OPEN the full 9-step projected trace (only the last flush is a real
   projected step at the clock-2 node), the forwarded value link and reading-W
   shape as lowering-certificate premises, mixed footprints (tearing refusal), run
   induction to W runs, GX refinement, and validator soundness. No
   hardware-correspondence and no W/GX closing claim is made.
10. Task-shape note: the owner task's MECHANISM paragraph suggested an `HwAdapter`;
    the author proved the BRIDGE paragraph instead (the actual OPEN leg) with a
    recorded reason, connecting to the coherent machine only where real
    (`HwSchritt.lade` observations). The reviewer criteria require the accepted
    evaluator lifted — satisfied — and no adapter. Acceptable as disclosed.
- Own-clone `./lean-bau` (baseline, no candidate files here): `Build completed
  successfully (606 jobs)`, first line `== exit 0; 0 error line(s) in the COMPLETE
  output`. Author-clone full build per evidence: 601 jobs green on this source.

## What remains open

- Nothing from this review: the candidate is accepted as reviewed. The OPEN items
  are the author's own CUTS (projected-trace completion, run induction, GX, validator
  soundness), owned by future lanes, not by this review.

## Definitions/theorems added by this lane

None. No Lean files created or modified; only this report.

CUTS: candidate content fully reviewed at the newly pinned HEAD; no independent
candidate rebuild possible under lane ownership (stated above); baseline
`./lean-bau` green (606 jobs, exit 0).
