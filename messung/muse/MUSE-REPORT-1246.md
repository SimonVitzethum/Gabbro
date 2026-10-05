# MUSE-REPORT-1246: exact review of author lane 1245 (pinned snapshot)

CANDIDATE: 1245 e233908cf810de1b3e04234d764e00578c7e3d0c

VERDICT: ACCEPT

Lane 1246. Clone /home/simon/Dokumente/gabbro-muse/a1246, branch
muse/1246 (verified; matches the lane file, so no STOP). Owned file:
only MUSE-REPORT-1246.md. No Lean files created or edited; no existing
files modified.

## What was reviewed

The coordinator-pinned snapshot `.tmp/review/SNAPSHOT.json` (author
1245, head e233908cf810de1b3e04234d764e00578c7e3d0c, base
ca33ef1b3eaa30c178343517c9fd20f32a914b58, clean true) with the in-clone
snapshot directory `.tmp/review/author-1245/` (`PATCH.diff`,
`MUSE-REPORT-1245.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`, and the
post-image `grammatik/` files). The lane file itself carries only a
placeholder where the pinned HEAD belongs; the snapshot file is the
pin. The author clone was never touched (rule 1). The final commit in
`BUILD-EVIDENCE.json` (e233908c) matches the pinned HEAD prefix, and
its base matches the snapshot base.

`PATCH.diff` scope (complete, 3 paths, nothing else): new
`MUSE-REPORT-1245.md`, one appended line
`import Grammatik.X86.TsoAddressCarrier` at the end of
`grammatik/Grammatik.lean`, and the new 428-line module
`grammatik/Grammatik/X86/TsoAddressCarrier.lean`. I read the full new
module (both halves), the author report, the owner task, the complete
build evidence, and the diff hunks.

## Checks against the review checklist

1. Banned tactics: grepped the snapshot module for sorry, admit,
   axiom declarations, native_decide, unsafe, sorryAx, split_ifs,
   norm_num, ring_nf. Clean. The only `axiom` substring hits are the
   required `#print axioms` lines. No `sorry`-shaped warning can hide:
   the independent probe below is error-free and the merge gate runs
   its own sorry scanner.
2. Axioms: independently reproduced with `./lean-probe` on the
   snapshot file in this clone (see below). Every theorem is within
   propext, Classical.choice, Quot.sound. The bridge specialisation
   and the joint witness inherit Classical.choice from the accepted
   bridge; everything else is propext with Quot.sound where
   quotient-based address reasoning is used.
3. Existing files: untouched except the single ordered import line
   (diff hunk `@@ -642,3 +642,4 @@`, one added line). No weakening
   or deletion anywhere.
4. Premises used: checked theorem by theorem while reading.
   `kartiert_sep` uses hsep, h1, h2, w1, w2. `kartiert_injektiv`
   uses hsep, h1, h2, w. `platzOk_rep` uses h, hp, htr (all three key
   components through `trifft_inv` and subst). `zugelassen_schranke`
   uses h and hloc. `kartiert_von_erst` derives both conjuncts from
   hfirst. The bridge specialisation threads every premise into the
   applied accepted theorem; the `obtain` triple keeps the needed
   `repOk` arm and the unused arms are derived facts about the
   placement memory, not discarded premises.
5. Lifted, not copied: the module imports `PipelineImage` and
   `CarrierTraceBridge` and reuses them unchanged (`layoutVon`,
   `sepB`, `sepB_sound`, `layoutVon_loc`, `trifft_inv`, `platzOkB`,
   `LayoutSep`, `repOk_int`, `natAdresse_ohneUmbruch`, `Disjunkt`,
   `disjunkt_von_intervallen`, `natAdresse`, `RepSlot`, `zahlWort`,
   `wortZahl`, `schrittW_aus_gruppen_drain` and its full witness
   vocabulary). I spot-checked each name against this clone's
   accepted tree; all resolve to accepted definitions. The only new
   definitions are `kartiert` and `psWit`. Nothing is redefined.
6. Refusals: `leer_ohne_kartierung` (no slot maps over the empty
   placement) and `platz_ueberlapp_verweigert` (placements at 4096
   and 4100 refused by decided `sepB`) are genuine: a proved
   negation and a decided computation over two distinct witness
   rows, both kernel-checked.
7. Witness: `schrittW_aus_gruppen_drain_platziert_zeuge` joins all
   premises on concrete values. Non-degenerate: one-table `witD`
   that the witness function writes (`ctHw`), a reached run with
   source slot 0 -> 42, observably changed target bytes at placed
   address 4096 (`hBytes`, decided), the installing `write64` step,
   decided admission and layout facts, and the specialised bridge
   conclusion (`SchrittW`, value agreement, `RepSlot`). The generic
   two-core adapter boilerplate does not apply here: the owner task
   (authoritative over the context boilerplate, as the author also
   notes) asks for a witness on a placed table that a function
   writes, and the specialisation inherits the accepted bridge's
   shape unchanged.
8. Silicon: no new hardware claim. The header and CUTS state byte
   facts reuse the accepted `Speicher`, `SourceMemory` and
   `PipelineImage` definitions with no new silicon provenance.
9. CUTS and claims: the CUTS block plus `#print axioms` for every
   main theorem close the file. No hardware correspondence and no
   W/GX claim is made. The report's FINDING section names exactly
   what still needs placing (committed-read bridge, forwarded-read
   bridge, run induction, the RMW timestamp leg, globals), as the
   task orders. The claim is not larger than the proof.

## Independent reproduction (this clone, newer tree)

`./lean-probe .tmp/review/author-1245/grammatik/Grammatik/X86/TsoAddressCarrier.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`, with the full
`#print axioms` list matching the author's evidence axiom for axiom
(all within the standard set). This also shows no accepted-tree
drift breaks the candidate.

Own `./lean-bau` baseline (branch muse/1246, without the candidate
applied): `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (651 jobs)`. Author evidence for the
candidate tree: exit 0, 642 jobs.

## Nits (not affecting the outcome)

- The author report says 429 lines; the module has 428.
- `kartiert_sep` / `kartiert_injektiv` take `sepB` plus explicit
  no-wrap bounds rather than `platzOkB` admission directly;
  `zugelassen_schranke` composes admission into the bound, which
  closes the gap to the asked "injective on admitted placements".
- `BUILD-EVIDENCE.json` shows red intermediate probes during
  construction; the final probe and build are green. That is the
  documented small-pieces workflow, not a defect.

## Outcome history note

The earlier committed report of this lane recorded REPAIR for a
purely procedural reason (no pinned HEAD supplied, snapshot not yet
present, nothing reviewed). The pinned snapshot has since been
supplied in-clone and the exact review above is complete on the
merits; this ACCEPT supersedes that placeholder. Nothing was
reworded to pass formatting: the findings and the outcome come
from the evidence listed above.

## Lean names added by lane 1246

None. Review-only lane; no definitions, theorems, or witnesses added.
