# MUSE-REPORT-1216: Exact review of candidate 1215 (W runs to GX refinement)

CANDIDATE: 1215 0f31f20a2c0682dd15ceb04a0709f87a74c244e7

## Scope and inputs

- Review lane. Added no Lean code and changed no existing file. Owned deliverable is this report only.
- Clone verified: `/home/simon/Dokumente/gabbro-muse/a1216`, branch `muse/1216`, clean tree at `cbc0afe0`.
- Candidate: lane 1215, pinned HEAD `0f31f20a2c0682dd15ceb04a0709f87a74c244e7` over base `988d75ef`
  (from `.tmp/review/SNAPSHOT.json`). Reviewed the exact snapshot diff (`PATCH.diff`, 428 lines),
  the snapshot file copy, `MUSE-REPORT-1215.md` and `BUILD-EVIDENCE.json`. The author clone was not
  accessible, so per the task ("Read the candidate diff only") no author-tree commands were run.
- Candidate diff content: new file `grammatik/Grammatik/X86/TsoGxRefine.lean` (319 lines),
  exactly one added `import Grammatik.X86.TsoGxRefine` line in `grammatik/Grammatik.lean`,
  plus `MUSE-REPORT-1215.md`. No other file touched.

## Checks performed (all against my own clone's accepted tree plus the snapshot)

1. Forbidden tokens: word-boundary grep for `sorry|admit|native_decide|unsafe|axiom|sorryAx` over the
   snapshot `TsoGxRefine.lean` returns no match (the only substring hits are prose "admitted").
2. Lifted, not copied: every heavy lemma the candidate leans on exists with a matching signature:
   `schwach_ist_gX` (`Speichermodell/AtomarW.lean:279`, premise order and conclusion identical to the
   candidate's application), `gx_aus_g` / `gx_aus_g_lauf` (`AtomarLauf.lean:67/75`),
   `brueckenLauf_erreichbar` (`X86/TsoRunInduction.lean:62`, same `leer`/`erweitern` induction shape
   the candidate mirrors), `neuestens_jüngste` (`X86/TSOHistory.lean:95`, 6-component split matching
   the candidate's destructure; both `simp [hsplit, hpre]` closures check out against list-append
   normal forms), `tsoRmw_puffer_bleibt_verweigert` (`X86/TsoRmwBridge.lean:218`, explicit
   `e rest` args matching the candidate's `_ _`), `schrittW_aus_gruppen_drain_zeuge`
   (`X86/CarrierTraceBridge.lean:832`, 23-hole existential matching the candidate's 23-name
   destructure exactly), `GeteiltV`/`GeteiltA` (`Zielsatz/Spec.lean:2100/2104`, so `h.1.1 :
   AtomarAusgenommen c` is well-typed), `HavocA` (`Speichermodell/AtomarSem.lean:49`, the
   `(hA X σ).2 c fun h => hT h.2` unpacking is exact), `RufSchrittW` as a 5-part existential
   (`Speichermodell/MaschineW.lean:194`), `SchrittW.schritt : RufSchrittG ... (mitSpeicher W.g σ)
   u M''` (same file:150/155, absorbed by the witness existential), `RufErreichbarGX.schritt`
   taking reachability before step (`AtomarLauf.lean:46`, matching `.schritt _ _ _ ih hGX`),
   all witness constants (`ctHw`, `ctBuf1_4`, `ct_stale0/1`, `ctFfresh`, `setTso_wf/ansicht`,
   `hwWitStart_wf`, `spurW_erreichbar/speicher`, `laengeOk` admitting 9 by `decide`).
3. Premise use: every theorem consumes all its premises (`hs`/`hr`/`h` drive the single-step,
   run and induction proofs; all eight DRF/checker premises feed `schwach_ist_gX`; `hFwd` drives
   the buffer split; `hA`/`hT` both used in the rely unpacking).
4. Witnesses: `gxSchrittAusG_zeuge` is non-degenerate (written table via `ctHw`, source step
   `0 → 42`, changed target bytes, two-core `spurW` memory change, owner-only forwarding
   divergence, refused LOCK context). `lockBeiWeiterleitungVerweigert_zeuge` is non-degenerate
   (two cores with divergent observations at `ctF`, pending foreign byte, refused LOCK XADD).
   Rule 13 does not mechanically demand more: lane 1215's task contains no `ZEUGE:` lines and no
   added theorem quantifies premises over `Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`
   (`FussSX` binds `f : D.Fn`; the rest bind threads, functions and carriers).
5. No weakened guarantees, no fake closure: the refinement theorems keep the DRF/checker premises
   (`GutO`, `AbgK`, `FussSX` over `GeteiltV`, `StartExklusiv`) explicit — the same conditional shape
   as the accepted `schwach_ist_gX` — and CUTS lists the exact open remainder (checker-side
   discharge, start-anchoring of the fragment head, `rmw`-field assembly, `valX86_sound`,
   scheduling/fairness, interrupts/devices). No hardware correspondence beyond self-consistency is
   claimed; no new silicon facts are introduced (length 9 flows from the accepted generic
   `laengeOk`; the LOCK refusal holds for any admitted length).
6. Build: `./lean-bau` on my clean tree ends `Build completed successfully (640 jobs).`
   The candidate's own green build and `#print axioms` (standard subset of
   `[propext, Classical.choice, Quot.sound]`, `gxLockLaenge` axiom-free) are author-supplied
   evidence in `BUILD-EVIDENCE.json`; I did not materialize the candidate, so the merge gate's
   rebuild plus `pruefe-kein-sorry.py` remain the mechanical confirmation.

## Observations (not verdict-blocking)

- `brueckenLaufGxGeteilt` and `geteiltVAtomar` carry `[DecidableEq D.Fn]`; harmless (instance, not a
  Prop premise, axiom-neutral), but a follow-up could check whether the instance is truly needed.
- No joint `_zeuge` exists for `brueckenLaufGx`/`brueckenLaufGxGeteilt`; the author reports this as
  an explicit finding with the precise reason (start-anchoring gap: `ctProg` returns immediately),
  not worked around. Agreed: this is honest incompleteness, and closing it is new work (a fragment
  body plus entry execution), not a repair of this candidate.
- The MECHANISM paragraph's `HwAdapter` demand is correctly identified as inapplicable (consumer is
  machine GX, same as lane 1187 for W); reusing accepted `tsoRmwAdapter` for the LOCK leg respects
  rule 16.

## Verdict

VERDICT: ACCEPT

The candidate proves what it claims and claims only what it proves: the unconditional GX embedding,
the conditional bridged step/run refinement over the admitted shared atomics with the DRF/checker
premises explicit, the rely-stability fact, and the LOCK/forwarding disjointness — all by lifting
accepted lemmas, with standard axioms, two non-degenerate witnesses, an honest CUTS block, and a
one-line footprint on existing files.
