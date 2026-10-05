# MUSE-REPORT-1212: exact review of candidate 1211 (FP s32/MXCSR dispatcher)

Lane 1212, report-only independent exact review. Clone
`/home/simon/Dokumente/gabbro-muse/a1212`, branch `muse/1212` verified
(`.git/HEAD` = `refs/heads/muse/1212`; working tree `git status` clean).
Owned file only: `MUSE-REPORT-1212.md`.

CANDIDATE: 1211, pinned HEAD `fe97f2a15d3f0061cfe0d3deac836c62176b0d37`
(base `988d75ef`), reviewed from the exact snapshot in
`.tmp/review/author-1211/` (`PATCH.diff`, 1411 lines; file snapshot;
`BUILD-EVIDENCE.json`). The author clone `a1211` is outside this lane's
allowed directory, so the pinned snapshot is the review basis; it lists
exactly three files, `clean: true`.

## VERDICT: ACCEPT

## What was checked

1. **Scope.** The diff touches exactly three files: new
   `grammatik/Grammatik/X86/HwFpDispatch.lean` (1307 lines),
   `grammatik/Grammatik.lean` (one appended
   `import Grammatik.X86.HwFpDispatch` line at the end, nothing else),
   new `MUSE-REPORT-1211.md`. No existing theorem edited, weakened, or
   deleted. The diff tail was read to its end; no hidden hunks.
2. **Banned tokens.** Replicated the scan myself on the snapshot file:
   13 matches, all the English words "admitted/admits" in comments. No
   `sorry`, `admit`, `axiom` declaration, `native_decide`, `sorryAx`,
   or `unsafe`.
3. **Axioms.** Per the author's evidence log, every `#print axioms`
   line (15 prints, one per main theorem) is a subset of `propext`,
   `Classical.choice`, `Quot.sound` — the standard set. Nothing else.
4. **Premise use.** Audited every theorem while reading all 1307
   lines: each hypothesis is consumed by `rw`, `simp`, `exact`, or
   `cases`. No `intro _` / `have _ :=` discard, no conclusion restating
   a premise, no contract quantification (no contracts involved).
   Note (not a violation): in `fpDispSchritt_wf` the `cases h`
   binders (`hfetch`/`hstep`/`hmem`) are unused in the branch bodies —
   semantically correct because `HwWf` preservation does not depend on
   step details, and the evidence `h` itself is consumed by the case
   split.
5. **Lifted, not copied.** Grep over the new file confirms no
   redefinition of `s32Schritt`, `mxcsrSchritt`, `s32Decode`,
   `mxcsrDecode`, `fpHwCvttZugelassen`, `stepExt`, `decodeExt`, or
   `FpCtrlSchritt`. Every cited family lemma
   (`s32Schritt_addssRR`, `s32_eins_plus_zwei`, `mxcsrSchritt_ld_erfolg`,
   `mxcsrSchritt_gesperrt_ud`, `s32Roundtrip_addssRR`,
   `mxcsrRoundtrip_ld/st`, `fpCtrlAusgabe32_*`,
   `pin_ext_fp_movsd`, `pin_ext_nichts_leer`, `setKernDaten_wf`,
   `setTso_wf`, `load_verweigert`, `issue_verweigert`, …) was verified
   to exist in this clone's base tree. The gate is re-proved as
   required: `fpDispGate_cvtt_gleichung` is `rfl` from the gate
   definition, NaN refusal and `42.0` admission unfold it and cite only
   the value-level `cvttHwGueltig_nan`/`cvttHwGueltig_42` — no family
   gate theorem is cited.
6. **Disjointness.** Closed-chain `decide` pins in every direction
   (unified refuses s32/LDMXCSR/STMXCSR rows; the new decoders refuse
   each other and the old DOUBLE row; the old row stays unified via
   cited `pin_ext_fp_movsd`; each new row taken in its own arm). No
   overlap found; the author's "no FINDING" statement is accurate.
7. **Refusals really refuse.** Each refusal theorem rewrites with an
   accepted refusal lemma (bad length, refused profile, LOCK `#UD`,
   unreadable/unwritable bytes) or a structural pin (STMXCSR on the
   register path, conversion domain on the unified leg). Planted
   behaviors (NaN-sourced conversion refused by the re-proved gate;
   core-1 empty-window refusal) are closed `decide` evaluations joined
   into the witness.
8. **Witness non-degenerate.** `fpDisp_zeuge` joins: fetched
   `ADDSS xmm2, xmm3` giving `3.0f32` with upper 96 bits preserved and
   RIP 4100; fetched `LDMXCSR [rax+4]` reset-word install with RIP
   4107; owner-only forwarding (`0x40` to core 0, zero to core 1);
   four-drain install changing actual shared memory (`0` becomes
   `0x40400000`, observed from both cores — the memory-changing step);
   NaN gate refusal; core-1 refusal; `HwWf`. Two cores participate.
9. **Silicon.** The candidate states no new silicon fact: encodings come
   from the accepted family encoders and roundtrips. LOCK-prefixed
   MXCSR refusing is consistent with the supplied Intel SDM 093US
   extract (pervasive `#UD If the LOCK prefix is used` rows). CUTS
   names the SDM extracts as provenance, not proof. No
   hardware-correspondence or W/GX claim anywhere; the open drain/
   `write32` byte correspondence, unwired `fetchExt`/`HwSchritt`, and
   sticky-flag/SNaN/DAZ/FTZ cuts are listed honestly.
10. **Builds.** Author evidence: per-section `./lean-probe` 0 errors
    (one linter warning on the `∃ s'` binder, same shape as the
    accepted `HwFpControl` file), `./lean-bau` last line
    `Build completed successfully (640 jobs)`. The evidence log also
    shows one intermediate red probe (a genuine type error) fixed
    before the final commit — consistent with real iteration.
    Reviewer run: `./lean-bau` in this clone (base tree — the
    candidate was deliberately NOT applied here per OWN ONLY) ends
    `Build completed successfully (640 jobs)`, so the base vocabulary
    this review checked the candidate against is green.

No unsupported desired-correctness premise, no weakened guarantee, no
fake closure found. The one piece I could not re-execute is the
candidate-tree build itself (ownership forbids applying the patch
here); I rely on the author's complete-output evidence log for that
line, and everything re-checkable from the snapshot (tokens, axioms
via the log, scope, lifting, pins, witness shape) passes.

## Open / not claimed (carried from the candidate CUTS, agreed)

- No hardware correspondence (self-consistency only).
- `decodeFpDisp` not wired into `fetchExt`/`HwSchritt`; unified legs
  plug in through `FpDispSchritt`.
- No target-to-W/GX simulation; no whole-word atomicity beyond drain
  groups; STMXCSR/MOVSS-store drain correspondence open at value/
  footprint issue level.
- Faults beyond the carried divide halt, sticky flags, SNaN/DAZ/FTZ,
  NaN payloads: absent / at inherited family cuts.

Nothing in lane 1211's task looks wrong; every requirement
(disjointness proof, `fetchExt_erfolg` discipline, step-level gate
re-proof, two-core non-degenerate witness) is met as stated.
