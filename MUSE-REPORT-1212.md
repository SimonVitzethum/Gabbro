# MUSE-REPORT-1212: exact review of candidate 1211 (FP s32/MXCSR dispatcher)

Lane 1212, report-only independent exact review. Clone
`/home/simon/Dokumente/gabbro-muse/a1212`, branch `muse/1212` verified
(`.git/HEAD` = `refs/heads/muse/1212`; working tree `git status` clean).
Owned file only: `MUSE-REPORT-1212.md`.

CANDIDATE: 1211 339cb28b7a56ac8f7006d4575809422c1469d5d0
(base `988d75ef`), reviewed from the exact snapshot in
`.tmp/review/author-1211/` (`PATCH.diff`, 1453 lines; file snapshot;
`BUILD-EVIDENCE.json`). The author clone `a1211` is outside this lane's
allowed directory, so the pinned snapshot is the review basis; it lists
exactly three files, `clean: true`. This report re-reviews the NEW
pinned HEAD after the author's repair commit; the previous verdict on
`fe97f2a1` is superseded and is not reused below.

## Verdict

VERDICT: ACCEPT

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

## Re-review after the author repair (new pinned HEAD)

The repair commit `339cb28b` ("repair report: integration gate failed
on resources") was inspected in full. It changes exactly one file:
`MUSE-REPORT-1211.md` gains a 42-line repair section (report hunk
`@@ -0,0 +1,125 @@`; total `PATCH.diff` 1453 lines vs 1411
before). The Lean module `HwFpDispatch.lean` and the `Grammatik.lean`
import line are untouched.

Verification that the module is unchanged, not assumed:

- Re-read the new snapshot's `HwFpDispatch.lean` end to end (all 1307
  lines, same five chunks as the first review): identical content —
  same imports, same `FpDispInstr`/`decodeFpDisp`/pins/fetch/gate/
  state-dispatch/machine-step/agreement/refusal/witness sections,
  same CUTS block, same 15 `#print axioms` lines, same
  `end Gabbro.Grammatik.X86`.
- Re-ran the banned-token grep on the new snapshot: the same 13
  English "admit(s)/admitted" comment lines at the same line numbers;
  no `sorry`/`admit`/`axiom`/`native_decide`/`sorryAx`/`unsafe`.
- Re-ran the no-redefinition grep on the new snapshot: no
  `s32Schritt`/`mxcsrSchritt`/`s32Decode`/`mxcsrDecode`/
  `fpHwCvttZugelassen`/`stepExt`/`decodeExt`/`FpCtrlSchritt`
  definition. All previous findings (scope, axioms, premise use,
  lifting, disjointness, refusals, witness, silicon, CUTS) therefore
  carry over unchanged to the new HEAD.
- Fresh author evidence in `BUILD-EVIDENCE.json` (post-repair
  entries): `./lean-probe` on the unchanged module gives
  `== 0 error(s) in the COMPLETE output; exit 0` (same single `s'`
  linter warning), and `./lean-bau` ends
  `Build completed successfully (640 jobs)`.

On the integration gate failure quoted in the author's repair
section (`Lean merge build failed`, `failed to create thread`, exit
134 on `HwFpDispatch` after 10s, zero Lean error lines): the quoted
signature is a resource exhaustion (pthread creation under a
parallel 642-job integration build), consistent with the project's
documented virtual-address/thread-exhaustion failure mode — not a
proof defect, and the module re-verified green twice afterwards in
the author clone. I find the author's classification honest and I
found no defect it could be masking: every `decide` in the file is
a small closed evaluation over byte lists of 4–11 bytes. Integration
green on retry (thread budget) remains the integrator's concern and
is explicitly NOT claimed by this module verdict.

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
