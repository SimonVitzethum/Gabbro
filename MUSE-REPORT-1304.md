# MUSE-REPORT-1304: Exact review of candidate 1303 (HwXsaveFull)

Lane 1304, branch `muse/1304`, clone `/home/simon/Dokumente/gabbro-muse/a1304`.
Re-review of the REPAIRED candidate 1303, pinned HEAD
`1370d3f54ae032b15d58e24a465420691156e243` (base
`234f2728a718157cba0e1f9e0ef300874b34ea6a`), delivered as files under
`.tmp/review/author-1303/` (SNAPSHOT.json, PATCH.diff, OWNER-TASK.md,
BUILD-EVIDENCE.json, MUSE-REPORT-1303.md, the three changed files at
their repository paths). The author clone and the pinned hash were never
touched; no `git show/log/diff` on the pinned hash was used.
The previous verdict on `647ed0a6` is superseded by this re-review;
nothing from it is carried over unverified — every point below was
re-checked on the NEW files. The repair is a mechanical rename
(`Voll`/`voll` → `Xsave`/`xsave`, plus `kanonisch` → `xsaveKanonisch`,
`witArt` → `xsaveWitArt`, `witFehler` → `xsaveWitFehler`) after the
integration gate found `VollEreignis` owned by sibling lane
`HwTranslateFull`; all names below use the new mapping.

CANDIDATE: 1303 1370d3f54ae032b15d58e24a465420691156e243

VERDICT: ACCEPT

## What was checked

1. **File scope.** Changed files are exactly the three in SNAPSHOT.json:
   `MUSE-REPORT-1303.md` (new), `grammatik/Grammatik/X86/HwXsaveFull.lean`
   (new, 2829 lines), `grammatik/Grammatik.lean` (one appended line
   `import Grammatik.X86.HwXsaveFull`, verified in PATCH.diff hunks at
   lines 124-132). No other file touched.
2. **No forbidden tactics.** Grep for `\bsorry\b|\badmit\b|`
   `\bnative_decide\b|\bunsafe\b|^axiom\b` over the candidate file: no
   match. The only `axiom` substring hits are the 20 `#print axioms`
   lines plus one CUTS comment line. No `sorryAx`.
3. **Independent probe, green.** `./lean-probe
   .tmp/review/author-1303/grammatik/Grammatik/X86/HwXsaveFull.lean`
   (run in place; a bash copy of the file into `grammatik/` was refused
   by the permission classifier, so the candidate was elaborated at its
   delivered path, resolving imports against this clone's newer tree):
   `== 0 error(s) in the COMPLETE output; exit 0`. The 20 `#print
   axioms` lines all report subsets of `[propext, Quot.sound]`
   (several `[propext]` only) — standard, matching the author's claim.
4. **Baseline build, green.** `./lean-bau` on this clone (without the
   candidate integrated — see § Findings 1): `== exit 0; 0 error
   line(s) in the COMPLETE output`, `Build completed successfully (692
   jobs)`. `git status --short` is empty, so this commit owns only this
   report.
5. **Premises used.** No `intro _` / `have _ :=` discard anywhere. The
   single underscore-name hit (`intro _hb _hk832 _hnd hm`,
   `neuestens_einmal832` nil case) is a vacuous induction base case
   closed by `simp at hm`; all four hypotheses are used in the cons
   case. No `Prop`-typed premise; no conclusion restating a premise;
   no contract quantification (no contracts in this hardware lane).
6. **Lifted, not copied.** The file imports `HwContextState`,
   `Avx2State`, `HwFaults` and reuses `HwMaschine`/`HwSchritt`/`HwWf`,
   `issueByte`/`loadByte`/`flushKern`/`issueListe`,
   `ctxAlle`/`fxEintraegeAux`/`ctxLadeAux`/`ctxLade_geladen`/
   `ctxFalte`/`ctxNull`/`ctxByte`/`ctxOffsets`/`mxcsrReserviertFrei`/
   `ldmxcsrArchOk`/`xcr0SseBereit`/`xcr0AvxBereit`,
   `YmmDatei`/`vecJoin`/`vLo`/`vHi`, `ArchFehler` unchanged. The
   `HwAdapter`-vs-relation choice is the task-allowed relation
   (`XsaveSchritt` with exact two-way TSO-leg embedding:
   `xsaveLade_ist_hw`, `xsaveGibAus_ist_hw`, `xsaveSpüle_ist_hw`,
   `xsaveSpüle_ist_hw_zurueck`), with the reason documented (x87/mask/YMM
   state lives beside `HwMaschine`, as in the accepted `YmmMaschine`
   wrapper). `xsaveSpeichern_wf`/`xsaveWiederherstellen_wf`/`xsaveSchritt_wf`
   preserve `XsaveWf`. No `Voll*`/`voll[A-Z]` identifier remains in the
   file (grep: no match), so the evidenced gate collision
   (`VollEreignis.noConfusion` from `HwTranslateFull`) is removed by
   construction; the three hardened names (`xsaveKanonisch`,
   `xsaveWitArt`, `xsaveWitFehler`) have no bare counterparts left.
7. **Refusals really refuse.** Every fault gate is a proved outcome
   equality by unfolding (`xsaveSpeichern_fehlerNM`,
   `_fehlerUD_ohne_cpuid`, `_fehlerUD_lock`, `_fehlerGP_ohne_x87`,
   `_fehlerUD_ohne_sse`, `_fehlerUD_ohne_avx`, `_verweigert_leer`,
   `_fehlerGP_nicht_xsaveKanonisch`, `_fehlerGP_falsch_ausgerichtet`,
   `_fehlerSS`, `_fehlerPF`, `_fehlerAC`,
   `_verweigert_ohne_schreibrecht`, restore mirrors plus
   `_fehlerGP_reserviert` with exact `ldmxcsrArchOk` agreement), and the
   empty request plus the reserved-bit #GP are additionally
   `decide`-observed (`wit_empty`, `wit_gp_reserviert`,
   `wit_verweigert`).
8. **Witness non-degenerate.** `xsaveRundlauf_maschine_zeuge` joins on
   reached two-core state: core 0 AVX-only save at 0x1000 (476 buffered
   entries), core 1 SSE-only save at 0x2000 (480 entries), owner-only
   forwarding (`wit_fwd0/1`: mask byte 191, header byte 5 = XSTATE_BV
   bits 0+2, YMM byte 9, x87 byte 5, MXCSR byte 191), foreign view still
   zero (`wit_fremd`), a memory-changing drain (`wit_drain`: cell 0 → 5
   after one flush), applied and observed round trips
   (`wit_restore0/1`, `wit_rundlauf_anwendung0/1`), refusals, FINIT
   facts and `XsaveWf`. (No `ZEUGE:` line in the owner task; the joint
   witness exceeds what rule 13 requires for non-syntax premises.)
9. **Silicon facts.** Footprint matches the Intel layout: x87 block
   0–23 + 32–159 (152 bytes), MXCSR 24–27, MXCSR_MASK 28–31, XMM via
   accepted `ctxOffsets`, header 512–575 with XCOMP_BV 0, YMM_Hi128
   576–831; XSTATE_BV = 1 + 2·SSE + 4·AVX (bits 0/1/2); masks carried
   and written but ignored on restore (stated); FINIT reset value is an
   explicitly opaque constant, not a silicon claim. Fault classes
   NM/UD-CPUID+LOCK/GP/SS/PF/AC/canonical+alignment come from the
   accepted `ArchFehler` vocabulary with oracle inputs and documented
   priority; derivation (TS bit, CPUID, segments, paging, CPL/AC) is
   booked as oracle, not assumed. No hardware-correspondence and no W/GX
   claim anywhere (grep confirms only CUTS disclaimers).
10. **CUTS honest.** The file ends with a full CUTS block (x87 FPU
    execution, mask semantics, header enforcement, RFBM/XSS/supervisor/
    compacted forms, 48-bit-only canonical check, the 736-entry joint
    kernel-evaluation wall with per-component observation instead, no
    W/GX/atomicity/source links, handler bodies user logic) plus
    `#print axioms` for all 20 main theorems. No claim exceeds the proof;
    `gabbro_ziel` untouched.

## Findings (not verdict-relevant)

1. **Repair provenance.** BUILD-EVIDENCE.json chains the old commit
   `647ed0a6` (the stale verdict's candidate) to the repair commit
   `1370d3f5` (= the NEW pinned HEAD), with `./lean-probe` 0 errors
   under the `xsave*` names and `./lean-bau` green (677 jobs) at that
   commit. The author's MUSE-REPORT-1303.md documents the rename as
   two mechanical `replaceAll` passes plus three hardened names, with
   semantics and proofs untouched — consistent with what the files
   show (same 2829 lines, same footprint bounds/offsets/witness
   values, only identifier prefixes moved).
2. **Collision premise not locally reproducible — honestly booked.**
   This clone's `grammatik/Grammatik/X86/` contains no `VollEreignis`
   (grep: no match), i.e. the sibling `HwTranslateFull` is not in this
   tree, so the gate's `already contains
   'Gabbro.Grammatik.X86.VollEreignis.noConfusion'` cannot be replayed
   here. The author states this residual risk plainly and leaves it to
   the gate re-check. The rename removes the entire evidenced family
   regardless, which is the correct mechanical fix.
3. The lane instruction "copy the candidate's Lean file into your own
   clone first" could not be executed literally: a bash `cp` of the
   file into `grammatik/` was refused by the permission classifier
   (two rejections; plain `ls`/`git status`/`lean-probe`/`lean-bau`
   commands were allowed). The probe was therefore run at the delivered
   path, which still elaborates the exact candidate bytes against this
   clone's dependency tree — and passes with 0 errors. The `./lean-bau`
   line above is the baseline tree, not a candidate-integrated build;
   the author's BUILD-EVIDENCE.json records the integrated build path
   (old snapshot iterated to `== 0 error(s)`, `Build completed
   successfully (677 jobs)`; repair commit re-verified the same way:
   probe 0 errors under `xsave*` names, `Build completed successfully
   (677 jobs)`).
4. The candidate's base (`234f2728`) is older than this clone's tree
   (tail imports `ValidatorKapDecoder`/`IntSignXchg`/
   `PipelineBlockTables`; 692 vs 677 jobs). The 0-error probe against
   the newer dependencies is the stronger signal and it holds.
   Fresh `./lean-bau` on this clone after the re-review: `== exit 0;
   0 error line(s) in the COMPLETE output`, `Build completed
   successfully (692 jobs)`.

## What remains open

Nothing in this review lane. Remaining work is the candidate's own
documented CUTS list (see §10 above), owned by future lanes.

Co-Authored-By: muse-agent-1304 <muse-agent-1304@noreply.invalid>
