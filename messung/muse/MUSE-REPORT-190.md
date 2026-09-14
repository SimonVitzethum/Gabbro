# MUSE-REPORT-190 (lane 190, fourth independent review, 2026-09-15b)

## What I did

Wrote `messung/URTEIL-MUSE-2026-09-15b.md` (English): the fourth independent
verdict on whether the repaired `theorem gabbro_ziel : GabbroZiel` is the
goal. Read `dokumente/SATZKARTE.md` §22, the `Spec.lean` header (Einheit,
NutzerPflicht with StartPflicht, Laufzeit A4, the one assumption list),
`Zielsatz/Beweis.lean`, `Zielsatz/Akzeptiert.lean`,
`Zielsatz/SpecProben.lean`, `Zielsatz/Proben.lean`, both third-round verdicts
(MUSE-2026-09-15 by lane 189, OPUS-2026-09-15), and `RegLokal`
(`ZielOrtGeraetSem.lean`). Changed NO existing file; added NO Lean file to
`grammatik/` (so no `Grammatik.lean` import edit needed). Scratch probe
`.tmp/sonde190.lean` only (git-ignored, not committed).

## New definitions/theorems

None in `grammatik/`. New files: `messung/URTEIL-MUSE-2026-09-15b.md`
(the verdict) and this report. Probe (not committed) `#check`s:
`probeA_falsch_inv_nicht`, `unerfuellbar_widerlegt`, `havocOk_bewohnt`,
`p1_akzeptiert`, `start_req_widerlegt`, `laufzeit_nur_erklaert`,
`laufzeit_ohne_starts`, `laufzeit_ruhe`, `laufzeit_initRuhe`,
`akD_kein_zweiter_schreiber`, `akP3_ohne_starts`,
`zwei_schreiber_abgelehnt_gilt`, `ungeschuetzt_abgelehnt_gilt`,
`rennfreiBis_of`, `register_ohne_traeger_konstant`, `gabbro_ziel`,
`gabbro_ziel_zeuge`, plus `#print axioms` for `gabbro_ziel`,
`probeA_falsch_inv_nicht`, `havocOk_bewohnt`.

## Last `./lean-bau` result line

`Build completed successfully (225 jobs).`
`./lean-probe .tmp/sonde190.lean`: `0 error(s)`, exit 0. Axioms:
`gabbro_ziel`, `probeA_falsch_inv_nicht`, `havocOk_bewohnt` all
`[propext, Classical.choice, Quot.sound]`.

## Verdict (one line)

`GabbroZiel` is the goal with named gaps (§6 of the verdict: 9 model
design boundaries, 1 use-side half-gap, 3 implementation distances).

## What remains open

All in verdict §6. Implementation distance: no single Rust `Akzeptiert`
Bool (components N290-N294, N240-half, H013 exist; no-reasons half of
`wurzeln` still missing — `startexklusiv.rs` never mentions `gruende`);
`obligations --g` states the older `ziel_ort_sperre_ende` vocabulary, not
`NutzerPflicht E`; C linkage one program/one thread, exporter fills no
`starts`/`sp0`/source `requires`, concurrent stage unstarted. Model
boundaries: weakest `zeit` leg, no-unnamed-stuck-state progress, atomic
exemption, adequacy limits, `RegLokal` constancy asterisk, one-thread-
per-busy-start, stack depth, returns-only invariants, no ensures at
reason exits.

## Where I believe the task description was imprecise

1. "verify P1-P3 closed with ./lean-probe on a .tmp/ file" — done, but
   the P3 remainder deserves naming: the legacy predicate `DatenRasse`
   (`RennfreiVoll.lean:655-659`) still carries `¬ PaarungAusgenommen`;
   it is not the goal's race leg (`RennfreiBis`, `Spec.lean:386-393`,
   verified exemption-free by grep), so P3 is closed AT THE GOAL while
   the old predicate keeps the exemption. The verdict names this.
2. The "stale" hints check out with one correction: gap 10
   (`obligations --g`) is not fully stale — the tool states the OLDER
   obligation vocabulary (`ziel_ort_sperre_ende`: `KoerperGutS`/`InvGutS`
   + start duty), not today's `NutzerPflicht E` over `Einheit`/`mitRuhe`
   (no `InvGutGrund`, no `StartPflicht` shape). Marked PARTLY, not
   CLOSED, with the file/line evidence.
3. Nothing in the task was wrong about the grouping questions: every
   premise is in exactly one group; `S`/`Q`/`starts`/`sp0` are fields
   of `E`, not premises — the P2 repair as described in SATZKARTE §22
   verifies against the tree.
