# MUSE-REPORT-143 (lane 143, independent verdict)

## What I did

Independent-reviewer lane: wrote `messung/URTEIL-MUSE-2026-09-13.md` (English
verdict on whether the project goal is reached). No existing file changed; no
Lean work added to `grammatik/`; probe scratch `.tmp/sonde143.lean` not committed.
Did not look for or read `messung/URTEIL-OPUS-*`.

Read first: `dokumente/SATZKARTE.md` (full, incl. new sections 11-12),
`grammatik/Grammatik/ZielOrtRahmen.lean` (statement + CUTS), `Referenz104Rahmen.lean`,
`AuditZiel.lean`, `AuditFinal.lean`, `RennfreiVoll.lean` (theorem + CUTS),
`KostenG.lean` (targets 1-3 + findings F1-F9 + CUTS), `MUSE-REPORT-133.md`,
`MUSE-REPORT-134.md`, `dokumente/SYNTAX.md` decidability table rows, plus grep
evidence for checker rules (`N240` in `startexklusiv.rs`, `E220`/`E221` in
`wirkungen.rs`, `H222`/`H007` in `geteilt.rs`, tests in `startexklusiv.rs`,
`vertragsfuss.rs`, `bau.rs`, `korpus.rs`) and surface counts over `beispiele/`
(91 files).

## New definitions/theorems

None (reviewer lane; task forbids changing existing files). Verdict file only.

Carrier-less surface list (no `table`/`global`/`lock`/`register`, heuristic):
11a, 11, 12, 14, 21, 22, 23, 24, 26, 29, 32, 35, 36, 51, 54, 60, 61, 62, 63, 64,
67, 68, 69, 73, 92, 93, 98, 99 (28 files). Other counts: `traverse` 13 files,
`forever` 7, `awaits` 8, `axiom` 3, `register` 9, `atomic` 10, `locks` 26,
`exchange` 5, `transition` 8, `concurrent` 2, no surface `table` 38.

## Last `./lean-bau` result line

`Build completed successfully (103 jobs).`

`./lean-probe .tmp/sonde143.lean`: `== 0 error(s) in the COMPLETE output`.
Axioms: `ziel_ort_rahmen`, `ziel_ort_rahmen_ref104`, `rennfrei_g_voll`,
`frame_schritte_beschraenkt` all depend only on
`[propext, Classical.choice, Quot.sound]`.

## What remains open

Nothing in this lane: verdict written. Open for the PROJECT (ordered): (1) G to
emitted-C linkage -- zero theorems; (2) checker rules computing exactly
`programmImFragmentG`/`fussOrtGB`/`fs` per `.gab` file (neighbours N240, E220/E221,
H222, H007 exist and fire; the composition is Lean-side); (3) waiting/time --
scheduler assumption unproved, F1-F9 undercounts, TARGET 4 not in the model;
(4) named fragment edges (carrier-less, locks-block-only readers, non-local
devices, reason frames, per-slot frames, same-routine threading); (5) adequacy
via contract-ignoring `rufRumpf`, loop-free converse only.

## Anything in the task I believe is wrong

Two task-text claims are outdated (agreeing with lane 134): `KostenG.lean`
exists (the task's material list implies time coverage is open -- it is, but
step bounds DO exist, so "time" needs the precise cost-vs-time distinction my
verdict draws); and `rennfrei_g_voll` now covers reads at any distance (the
older "adjacent double-write" description understates it -- the remaining gap
is read/write formulation and release-explicit non-adjacent form, not distance).
No target statement was given, so rule 12 does not apply.
