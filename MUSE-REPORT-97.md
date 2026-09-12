# MUSE-REPORT-97 -- lane 97: goal map re-measured (docs lane, no Lean changes)

Branch: `muse/97`. Changed file: `dokumente/SATZKARTE.md` only (prior map
kept as history, new §§7-10 prepended). No `.lean` file touched, none added.

## What was done

1. Read the full goal family in `grammatik/Grammatik/Ziel.lean`
(`ziel_nutzer_last`, `ziel_seqLogic_aus_spec`,
`ziel_seqLogic_aus_spec_invariantForm`, `ziel_nutzer_last_aus_disziplin`,
`ziel_nutzer_last_aus_maschine`, `ziel_nutzer_last_aus_pc`,
`ziel_nutzer_last_aus_pc_stabil`, `ziel_nutzer_last_aus_pc_Q`), plus
`csl_ressourceninvariante` (`CSLInvariante.lean:305`),
`EZD.eigenzustand_nur_eigene_schritteD_rep` (`EigenZustandD.lean:1368`),
`rufG_treu` (`RufMaschineG.lean:1198`), `rufF_treu`, `hoare_call`,
`stabil_aus_lauf`, and the discharge lemmas they consume
(`interferenceFree_of_invariantForm`, `invariantenKontext_aus_disziplin`,
`speicherVertrag_aus_Q`, `haengtAb_vertrag_gesamt`, `pc_*`,
`genWelten_*`, `sampling_closes_frist`, `syscall_paarung`,
`axiomCall_haelt_waechter`, `wache_aus_schuld`, `pcSpur_von_reach`).
Also read `dokumente/PLAN-SYSCALL.md`, `PLAN-BITS.md`, `PLAN-ERWEITUNG.md`
and the wave-3 reports (`MUSE-REPORT-81/82/85`).
2. Classified every premise as (a) USER / (b) HARDWARE / (c) DISCHARGED
(named theorem) / (d) STILL OPEN, with the older family members' deltas
booked in prose (§7 table + paragraphs).
3. Proposed one fixed target statement per (d) item: D1-D9, D11-D12
(11 items; no D10 -- numbering skips it, see below).
4. Axiom probe: wrote `.tmp/sonde97.lean` (git-ignored, not committed)
with `#print axioms` for all 11 theorems; `./lean-probe` reports
0 errors; every theorem depends only on
`[propext, Classical.choice, Quot.sound]` (§9).
5. Rewrote `dokumente/SATZKARTE.md` in English with the new table, dated
2026-09-12, and a "distance to the goal" section (§10): 11 (d) items;
lane 80 expected to close D8+D12, lane 84 the straight-line halves of
D5+D1.

## Exact names of new definitions/theorems

None (docs lane; task forbids editing `.lean` files).

## Last `./lean-bau` result line

`== 0 error line(s) in the COMPLETE output` /
`Build completed successfully (53 jobs).`
(`./lean-probe .tmp/sonde97.lean`: `== 0 error(s) in the COMPLETE output`.)

## What remains open

- The 11 (d) lanes D1-D9, D11-D12 in `SATZKARTE.md` §8.
- Note: §8 numbers lanes D1-D9 then D11-D12 (no D10); the §10 count (11)
is correct, the skip is a numbering gap, not a missing lane.
- `pruefe-englisch.py` exits 1 on pre-existing Rust ratchet drift
(7905 vs 7881 booked German comment lines etc.); unrelated to this lane
(diff touches only `dokumente/SATZKARTE.md`), left alone.

## What in the task I believe is wrong

Nothing blocking. Two notes: (a) `eigenzustand_nur_eigene_schritteD_rep`
lives in namespace `Gabbro.Grammatik.EZD`, so the probe must print
`EZD.eigenzustand_nur_eigene_schritteD_rep` (bare name is unknown).
(b) The task's lane-80/84 descriptions are taken as given (both lanes are
running elsewhere, nothing merged to verify against); §10 records them as
expectations, not measurements.
