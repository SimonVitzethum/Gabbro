# MUSE-REPORT-193 (round-6 confirmation verdict, lane 193)

## What I did

Independent confirmation review for the sixth wave: a systematic sweep over
EVERY constructor of every outcome type (`Logik`, `Hardware`, `Ausgang`,
`EndAusgang`, `RufAusgang` in `grammatik/Grammatik/Semantik.lean`;
`HaltArt` in `grammatik/Grammatik/Zielsatz/Spec.lean`; `FortFaden`/
`FortschrittG` in `grammatik/Grammatik/Fortschritt.lean`), every non-`ok`
source of `execStmt`/`execBlock`/`execBlockH`/`execEnd`/`rufAt` (incl. the
`traverse`/`retry`/`forever` runners), and every machine-G stuck condition
(`RufMaschineG.lean`, via `fortschrittG_aus`). For each entry I recorded who
decides it (user code / oracle / scheduler / model / declaration) and
whether obligation (b) (`NutzerPflicht E`) or the conclusion (`Ziel`)
constrains it. Full table in `messung/URTEIL-MUSE-2026-09-15d.md`.

I did NOT read any `URTEIL-OPUS-2026-09-15d*` file. I read
`URTEIL-OPUS-2026-09-15c.md` (G1) as instructed. No existing file changed.

## New definitions/theorems

None in the tree (reviewer lane). New scratch theorems, all in the
UNCOMMITTED probe file `$TMPDIR/probe193.lean` (git-excluded, `./lean-probe`
exit 0, 0 errors):

- `Probe193.p_sum_bewohnt`, `p_temp_bewohnt`, `p_fnptr_bewohnt` -- G1
  direction 1, own exhibits (sum value, `0.5`, placed fnptr decode).
- `Probe193.p_G1A`, `p_G1R` -- G1 direction 2 (Opus round-5 probes refuted
  at (b): `¬ NutzerPflicht E1[E1R]` via `g1PA_widerlegt`/`g1PR_widerlegt`).
- `Probe193.nE1_nutzer : NutzerPflicht nE1` -- P-never: `ensures false`
  behind `hol() -> never` SATISFIES (b) (named `nieZurueck`).
- `Probe193.nE2_nutzer : NutzerPflicht nE2` -- P-geraet: `ensures false`
  behind a read with an everywhere-false promise SATISFIES (b) (named
  `hardware`/`geraet` honest vacuity).
- `Probe193.nAW_widerlegt : NutzerWiderlegt nAW` -- P-awaits: `ensures
  false` behind `awaits g` REFUTED at (b) (showing oracle in the class).
- Supporting: decls `nD1`/`nD2`, signatures, statements, programs, oracles
  (`nO`), handlers (`nRuf`, `nRuf2`), `n_axiom_pair`, lauf lemmas,
  per-clause obligation proofs. `#print axioms`: standard
  `[propext, Classical.choice, Quot.sound]` only.

## Last `./lean-bau` result line

`Build completed successfully (228 jobs).` / `0 error line(s) in the
COMPLETE output` (full log in `$TMPDIR/lean-bau-193.log`; I changed no
`grammatik/` file, so this re-confirms the inherited tree).

## What remains open

Nothing from my task: the sweep is complete and the verdict is "the goal
with named gaps -- no unnamed gap found". The two getting-through probes
are both named stops decided by the visible declaration, not model-decided
stops filed behind the obligation's back. Deliberately not built (with
reasons in the verdict §4): register-at-empty-type (symmetric to P-never),
`vorbedingung`/`nachbedingung`/`vorzustand` (constrained, need no probe),
`grund` values (caller-side duty, reading), `Hardware.ieee` (dead by grep),
machine-side re-proof (proved by `fortschrittG_aus`).

## What I believe is wrong in the task or nearby

Nothing load-bearing. Two probe-construction traps worth recording (both
documented in the verdict §3): (1) `fun e => nomatch e` swallows the
following comma inside `⟨...⟩` -- parenthesize; (2) a pattern mentioning
`Expr.wahr.orte` elaborates implicits `Γ Λ` to metavariables, so
`cases`/`generalize`/`rw` silently miss -- collapse `orte` with
`simp only [Expr.orte]` first. Minor wording note (not a gap): "no wait
cycle" in `Spec.lean:182` covers LOCK waits only.
