# MUSE-REPORT-25: read-only audit of Geteilt.lean, Marken.lean, Koernung.lean

Lane 25. No existing file modified (`git status` shows only new files under
`messung/muse-audit/25/` plus this report). All demonstrations checked with
`./lean-probe` (green, no errors; only unused-variable linter warnings that
confirm the findings). `./lean-bau` green: `Build completed successfully
(29 jobs).`

## What I checked

- `grammatik/Grammatik/Geteilt.lean` (793 lines): all theorems in §§1-11,
  especially `geteilt_treu`, `ungeteilt_aus_bau/_baulauf/_lauf`,
  `lauf_hat_eintritt`, `nur_deklariert_teilt_lauf`, the §7-8 fold/split
  round-trips, §9 world partition, §10 owner marks.
- `grammatik/Grammatik/Marken.lean` (661 lines): §§1-8, especially the
  `getragen_*_unberuehrt` lemmas, `verlauf_aus_lauf` vs
  `einfaedig_aus_verlauf_getragen`, `StandEinfaedig` vs `Einfaedig`,
  `Getragen` satisfiability.
- `grammatik/Grammatik/Koernung.lean` (680 lines): §§1-8, especially
  `refused_no_tear`, `AtBoundary`, `shared_inventory_tearing_free`,
  `ereignisAtomar_gilt`, the negative write/read cases.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the
  slice (only prose mentions); no premise with type `Prop` itself found.

## Findings table

| # | file:line | pattern | evidence (one sentence) | demo | status | severity |
|---|-----------|---------|-------------------------|------|--------|----------|
| G1 | Geteilt.lean:675-681 | b (unused premise) | `eigner_ungeteilt_ein_faden` never names `_hm : m ∈ W.eignerVon c`; proof is `geteilt_treu` directly. | `messung/muse-audit/25/GeteiltAudit.lean`: `g1_owner_premise_unused`, `g1_direct` | VERIFIED | low (honest docstring: "proof goes through unshared-ness"; premise only selects carriers) |
| G2 | Geteilt.lean:661-668 | b (premise used only on impossible branch) | `_hmE : ∃ c, m ∈ W.eignerVon c` is consumed solely by `absurd` on the produced-half branch; with empty produced list no existence premise is needed. | GeteiltAudit: `g2_no_existence_needed` | VERIFIED | info |
| G3 | Geteilt.lean:384-414,443-447 | c (identity fold, rfl round-trip) | `carrierVonTab`, `carrierVonGlob`, `tabVonCarrier`, `globVonCarrier` are all `fun x => x`, so `tabRundweg_holds`/`globRundweg_holds` prove `t = t`; separation `halvesDisjointForm [0] [0]` is false. | GeteiltAudit: `g3_fold_is_id`, `g3_mirror_is_id`, `g3_roundtrip_is_refl`, `g3_separation_fails` | VERIFIED | low (header books C1 honestly; §8 text correctly says separation "stays a stated shape") |
| G4 | Geteilt.lean:324-339 | a (conclusion = premise unfolded) | `lauf_hat_eintritt` projects `BauLauf.1` at `s`; `nur_deklariert_teilt_lauf` projects `BauLauf.2` and discharges same-thread by contradiction. | GeteiltAudit: `g4_entry_is_projection`, `g4_pairs_is_projection` | VERIFIED | info (both docstrings already say "sentence form" / "the definition, applied") |
| G5 | Geteilt.lean:342-348,759-776 | a (lifting = pre-applied premise) | `ungeteilt_aus_baulauf` is `ungeteilt_aus_bau` on `hl.1`; `ungeteilt_aus_lauf` adds only `mem_faltLauf` + two `congrArg`s. | GeteiltAudit: `g5_baulauf_is_bau` | VERIFIED | info (layering toward `hungeteilt` shape is genuine wiring, thin but real) |
| G6 | Geteilt.lean:302-312 | e-check (non-finding) | Coverage premise is satisfiable: `ErreichtBau miniB 3 0 7` holds by `RuftStarN.refl` + `by decide`. | GeteiltAudit: `g6_coverage_satisfiable` | VERIFIED (no vacuity) | - |
| M1 | Marken.lean:592-630 | b (unused step premises) | `getragen_erzeuge/fuehre/verbrauche_unberuehrt` bind full step hypotheses (`_hfrei`, `_hstufe`, `_hfremd`, `_hbesitz`) but use only `hU` + `hG` + `*_anders`; Lean's unused-variable linter fires on the m1 copies too. | `messung/muse-audit/25/MarkenAudit.lean`: `m1_erzeuge/fuehre/verbrauche_ohne_praemissen` | VERIFIED | low (lemmas frame `Unbenannt` preservation; step premises document intent but prove nothing) |
| M2 | Marken.lean:647-649 | a (alias theorem) | `einfaedig_aus_verlauf_getragen` is `verlauf_aus_lauf` with identical binders, one-application proof. | MarkenAudit: `m2_alias_vorwaerts`, `m2_alias_beide_wege` | VERIFIED | info (docstring honestly calls it "Corollary" for use-site `exact`) |
| M3 | Marken.lean:169-170,378-385 | c/d-check (separated, not a finding) | State-form `StandEinfaedig` is the function shape (header says so: "die Gestalt, keine Leistung"); run-form `Einfaedig` is NOT trivial -- two threads naming mark 7 refute it. | MarkenAudit: `m3_standform_ohne_induktion`, `m3_laufform_nicht_trivial` | VERIFIED (no overclaim; header is explicit) | - |
| M4 | Marken.lean:366-376 | a (pair + application restatements) | `verlauf_treu_und_einfaedig` pairs the two preceding theorems; `verlauf_besitz_stufe` applies `verlauf_stufentreu` to unpacked `Besitzt`. | MarkenAudit: `m4_paar_ableitung`, `m4_besitz_ableitung` | VERIFIED | info |
| M5 | Marken.lean:537-540 | c-check (non-finding) | `Getragen` is neither trivially true (refuted at `Anfang` for mark-naming run) nor trivially false (holds for owned-mark run). | MarkenAudit: `m5_getragen_erfuellbar`, `m5_getragen_nicht_leer` | VERIFIED (genuine predicate) | - |
| K1 | Koernung.lean:575-581 | b (unused premise + vacuous case split) | `refused_no_tear` never names `f` or `h : f.verdict = some g`; both `Guarantee` branches are `boundary_no_tear`. | `messung/muse-audit/25/KoernungAudit.lean`: `k1_ohne_verdict`, `k1_verdict_funktional` | VERIFIED | medium (theorem is ABOUT refused rows only via an unused hypothesis; the real content -- guarantee = boundary premise -- lives in prose + `AtBoundary` def) |
| K2 | Koernung.lean:559-560 | b/c (ignored argument) | `AtBoundary (_old new m)` ignores `old` (underscore binder); swapping old bytes preserves it. | KoernungAudit: `k2_alte_bytes_irrelevant` | VERIFIED | low (boundary genuinely depends only on `new`/`m`, but the two-sided name overclaims) |
| K3 | Koernung.lean:632-642 | a (per-disjunct re-discharge) | `shared_inventory_tearing_free` admitted/refused cases are direct applications of `admitted_no_tear` / `boundary_no_tear`. | KoernungAudit: `k3_admitted_ist_liste`, `k3_refused_ist_grenze` | VERIFIED | info (exhaustiveness via `ruling_covers` pattern is the real contribution) |
| K4 | Koernung.lean:625-642 | d (name overclaims) | "tearing_free" conclusion for `.volatileReg` is the tag `form = .volatileReg`, which holds jointly with the witnessed tear `mid_interruption_tears`. | KoernungAudit: `k4_volatil_trotz_riss` | VERIFIED | low (docstring does disclose "the open volatile row gets no claim"; the theorem NAME does not) |
| K5 | Koernung.lean:99-105,169-204 | non-findings | `EreignisAtomar` satisfiable for every event (`ereignisAtomar_gilt`); negative cases prove genuine `≠` (`schreibBytes_not_single`, `leseBytes_not_atomic`). | KoernungAudit: `k5_praemisse_erfuellbar` | VERIFIED | - |

Zero UNVERIFIED rows: every finding has a `./lean-probe`-checked demo.
`#print axioms` for demo theorems show only `propext`/`Quot.sound`/
`Classical.choice` (from `decide`/`Classical` in demos and list lemmas);
no `sorryAx` anywhere.

## What I did not find

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the slice.
- No premise of type `Prop` itself.
- No quantified-away contract parameters (no `requires`/`ensures` in slice).
- No memory-changing semantics claims in the slice (no `execStmt` folds here).
- No premises false for ordinary programs: `pruefeUngeteilt miniB 3 = true`
  computes by `rfl`; `BauLauf` coverage holds for the speech-probe run.
- The genuinely load-bearing results look real: `geteilt_treu` (checker
  soundness over computed reachability), `verlauf_stufentreu`/
  `verlauf_einfaedig` (induction over `Verlauf`), `schreibBytes_prefix_readback`
  (world-level readback), `two_byte_tear` (witnessed mix). Not challenged.

## What remains open / suggestions

- K1 is the sharpest: consider restating `refused_no_tear` without the
  unused `f`/`h` (take `AtBoundary` as THE guarantee premise), or prove a
  lemma connecting `verdict = some g` to `AtBoundary` so the hypothesis is
  used. Same for M1 (drop step premises or use them) and G1 (drop `_hm` or
  feed it into carrier selection explicitly).
- K4: rename `shared_inventory_tearing_free` or restrict its statement to
  non-volatile rows so the name does not claim what the volatile disjunct
  disclaims.
- G3: fine as booked cut C1, but the §8 header "The split round-trips,
  proved" could say "the identity fold round-trips" to avoid implying
  separation progress.

## Task feedback (what I believe is wrong)

- Nothing in the task is wrong. The pattern catalog (a-e) fit the slice
  well; the main correction I would offer: several "pattern-a" hits
  (G4, G5, M2, M4, K3) are explicitly documented as sentence-form
  restatements/corollaries in the source -- they are honest API-shaping,
  not disguised progress. The audit value is in the (b) hits (G1, M1, K1)
  and the (d) hit (K4), where unused premises or names genuinely overclaim.

## New definitions/theorems (all in `messung/muse-audit/25/`, audit-only)

- `GeteiltAudit.lean` (`Audit25.Geteilt`): `g1_owner_premise_unused`,
  `g1_direct`, `g2_no_existence_needed`, `g3_fold_is_id`,
  `g3_mirror_is_id`, `g3_roundtrip_is_refl`, `g3_separation_fails`,
  `g4_entry_is_projection`, `g4_pairs_is_projection`, `g5_baulauf_is_bau`,
  `g6_coverage_satisfiable`.
- `MarkenAudit.lean` (`Audit25.Marken`): `m1_erzeuge/fuehre/verbrauche_ohne_praemissen`,
  `m2_alias_vorwaerts`, `m2_alias_beide_wege`,
  `m3_standform_ohne_induktion`, `m3_laufform_nicht_trivial`,
  `m4_paar_ableitung`, `m4_besitz_ableitung`, `m5_getragen_erfuellbar`,
  `m5_getragen_nicht_leer`.
- `KoernungAudit.lean` (`Audit25.Koernung`): `k1_ohne_verdict`,
  `k1_verdict_funktional`, `k2_alte_bytes_irrelevant`,
  `k3_admitted_ist_liste`, `k3_refused_ist_grenze`,
  `k4_volatil_trotz_riss`, `k5_praemisse_erfuellbar`.

## Build record

- `./lean-probe messung/muse-audit/25/GeteiltAudit.lean`: green (1 linter
  warning confirming G1: `_hm` unused).
- `./lean-probe messung/muse-audit/25/MarkenAudit.lean`: green (linter
  warnings confirming M1: step binders unused in stripped copies too).
- `./lean-probe messung/muse-audit/25/KoernungAudit.lean`: green (linter
  warnings confirming K1: guarantee binder unused).
- `./lean-bau`: `Build completed successfully (29 jobs).`

<!--
CUTS:
- Audit-only lane: no theorems added to `grammatik/`; nothing to discharge.
- All findings VERIFIED via checked demos; no UNVERIFIED rows.
-->
