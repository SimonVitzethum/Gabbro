# Muse Report 873 — Optimiser rule: inlining rule

## What was done

Created `grammatik/Grammatik/X86/OptInlineCall.lean` (new file, ~537 lines)
and added its import at the end of `grammatik/Grammatik.lean`. The file
states and proves the DESIGN section 7 inlining row as a generic rule
lemma over arbitrary values with validator-decided side conditions,
reusing only accepted vocabulary (no new IR, no source/checker/Spec/goal
changes, no friend-reserved files touched).

## Exact names of new definitions/theorems

- `InlineCert` (8 Bool side conditions: `blockMapOk`, `freshRenamed`,
  `dutiesIncluded`, `depthOk`, `ghostPresent`, `reasonChannelKept`,
  `fpScopeSame`, `budgetCarried`) and `inlineAdmit` (conjunction).
- Refusals: `inlineRefuses_ghostless` (ghostless inlining refuses, even
  with identical contracts), `inlineRefuses_duties` (covers inlining
  across the lock floor), `inlineRefuses_depth`, `inlineRefuses_fpScope`,
  `inlineRefuses_blockMap`; probes `probe_inlineAdmit_ok`,
  `probe_inlineAdmit_ghostless`, `probe_inlineAdmit_duties`;
  `inlineAdmit_all` (admission unfolds into all eight).
- Certificate: `InlineCite` (`blockMapFresh`, `dutySubsetFresh`,
  `ghostOrderFresh`, `budgetExpandFresh`, `availFresh`), `citesRequired`,
  `citeOk`, `citeOk_ghostOrder`, `citeRefuses_noGhostOrder`,
  `probe_citeOk`, `probe_citeOk_noGhost`.
- IEEE: `inlineIEEE_kennwert` (kernel `0.5 + 0.25 = 0.75`, by `decide`).
- `OptInlineCall_verbindung`: generic connection concluding order
  preservation (`geistRekon_folge`), actual-value ghost re-emission,
  entry duty at its place (`rufAt_ok_vorOk`), empty reason channel
  (`Fin.cast hr`), log classification (`rufSchrittG_logSchritt`), carried
  work bound (`expandBound_keinVerlust`), all eight side conditions, and
  the fresh ghost-order citation.
- `OptInlineCall_verbindung_zeuge`: joint witness on fixture program `eP`
  (real `setze` `rufAt` equation by reduction, decided order premises, a
  genuine `w_rufEnde` step, `blattSummary` bound) plus non-degenerate
  extras (writing contract, reached five-step run from `geistRekon_zeuge`,
  `0 -> 5` memory change, real ghost pair with `Pflichtig`/`Armiert` and
  order leg, discharged `InlinePflicht` via `inlinePflicht_aus_rufAt`).

## Last `./lean-bau` result line

`Build completed successfully (511 jobs).` — whole project green.
`./lean-probe` on the new file: `0 error(s)`. Axioms: helpers on
`[propext]`; both main theorems on exactly
`[propext, Classical.choice, Quot.sound]` (standard `gabbro_ziel` set).

## What remains open (see file CUTS)

No executable source-body splice (same cut as `AufrufOpt`); return-duty
derivation and full discharge reused by citation; budget exhaustion timing
(`budgetSimulationOffen`) open per `CostSummary`; per-width float
flag/fault identity with the strength-reduction row; indirect calls have
no ghost form; no silicon/TSO/ABI claims.

## Task fidelity notes

- Every premise of every added theorem is used by its proof; no `Prop`
  premise restatement; contracts hold at their place with actual values.
- The witness order premises at `eSetze` hold by decided computation
  (`setze` is no `ruf`/`ende` function of `Φ50`); the non-vacuous order
  evidence rides in the witness extras. This is stated openly in CUTS.
- `caller`/`Λ` are not separate premises of the connection: duty
  inclusion is a validator-decided Bool (`dutiesIncluded`) plus the cited
  discharge; the actual caller/site appear in the witness `InlinePflicht`.
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes.
