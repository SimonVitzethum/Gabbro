# MUSE-REPORT-831: Composition closing — contract-at-call closing

Clone: `/home/simon/Dokumente/gabbro-muse/a831`, branch `muse/831` (verified).
Owned files only: `grammatik/Grammatik/X86/ComposeContractCall.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

Closed contracts at call sites in one checked composition step
(`grammatik/Grammatik/X86/ComposeContractCall.lean`, ~430 lines).
The exact producer/consumer interface is stated in the file header:

- Producer (source, lane 546 `ContractSites`, reused by name, never re-proved):
  `callSite_vorOk` (requires at actual arguments), `rufAt_ok_gibt_ens`
  (ensures at actual result), `inlinePflicht_aus_rufAt` (discharged
  `InlinePflicht`).
- Ghost (log, lane 310 `AufrufOpt` vocabulary): the call's return ghost
  event `RufEreignisF.rueck` is visible in the reached thread log.
- Consumer (caller, lanes 346/349): `GateStub.torOkB`,
  `bindungErstelltB`, `stubEndsTrapB`, `ValidatorSkeleton.valZeigerOk`.

New definitions/theorems (all in `Gabbro.Grammatik.X86`):

- `rufSchluss` — the composed closing predicate for one direct call:
  `ReqAmEintritt` at actual params, `RufEnsCheck` at actual result,
  `Nonempty (InlinePflicht ...)`, return ghost event in log, admitted
  gate stub (`torOkB` + `bindungErstelltB` + `stubEndsTrapB` +
  `valZeigerOk`), reached run with log equation.
- `ComposeContractCall_verbindung` (ZEUGE target) — generic over arbitrary
  `P O passes caller g`, derives the full closing from the `execStmt`
  call equation (entry, separate fuel `fe`), the `rufAt` bundle
  (return, separate fuel `fr`), ghost membership, gate Bools and
  reachability. Every premise is used. No conclusion restates a premise:
  each contract half is derived through a producer lemma from an outcome
  equation, and the closing is a new six-way conjunction.
- `ComposeContractCall_ohne_geist_verweigert` — generic refusal: an
  alleged closing over a log with no return ghost event for `g` gives
  `False` (uses exactly the absence fact + the alleged closing).
- `ComposeContractCall_verbindung_zeuge` — joint witness instantiating
  ALL premises on `eP/eO/eSetze`: `rfl` entry equation (`fe = 1`, the
  `callSite_vorOk_zeuge` reduction), `rfl` body/`rufAt` pair (`fr = 0`,
  the `rufAt_ok_gibt_ens_zeuge` reduction), ghost event from
  `vertragStandort_lauf_zeuge`'s reached log, decided gate facts
  (`schreibTor`, `zeugenMoves`, `zeugenStub`, pointer mirror at index 1),
  plus non-degeneracy: table `konto` written (`schreibt = true`),
  start slot `0` vs entry slot `5` on one reached run, and a target-side
  `write64`/`read64` change (`write_read_zeuge`).
- `ComposeContractCall_geistlos_verweigert_zeuge` — planted refusal: the
  identical requires/ensures (same reductions) and gate hold on the
  ghost-less start log of a reached run, yet `¬ rufSchluss` (missing
  return event proved by constructor mismatch).

## Check results

- `./lean-probe grammatik/Grammatik/X86/ComposeContractCall.lean`:
  `== 0 error(s) ... exit 0`.
- `./lean-bau`: `Build completed successfully (509 jobs).`
- `#print axioms` for all four theorems:
  `[propext, Classical.choice, Quot.sound]` only.
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`: 0 errors;
  `gabbro_ziel` (and `zielX_aus`, `zielFX_aus`, `gabbro_ziel_sc_aus`,
  `gabbro_ziel_gx`, `gabbro_ziel_verbund`, `gabbro_ziel_verbund_sc_aus`)
  still depend only on `[propext, Classical.choice, Quot.sound]`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; English throughout.
- No new diagnostic/gift/example/CLI numbers, no MARKE changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched.

## What remains open (explicit CUTS in the file)

Per-access refinement into W/GX, decoder coupling, `valX86_sound`,
shared IR (lane 287 — no substitute invented here), split holdings
(the closing shares the argument-resource list as holdings),
indirect/value-carrying call sites, cost/budget transfer, callee-side
obligation (c) beyond the discharged `InlinePflicht`.

## Anything believed wrong in the task

Nothing. One honest scoping note (rule 4): the ghost half is the call's
RETURN event visibility (the closing event), not the full
`geistPaar` entry+return splice — entry pairing across the inline
boundary stays `AufrufOpt` business and is named as a CUT. The refusal
direction is exactly "identical contracts without ghost events refuse".
The two-fuel split (`fe`/`fr`) is deliberate: it reuses both producer
witness reductions verbatim instead of asserting unproved fuel
uniformity; it does not weaken the conclusion.
