# Muse Report 381 — Independent exact-candidate B3 review of 343 SpillPrivate

Clone `/home/simon/Dokumente/gabbro-muse/a381`, branch `muse/381` verified.
Candidate snapshot: author 343, base `f737a6f04c22dfdd9499532e0535ad119cf2e56d`.
Reviewed exact snapshot files in `.tmp/review/author-343` (SNAPSHOT/OWNER-TASK/
MUSE-REPORT-343/BUILD-EVIDENCE/PATCH plus `grammatik/Grammatik/X86/SpillPrivate.lean`)
against actual accepted tree models and proof-boundary docs. No other clone read.
No network, no push. Report-only ownership: candidate module plus additive
umbrella import were staged privately for queued probes, then fully restored
before this commit; final tree contains only this report.

## What was checked

- Ownership and scope: snapshot file list is exactly `MUSE-REPORT-343.md`,
  `grammatik/Grammatik.lean` (one additive trailing import), and new
  `grammatik/Grammatik/X86/SpillPrivate.lean` (~399 lines). PATCH confirms no
  source, checker, Spec, goal, Typen, Rust, emitter, docs, or friend-reserved
  `OptimizationRules`/`OptimizationWitnesses` touch. Import is additive at end.
- Canonical reuse verified in-tree: `spillSlot` is `Rahmen.schlitzAddr`
  (`Stapel.lean`); `sichereWort`/`ladeWort`/`sichereWort_ausserhalb`
  (`Stapel.lean` lines 82-108); `Disjunkt`/`Fuss`/`write64`/`read64`
  (`Speicher.lean`); `write64_kommutiert`/`stabilFuss_bleibt`/`disjunkt_symm`/
  `mem_Fuss_iff`/`zweiSpeicher0`/`zweiNachA/B/AB/BA`/`zweiDisjunkt`/
  `zweiSchrittA/B/AB/BA`/`zweiWechseltA/B` (`SpeicherKommutation.lean`);
  `TSOZustand`/`TSOEintrag`/`pufferSetze`/`issueByte`/`flushKern`/
  `TSOErreichbar`/`issue_anderer_kern`/`issue_kein_speicher`/`flush_rahmen`/
  `issue_haengt_an` (`TSO.lean`). No second IR, no second evaluator, no SCFG
  consumer invented; 287 consumer side is marked waiting in CUTS, not substituted.
- Definitions reviewed: `spillSlot`, `SpillFrisch`, `GetrenntK`,
  `spillPrivatOk`, `SpillZugelassen`, `spillRahmenW`, `spillTSO0/1/2`.
- Theorems reviewed: `spillPrivatOk_verweigert_genommen`,
  `spillPrivatOk_verweigert_extent`, `spillPrivatOk_verweigert_aussen`,
  `spillPrivatOk_positiv`, `spill_zugelassen_verweigert_genommen`,
  `spill_zugelassen_verweigert_extent`, `spill_speichern_ist_write64`,
  `spill_laden_ist_read64`, `spill_ausserhalb_verweigert`,
  `spill_frisch_meidet_puffer`, `spill_frisch_leer`, `spillSlot_rW_null`,
  `spillSlot_rW_sechzehn`, `spill_getrennt_rW`, `spill_fill_kommutiert`,
  `spill_stabil_bleibt_fremd`, `spill_fill_kommutiert_zeuge`,
  `spill_frisch_bleibt_bei_fremd_issue`, `spill_bleibt_bei_fremd_flush`,
  `fremd_meidet_slot0`, `fremd_puffer_mem`, `spill_schritt1`, `spill_puffer1`,
  `spill_flush_schritt`, `spill_flush_wechselt`, `spill_frisch0`,
  `spill_frisch1`, `spill_tso_zeuge`.
- Rule checks: no `sorry`/`admit` tactic/`axiom`/`native_decide`/`unsafe`
  (the six `admit` substring hits are English "admitted" in doc comments);
  no `Prop`-typed premise (three `Prop` hits are `def ... : Prop` being defined);
  no `intro _` / `have _`; every theorem uses all its premises (refusals via
  first projection plus case analysis; commutation passes all four stores plus
  disjointness into `write64_kommutiert`; preservation uses issue/flush step,
  freshness, and avoidance/separation). No conclusion-as-premise; no
  quantified-away contract (no source `Vertrag` premise in this TSO-side module);
  reused semantics (`write64`/`read64`/`issueByte`/`flushKern`) change memory.
  Refusal `Bool` is validator admission only, no hardware fault invented; no
  alignment, width, float, LOCK, timing, or cost claim; byte-extensional only,
  no aligned multi-byte atomicity claimed. English only. CUTS block plus
  per-theorem `#print axioms` present.
- Witnesses: `spill_fill_kommutiert_zeuge` is joint and nondegenerate
  (concrete `spillRahmenW`/slot 0 vs address 16, `v != w` by decide, all four
  `write64` steps reach, `GetrenntK` proved, both low bytes observably change
  `0x00`->`0x08`/`0x18`, both orders agree via `spill_fill_kommutiert`).
  `spill_tso_zeuge` is reached (`TSOErreichbar` `.schritt .start (.issue ...)`
  from `spill_schritt1`), keeps `SpillFrisch` across the foreign issue, keeps
  every spill byte across the foreign flush while the foreign byte observably
  changes (`spill_flush_wechselt` by decide). Refusals are proved theorems
  (cases/simp), with positive `spillPrivatOk_positiv` by `rfl`.
- Task-reading notes (not defects): the plan phrase "freshness => disjointness"
  is informal staging, not a statable unconditional implication (an empty buffer
  does not make an arbitrary foreign footprint disjoint); the author correctly
  proves freshness preservation under avoidance/disjointness plus commutation
  from `GetrenntK`, with the link theorems `spill_frisch_bleibt_bei_fremd_issue`
  and `spill_bleibt_bei_fremd_flush`. The refusal target "never fresh" is
  correctly rendered as `¬ SpillZugelassen` (Bool plus freshness), since
  `SpillFrisch` alone is independent of taken/extent flags. Reload is covered
  as stable-footprint carry (`spill_stabil_bleibt_fremd`), not as a second
  commutation theorem; bounded claim and CUTS state this honestly.

## Verification executed

- `./lean-probe grammatik/Grammatik/X86/SpillPrivate.lean` (staged privately):
  0 errors; every `#print axioms` is no-axiom or a subset of
  `[propext, Quot.sound]`, nothing beyond the goal standard.
- `./lean-bau` (staged privately): `Build completed successfully (386 jobs).`
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean` (staged):
  0 errors; `gabbro_ziel` still on exactly
  `[propext, Classical.choice, Quot.sound]`.
- Staging restored before report: `grammatik/` clean, `git status` shows only
  this report file prior to commit.

## What remains open (matches in-file CUTS, not a rejection)

SCFG-side application waits for the accepted 287 interface; no aligned
multi-byte atomicity beyond byte extension; no LOCK RMW; no source-to-target
simulation; no cost/fairness/timing; no new ISA form. Full final-byte/source/
hardware correspondence remains open until derived.

## Judgement

Task actually done within its stated producer-half bounds: TSO-side freshness
and disjointness machinery, commutation plus stable-carry, TSO preservation,
proved refusals with positive probe, joint memory-changing witnesses, generic
canonical vocabulary only, truthful bounded claim and CUTS, green staged build
with unchanged goal axioms. No material finding requiring REPAIR.

CANDIDATE: 343 54a9c37d3223241fd23628662e2969f692fd832c
VERDICT: ACCEPT
