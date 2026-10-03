# Muse Report 1023 — Exact review of author 873 (Optimiser rule: inlining rule)

## CANDIDATE

CANDIDATE: 873 d2fb9f67fb0f07b29472f09a8816d499590c061c

## VERDICT

VERDICT: ACCEPT (bounded; scope limits in "Accepted as" / "Not accepted" below).

## What was reviewed

- Pinned snapshot: `.tmp/review/SNAPSHOT.json` (head `d2fb9f67…`, base `b040b155…`,
  files `MUSE-REPORT-873.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/OptInlineCall.lean`, clean).
- Exact author task (`.tmp/review/author-873/OWNER-TASK.md`), author report
  (`MUSE-REPORT-873.md`), full `PATCH.diff` (624 lines), snapshot file
  `grammatik/Grammatik/X86/OptInlineCall.lean` (537 lines, identical to PATCH hunk),
  and `BUILD-EVIDENCE.json` (11 queued-wrapper runs incl. intermediate red steps).
- Base match: this reviewer clone is at `b040b155` on `muse/1023`, identical to the
  snapshot base, so every reused name was resolved against the exact base tree.
- Local hardware references (`.tmp/HARDWARE-REFERENCES/`, Intel SDM edition
  325462-093US) were available; nothing in the candidate interprets bytes, so the
  hardware scope below is N/A by construction, not by omission.

## Independent checks performed (all inside this clone)

1. Reused vocabulary resolves in the base tree with matching shapes:
   `geistRekon_folge`, `rufSchrittG_logSchritt`, `rufAt_ok_vorOk`,
   `geistRekon_zeuge` (`X86/AufrufOpt.lean`); `rufAt_ok_gibt_ens`,
   `inlinePflicht_aus_rufAt` (`X86/ContractSites.lean`, call shape at line 321
   matches the candidate's use); `expandBound_keinVerlust`, `alleMax`,
   `blattSummary`, `budgetSimulationOffen` (`X86/CostSummary.lean`);
   `geistPaar` (`X86/AufrufOpt.lean`); `Pflichtig`/`Armiert`/`FolgeLog`
   (`Folge.lean`); `gleitRechne` (`Semantik.lean`); `bruch` (`Typen.lean`);
   `w_rufEnde` (`RufAdaequatRufG.lean`); fixtures `eD/eSetze/ePruefe/eHaupt/
   eHpSetze/eRumpfHaupt/eP/eO/eSp/eInit/ehg0` (`ZielOrtEinfadenZeuge.lean`);
   `Φ50` (`FolgeZeuge.lean`).
2. Banned tokens: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` tactic or
   command in the candidate file (grep hits are only prose "admitted certificate",
   "Probe" doc comments and the required `#print axioms` lines). No `intro _`,
   no `have _`, no `forall rho`/`forall v` contract generalisation, no
   `Prop`-typed premise.
3. Premise use: every premise of `OptInlineCall_verbindung` is consumed
   (`hz`→conjunct 7, `hzit`→conjunct 8, `hruf`→duty, `hord1/hrest/hord2`→order leg,
   `hstep`→log classification, `hm`→work bound, `hr`→empty reason channel).
   Contracts hold at their place with actual values (`wahr? (eval … rho)`).
   No `ensures` derived, no refusal turned into a warning, no faulting form above
   its guard.
4. Refusals cover both DESIGN failure cases named in the file header (ghostless
   inlining with identical contracts; duty violation covering the lock floor) plus
   depth, FP-scope, block-map and missing-ghost-order-citation refusals, each with
   `decide` probes. Refusal theorems for `freshRenamed`/`reasonChannelKept`/
   `budgetCarried` individually are absent, but all eight flags are forced jointly
   by `inlineAdmit_all`; noted as follow-up, not repair.
5. Witness `OptInlineCall_verbindung_zeuge` is joint on the non-degenerate fixture
   (`setze` writes, `(eD.signatur eSetze).schreibt () = true` by `rfl`; real
   `rufAt` equation by reduction with `fuel + 1 = 1`; genuine `w_rufEnde` step;
   `blattSummary` bound `alleMax = some 5`; reached run with `0 -> 5` memory
   change; real ghost pair with `Pflichtig`/`Armiert` order leg from
   `geistRekon_zeuge`; discharged `InlinePflicht` via `inlinePflicht_aus_rufAt`).
   The order premises at `eSetze` hold by decided computation (vacuous at that
   point) — openly disclosed in the author report and the file CUTS, with the
   non-vacuous order evidence carried in the witness extras. Acceptable as stated;
   the disclosure is precise.
6. Scope hygiene: PATCH touches only the 3 snapshotted files. No friend-reserved
   optimiser files, no source/checker/`Spec`/goal/emitter edits, no new
   diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes. This clone's base
   tree contains no `OptInlineCall.lean`; the candidate was not applied here.
7. Build evidence: final `./lean-bau` green, `Build completed successfully
   (511 jobs)`; `./lean-probe` on the new file `0 error(s)`; axioms exactly
   `[propext]` for helpers and `[propext, Classical.choice, Quot.sound]` for both
   main theorems (standard `gabbro_ziel` set). The evidence log honestly shows the
   intermediate red probes. I did not re-run the full build in this clone: the
   candidate is not applied here, so a local build would only re-verify the base,
   and the complete-output evidence (with exact axiom prints and the commit hash
   `d2fb9f67` matching the pinned HEAD prefix) is sufficient. `git status` clean
   except this report.

## Accepted as (bounded acceptance)

- Validator-decided `InlineCert`/`inlineAdmit` with the stated refusal cases;
  `InlineCite` certificate shape with mandatory fresh ghost-order citation;
  `inlineIEEE_kennwert` kernel probe; and `OptInlineCall_verbindung` as a
  CHECKED-RULE packaging lemma (admission + citations + successful direct `rufAt`
  + order premises + machine step + cost bound ⇒ ghost order/value preservation,
  entry duty, empty reason channel, log classification, work bound, cited side
  conditions) with a jointly inhabited non-degenerate witness.

## Not accepted (explicitly cut by the candidate, CUTS verified precise)

- No executable source-body splice and hence no proved body-splice simulation
  (same cut as `AufrufOpt`); return-duty derivation reused by citation; budget
  exhaustion timing open per `budgetSimulationOffen`; per-width float flag/fault
  identity left to the strength-reduction row; no indirect-call ghost form; no
  silicon correspondence, no TSO/GX bridge, no ABI/loader claim. Hardware
  byte/REX/flag review is N/A: the file touches no hardware state and invents
  none, which is itself the sound abstraction here.

## Task fidelity notes

- Nothing in the owner task is believed wrong. The `ZEUGE` pair
  (`OptInlineCall_verbindung` + `_zeuge`) is delivered with the required joint,
  non-degenerate, memory-changing witness.
- Observation (no repair): conjuncts 7–8 of the connection unpack premises
  `hz`/`hzit` via `inlineAdmit_all`/`citeOk_ghostOrder`. Inside an 8-part
  conjunction whose other six parts derive independent facts, this is legitimate
  admission-unfolding, not a premise restated as the conclusion.
- Follow-up (no repair): per-flag refusal theorems for `freshRenamed`,
  `reasonChannelKept`, `budgetCarried` could complete the refusal family.

## Last `./lean-bau` result line

Candidate evidence: `Build completed successfully (511 jobs).` (whole project
green; reviewer did not re-run: candidate not applied in this clone, see check 7).
