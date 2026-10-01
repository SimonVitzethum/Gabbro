# MUSE-REPORT-308: Independent counter-review of candidates 292, 293, 294

Lane 308, model opencode-go/muse-spark-1.3-contributor. Isolation gate passed
before any work: pwd `/home/simon/Dokumente/gabbro-muse/a308`, toplevel
`/home/simon/Dokumente/gabbro-muse/a308`, branch `muse/308`.

## Task

Counter-review the exact committed candidates pinned by `.tmp/review/SNAPSHOT.json`
(all based on `f4958150`):

- 292 `0e54300346132acb1ca5a47e623172694c0ba205` — source/invariant trust-boundary review
- 293 `ac45a5a5170a6695c48302849c4cc3265c96c6a9` — concurrency granularity / target bridge review
- 294 `961c6e00b3db3dd93666eaa45742999703704e14` — optimiser / full-binary obligation review

Method: read each author task, report, patch (owned files only) and review
document in full; re-checked every load-bearing factual claim against the Lean
sources and design documents at the pinned base `f4958150` via `git show`/`git grep`
in my own clone. No source edits, no builds (docs-only counter-review; no Lean
file touched), no network, no delegation.

## What was done

1. Confirmed each author patch touches only its two owned files
   (`MUSE-REPORT-NN.md` + one `dokumente/x86/REVIEW-*.md`), matching SNAPSHOT.json
   (`clean: true`, exact file lists). BUILD-EVIDENCE.json of each lane shows only
   owned-file status transitions.
2. Verified the dated baseline-absence claims at `f4958150` mechanically:
   - `grammatik/Grammatik/X86/` holds exactly `Typen.lean`, `Wort.lean`,
     `Speicher.lean` (294 §5 table: exact).
   - No `*SCFG*` anywhere under `grammatik/` or `bruecke/` (293 row 29: exact).
   - None of `DutyExport`, `EffectExport`, `AtomicExport`, `FpExport`,
     `CostExport`, `LowerMap`, `valX86`, `X86Verfeinerung`, `lowerOk`,
     `layoutOk`, `check_C` defined in any `.lean` file (292 §0/§7: exact).
3. Spot-checked source anchors at the base (all EXACT unless noted):
   - 292: `einheitAllg` sets five fields, `gestartet` implicit default `[]`
     (`Quelle.lean` 93-98, `Spec.lean` 1515); `startsAllg` filters unknown names
     and non-parameterless entries (`Quelle.lean` 84-89); `declOf` all-false /
     all-empty rows (`erlaubt` false, `Glob := Empty`, `maskiert` false,
     `UebersetzeAllg.lean` 147-196); `preExpr` = entry integer shapes + one
     `true` per held lock, non-`.int` dropped (`Pflichten.lean` 142-158);
     `hyps … | none => False` and `postU … .getD False` refusals
     (`Pflichten.lean` 285-300); `S := SperrInv.leer` discharged via
     `invGutS_leer` (`Simulation.lean` 250-258); NOT CLAIMED writer/held-section
     boundary (`Spec.lean` 1383-1391); `korrOk_fnCorr` is the C-call relation
     (`KorrespondenzAllg.lean` 1905ff).
   - 293: `schwach_ist_gX` exists with `KoerperGutSA`-free premises
     (`AtomarW.lean` 279); `SchwachX` universally quantifies over `ord`
     (`Spec.lean` 2200-2206); `Befehl` has no LOCK, no fence, no sub-64-bit form
     (`Typen.lean` 53-72); `GutO` constrains writes/locks/trace only, not
     foreign read footprint (`Satz.lean` 967-983); `FortschrittG` verbatim
     (`Spec.lean` 1828-1831); assumption (5) stated as ASSUMED at both ends
     (`Spec.lean` 1171-1177); the three off-by-ones disclosed in the report
     (87 vs 92, 287 vs 288, 455/457/462 vs 454, 426 vs 425) are real and
     immaterial; TSO bridge disclaims fairness repeatedly (§§4.10/6.9),
     IMAGE-ABI contains no fairness/eventuality language at all.
   - 294: `Budget.lean` C1 (no `Stmt`/`Block`-to-op-list link) and C5
     (declared `assign`, no `execStmt` link) verbatim; `Folge.lean` `fNach`
     clears on compound/indirect/lock/loop, `FolgeOk` forces `ruf` into `ind`,
     `FolgeLog` demands the DIRECTLY older entry be a `vor` return;
     `Wort.lean` carries 55 theorem/lemma lines with CF/OF distinct;
     `X86/Typen.lean` `Flags.af = none`; IR-VALIDIERUNG at base contains no
     `asm` mention (finding §6.2 confirmed); QUELLBRUECKE §4 takes no
     refinement premise in `schluss_x86` and binds full-unit `hE`
     (lines 363-399); IR-VALIDIERUNG §2.4 binds `lowerOk(E, G0)`, per-step
     `check_C`, `layoutOk(Gn, B, Img)`; IMAGE-ABI §11 states the
     three-conjunct external-body rule (lines 448-465).
4. Checked historical-baseline discipline: all absence/coverage claims in the
   three documents are dated to the pinned base (294 §5 table "at `f4958150`",
   293 §1 "checked against the tree on branch `muse/293` (base `f4958150`)",
   292 §0 anchors + CUTS "valid at this commit only"). Modules merged after the
   base (`X86/Ganzzahl`, `TSO`, `Bild`, `Ausfuehrung`, `SpeicherKommutation`,
   `FlagBeweis`, FLOAT-ZEIT, lanes 281-285/289) therefore do not contradict any
   claim. No undated current-coverage claim that has become misleading was found.
5. Checked for whole-chain overclaims: none. 292 §11, 293 CUTS, 294 §§7-8 each
   explicitly refuse source-to-IR/binary closure and separate proved
   (pilot vocabulary, word/memory helpers, budget arithmetic-with-cuts, bridge
   theorems) from specified-only (execution, codec, SCFG, lowering, TSO bridge,
   image checker, FP/time, optimiser rules, closing theorem). Counterexamples
   (292 C1-C8, 293 traces A/B/C + interleaved exchange, 294 CE-1..CE-6) are
   presented as witnesses that the refusals are necessary, each with a named
   refusing clause — the mechanisms I re-checked (Befehl set, preExpr erasure,
   hyps/postU refusal, budget cuts, Folge order) support exactly that reading.

## Precision note (not a defect, no author correction required)

293's report compresses the `schwach_ist_gX` premise list as
`(hO hvoll hAbg hWurzel hI hr)`; the actual signature at the base also carries
`hFuss` (`FussSX`), `hlokK` (`GetrenntK`), `hTA` (`AtomarAusgenommen`) and `hex`
(`StartExklusiv`). The material claim (no `KoerperGutSA` premise) is correct,
and the review document itself (§8 step 5) books `hTA` and `FussSX` as explicit
wave-B obligations, so nothing unsound is licensed and no finding is weakened.
Recorded here for anchor hygiene only.

## Exact names of new definitions/theorems

None. Docs-only counter-review: no Lean definition, theorem, or witness added;
no existing file modified. No diagnostic, gift, example, CLI, or MARKE number taken.

## Last `./lean-bau` result line

Not run: no Lean file touched (`git status` shows only this report as untracked
at write time); per the lane task ("use queued `./lean-probe` only if needed to
reproduce a precise mathematical finding") no build was needed — every finding
above is by reading cited definitions at the pinned base.

## What remains open

- All phase-B constructions stay unbuilt by these candidates (by design):
  execution semantics, decoder, SCFG + rule register, source-computed exports,
  lowering map, per-access TSO table, validator + `valX86_sound`, ghost
  call/return and budget correspondences, binding/kernel contracts.
- The 294 §6 precisifications (asm-lowering sentence, C1/C5 citation,
  spill-escape cross-reference) and the 293 §5.2 single-owner recommendation for
  `accessList(rule)` belong to the owning lanes, not to these reviewers.

## Anything believed wrong in the task or sources

Nothing material. The task's date/baseline discipline matches what the authors
did; no source unsoundness was found in the course of counter-review (all risks
identified by the three candidates sit on the consumer/schema side, correctly
marked refused or OPEN).

CANDIDATE: 292 0e54300346132acb1ca5a47e623172694c0ba205
CANDIDATE: 293 ac45a5a5170a6695c48302849c4cc3265c96c6a9
CANDIDATE: 294 961c6e00b3db3dd93666eaa45742999703704e14
VERDICT: ACCEPT
