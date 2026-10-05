# MUSE-REPORT-1234 — Exact review of candidate 1233 (Pipeline work bounds for branches and loops)

Lane 1234 (branch `muse/1234`, clone `/home/simon/Dokumente/gabbro-muse/a1234`).
Report-only independent exact review.

CANDIDATE: 1233 25d2000a1621b70e133135714785e22cf4893240

Reviewed artefact (base `cbc0afe00eeb8708961b13489750e41e998740d1`,
from `.tmp/review/SNAPSHOT.json`): the snapshot
`.tmp/review/author-1233/` (`PATCH.diff`, `PipelineWorkBranches.lean`,
`MUSE-REPORT-1233.md`, `BUILD-EVIDENCE.json`, `OWNER-TASK.md`).
Own file: only this report. No source files touched.

VERDICT: ACCEPT

## What was checked (candidate diff only)

Files in candidate: `MUSE-REPORT-1233.md` (new), `grammatik/Grammatik.lean`
(one appended import line), `grammatik/Grammatik/X86/PipelineWorkBranches.lean`
(new, 446 lines). No other file touched. Matches the owner task's OWN ONLY list.

1. **No sorry/axiom/native_decide.** Grepped the snapshot Lean file:
   matches are only the words "admitted" (prose: "admitted summary maximum",
   "admitted pipeline summary") and the 21 `#print axioms` lines. No
   `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `sorryAx` as tactics
   or declarations. BUILD-EVIDENCE shows the author ran
   `pruefe-kein-sorry.py` per the report (0 violations claimed; the raw
   command output is not in the evidence JSON, so this leg rests on the
   report claim + my grep, not on a re-run — see § Honest limitation).
2. **Axioms standard.** BUILD-EVIDENCE's `#print axioms` pass lists every one
   of the 21 constants as a subset of `[propext, Classical.choice,
   Quot.sound]` (defs and `decide`/`rfl` witnesses use none/fewer; the main
   transfer and the joint witnesses use the full standard triple). No
   non-standard axiom in the evidence.
3. **Existing files untouched except one import line.** `PATCH.diff` shows
   exactly one added line in `grammatik/Grammatik.lean`
   (`import Grammatik.X86.PipelineWorkBranches`, appended at the end) and
   nothing else outside the new file + report.
4. **Every premise used (spot-verified).** `deckung_von_laenge`,
   `pruefeZweig_korrekt`, `deckung_ite` thread their hypotheses into the
   conclusion; `schleife_budget_transfer` uses `m` in both sides and `h` in
   `Nat.mul_le_mul_right`; `zweig_arbeit_korrekt` uses all of
   `hc hsep hcode hf hrip hW hE hval hCost hb hk` (run / derived coverage /
   work / time legs). No `intro _`, no discarded hypothesis, no `Prop`-typed
   premise in the new file.
5. **Accepted evaluator lifted, not copied.** `zweig_arbeit_korrekt` reuses
   `senkBlock_korrektC` as a black box, `pipeSummary`/`pipeSummary_expand`,
   `decodiertZu`/`arbeit_decodiert`, `Deckung`/`budgetAusfuehrung_transfer`,
   `validate_sound`, `decodeAll_encodeAll`, `kompiliert_geladen`/`imageOk_*`,
   and the `pd`/`pw` witness packages. No second interpreter, no second IR,
   no optimiser edit. `iteCode`/`iteSchranke` are stated over the accepted
   `Pipeline.lean` shape; `schleifeSchritte` is the accepted
   `PipelineLoops.lean` def (`runden * (m + 2) + 1`, confirmed in-tree),
   and the transfer proof matches it.
6. **Planted refusals really refuse.** `gift_zweig_knapp`/`gift_zweig_ok`
   are decided length checks on `pdProg.drop 17`: `pdProg` in-tree is 34
   instructions (9 chunk + 8 check + 17 ite), so the drop-17 slice is exactly
   the 17-instruction ite lowering; 17 ≤ 12 is false, 17 ≤ 18 is true —
   boundary fires by `decide`. `gift_retry_sieben` (bound 7 vs PipeBlock's
   bound-5 instance) and `gift_forever` close by the generic refusal lemmas,
   which are `rfl` over `senkBlock`'s catch-all arm (`| _, _, _, _, _, _ =>
   none`, confirmed in `Pipeline.lean` lines 1451–1477) — a genuine
   generalisation, not a copy.
7. **Witness non-degenerate.** All three `_zeuge` theorems conjoin the
   refusal/transfer claim with the accepted `PipePaket`/`pipePaket_hold`
   (one table its contract writes; source run moving slots; fetched-byte run
   observably changing memory — confirmed in `PipelineWork.lean` 602–623).
   `zweig_arbeit_korrekt_zeuge` additionally pins the `x = 30` then-branch run
   through actual `execBlock` with memory-changing rows plus validator,
   cost, image and run facts jointly. No empty-run or table-free witness.
8. **Silicon facts.** No new encodings, no new fault classes, no ordering
   claim. Byte facts flow through the accepted `encodeAll`/`decodeAll` and
   per-form `schrittKosten` via `budgetAusfuehrung_transfer`; the 14-arm
   `Befehl` case split reuses the accepted cost table shape. Nothing to check
   against the SDM extracts beyond reuse, which is correct.
9. **CUTS honest; no claim larger than the proof.** The file's CUTS openly
   states: coverage counts the static whole-list length (dynamic-path bound
   is arithmetic only); loop work stops at the labelled-step budget with the
   body/bytes legs left to `PipelineLoops`; no entry/mapping, no
   TSO/concurrency, timing stays a named hardware assumption. In particular
   no hardware-correspondence or W/GX claim. The author report's "honestly
   weaker in one place" note matches the file. This is the correct scope for
   an ACCEPT.

## Two doc nits (not verdict-changing, noted for the merger)

- The author report says "`Vertrag` spelled capital here"; the snapshot file
  line 41 actually uses lowercase `vertrag D`, matching the tree. Stale note,
  no proof effect.
- CUTS line for the `x = 30` witness says rows "`7 -> 65` and `9 -> 6`";
  the theorem proves `(slots 0).n = 65 ∧ (slots 1).n = 130`. The `9 -> 6`
  figure belongs to the base `PipePaket`, not this run — should read
  `9 -> 130`. Typo only; the formal statement is what merges.

## Honest limitation of this review

- `./lean-bau` was NOT re-run by me: the `bash` tool call needed for the
  queued wrappers was permission-denied in this session (first attempt
  rejected), so there is no fresh independent build line from lane 1234.
  Acceptance rests on: (a) the candidate's snapshot BUILD-EVIDENCE
  (`./lean-probe … == 0 error(s); exit 0` final, `./lean-bau … Build
  completed successfully (641 jobs)` at the pinned HEAD, with the two
  transient `failed to read file` olean-contention failures documented as
  cleared on retry with no proof change); (b) my own grep/read checks above
  over the exact snapshot. A serial integration build before merge remains
  required per the standing gate and is not replaced by this verdict.
- `./lean-probe` likewise not re-run, for the same reason. No Rust scope in
  the candidate (none claimed, none present). No `cargo`/emission checks
  applicable.

## Remaining open (carried, not opened by me)

Per-path retired-work connection of `itePfad_schranke` to a taken-path `lauf`
prefix; per-round body correspondence and labelled-to-bytes leg for loops;
entry/image admission beyond `Pipeline.CodeAt`; all concurrency/time scoping
as in the file's CUTS. Nothing here weakens a guarantee to gain coverage.
