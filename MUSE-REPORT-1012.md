# MUSE-REPORT-1012: exact review of author 862 (CFG simplification rule)

## Identity

- Clone `/home/simon/Dokumente/gabbro-muse/a1012`, branch `muse/1012`: verified, match.
- Review material (pinned, clone-local): `.tmp/review/SNAPSHOT.json`,
  `.tmp/review/author-862/{OWNER-TASK.md,PATCH.diff,MUSE-REPORT-862.md,BUILD-EVIDENCE.json,grammatik/...}`.
- Base of this clone is `b040b155`, the snapshot's recorded base. No source
  outside `MUSE-REPORT-1012.md` was touched; no other clone, no network, no push.

## Verdict

- CANDIDATE: 862 0eb5dbddfd2e940178074571d7af5b5c3fd28cea
- VERDICT: ACCEPT (bounded; bounds in "Acceptance bounds" below)

## What the candidate is

New file `grammatik/Grammatik/X86/OptCfgSimp.lean` (379 lines) plus one import
line in `grammatik/Grammatik.lean`. Owner task (lane 862): DESIGN section 7
row for CFG simplification — local premise "unreachable edge proof (decided
const cond), exit edges preserved", certificate "B block map", failure case
"delete a `narrow`-else edge", phase E. Targets `OptCfgSimp_verbindung` and
`OptCfgSimp_verbindung_zeuge` both exist with those exact names.

## Checks performed (independent, against base tree + snapshot)

1. **Task fidelity / scope.** Only the three owned files in PATCH; no
   diagnostic/gift/example/CLI numbers, no MARKE_EMIT, no source/checker/Spec/
   goal/emitter edits, no friend-reserved optimiser files. Imports are
   canonical only (`Typen`, `Syntax`, `Semantik`, `ReferenzB`,
   `X86.InvariantenOpt`). The structural model cited (`OptFoldConst.lean`)
   exists and the witness/cert/refusal shape follows it.
2. **Reused-lemma reality.** Every soundness-bearing step delegates to a real
   accepted lemma verified present in this base with a matching signature:
   `InvariantenOpt.isWahrAll_sound` (lines 140-141),
   `exec_ite_wahr` (228-235), `exec_pruefung_wahr` (215-223), `isWahr` (62),
   `wCond` (362), `wit_isWahr` (406). Reference-program facts
   `refD`/`refEin_schreibt`/`refB_erreicht`/`refB_schreibt`/`refO`/`refSp0`/
   `refP`/`MB`/`initB`/`keinRuf`/`vertragVon`/`Expr.wahr`/`Block.nil`/
   `Endblock.leave` all verified present with matching statements.
   In particular `isWahrAll .wahr = true` holds definitionally (first match
   arm), so the witness's `hBruecke := rfl` is a genuine recomputation, not a
   trusted hint.
3. **The one non-trivial inference.** `narrowSonst_erreichbar` closes by
   `simp [execBlock, hAussen]`; the base equation
   (`Semantik.lean:852-856`) sends exactly the out-of-range case to
   `(execEnd sonst σ ρ).zuAusgang` in the post-read world, which is what the
   theorem states. Sound, and it makes the `narrow`-else refusal load-bearing
   rather than decorative. There is deliberately NO theorem deleting a
   `narrow` else.
4. **Premise use.** `hZul` and `hBruecke` are both consumed (decided-bit
   extraction through the conjunction, then rewrite). The exit/narrow bits do
   not enter the equation — they gate *firing* via `hZul`, proved by the
   refusal legs. The author documents this division (section-5 header); a
   semantic exit-edge premise over arbitrary blocks would need the block-map
   vocabulary that is still OPEN (lane 287), so forcing it into the equation
   would be fake closure. No `intro _` / `have _ :=`, no `Prop`-typed
   premises, no quantified-away contracts, no derived `ensures`, no
   refusal-to-warning. Forbidden-token scan of the snapshot file is clean
   (hits are only English words like "admitted" and `#print axioms` lines).
5. **Witness (HARD RULE 13).** `OptCfgSimp_verbindung_zeuge` binds ALL
   premises jointly on non-degenerate `refD` (table written:
   `refEin_schreibt ()`) beside the reached memory-changing run
   (`refB_erreicht`, `refB_schreibt`: slot 0 changes). The `_hZul`/`_hBruecke`
   underscore naming matches the accepted `OptFoldConst` house pattern for
   provided existential premises — both are provided (`by decide`, `rfl`),
   not discarded. The `ite`/`pruefung` instances use `nil` branches, which is
   fine: non-degeneracy attaches to the program and the run, both present.
6. **Negative mutations.** All three refusal legs proved
   (`cfgVerweigert_unentschieden/austritt/narrowSonst`) plus three `decide`
   probes and the `probe_cfgEntscheidung` reuse of the accepted `wCond`
   witness. The DESIGN failure case (narrow-else deletion on "range hope") is
   refused AND exhibited live. No weakened guarantee: the connection is an
   outcome equality, not a refinement.
7. **Hardware checklist.** This candidate is source-level
   (`Syntax`/`Semantik` fragment, per the owner task's explicit staging); it
   touches no byte form, REX/register/width, flag, TSO/atomicity, feature/
   MXCSR/interrupt gate, so those checklist items are N/A by construction,
   not evaded. What the checklist demands in spirit is honoured: firing
   consults boolean truth only (never float rounding/NaN — `isWahrAll`
   answers `false` on non-literal shapes by design), the faulting form
   (`narrow` else) is never speculated above its guard, no memory access is
   added/removed (kept branch verbatim, identical `c.orte` read, same `R`,
   same `passes`), and no determinism over undefined hardware state is
   invented. Correspondence honestly stops at source outcomes (see bounds).
8. **CUTS/claim boundary.** Precise: no block-map checker, no narrow-else
   rewrite, no level-(c) cost transfer, no `FolgeG`/TSO-GX legs, no silicon/
   ABI/loader claims. The author report's "0 errors, 0 warnings / 511 jobs"
   matches the final BUILD-EVIDENCE entries (intermediate probes showed
   unused-name warnings that the final `_c`/`_e`/`_sonst` naming resolves;
   final probe and `lean-bau` show the full axiom printout, every theorem
   within `[propext, Classical.choice, Quot.sound]`). Axiom conformance
   independently plausible from the proof terms (all `rfl`/`simp`/`exact`
   over accepted lemmas); exact `#print axioms` lines are in the evidence log.

## Minor notes (not verdict-relevant)

- Report says "~380 lines"; the file is 379 lines. Cosmetic.
- `cfgFehler_logik_bleibt` / `cfgFehler_hardware_bleibt` are thin corollaries
  (rewrite + exact). Genuine, and the spelled-out two-channel form is what
  the owner task asked for — not fake closure.
- Call-log/concurrency/budget/contract preservation is argued via outcome
  equality in the section-4 header, not as separate formal legs; the formal
  legs stay OPEN per CUTS. This matches the task's ZEUGE requirement exactly,
  so it is a bound, not a gap.

## Acceptance bounds

ACCEPT covers: validator-decided admission with all three refusal legs,
decided-boolean firing over arbitrary conditions, verbatim executable
rewrites, source-outcome equality on `ite` + `pruefung` shapes with both
fault channels spelled out, and the joint non-degenerate witness. It does
NOT cover: validator-side block-map recomputation, level-(c) machine-work
transfer, whole-unit `FolgeG`, per-access W/GX refinement, or any
silicon/ABI/loader claim — all OPEN per CUTS and out of scope for this rule
lemma.

## Verification performed by this reviewer

- No local build was run: this lane owns no source and the review task
  forbids touching source or live controls; reproducing the build would mean
  applying the candidate patch in this clone. Verification is by inspection
  of the pinned snapshot against the base tree (all reused definitions and
  both semantic equations read directly) plus the complete queued-wrapper
  evidence (probes incl. one intermediate 2-error state that was repaired,
  final 0-error probes, green `lean-bau`, commit record at the pinned HEAD).
  No suspicious case requiring reproduction was found.
- `git status` in this clone is clean except this report.

## Task remarks

Nothing in the lane-1012 task appears wrong. The hardware checklist reads as
if every candidate touched bytes; for source-level rule lemmas like this one
the correct application is the spirit-check in item 7 above, which the
candidate passes.
