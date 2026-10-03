# MUSE-REPORT-1038: Exact review of author 888 (multiply selection rule)

## Task

Review exact author 888 (Optimiser rule: multiply selection rule).
Report-only: own only `MUSE-REPORT-1038.md`. No source or live-control changes.

## CANDIDATE

CANDIDATE: 888 7fc61948fe48ccc3f9babee883ede90465fda07d

Source: `.tmp/review/author-888/` (pinned snapshot `SNAPSHOT.json`: base
`b040b155159f47629542b0083e2f0a8a607f2b4c`, files `MUSE-REPORT-888.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/OptMulSel.lean`, clean tree).
The three-file scope matches the owner's owned-files list. No other files in
the diff.

## VERDICT

VERDICT: ACCEPT (bounded — see claim boundary below).

## What was checked

1. **Scope hygiene.** `PATCH.diff` touches exactly three files: one new Lean file
   (461 lines), one appended import line (`import Grammatik.X86.OptMulSel` after
   `ComposeImageFetch`, which is the tail of `Grammatik.lean` at base), and the
   author report. No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes,
   no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files
   (`OptimizationRules.lean`, `OptimizationWitnesses.lean` untouched).
2. **Mechanical hygiene.** The staged file contains no `sorry`, `admit`, `axiom`,
   `native_decide`, `unsafe`, and no `intro _` / `have _ :=` discards
   (verified by search over the staged copy). Every theorem premise occurs in
   its goal; proofs never drop a binder. No `ensures` derived; no refusal turned
   into a warning; `div`/`sdiv`/`srem` appear nowhere.
3. **Build evidence.** `BUILD-EVIDENCE.json` records the queued-wrapper trail:
   final `./lean-probe grammatik/Grammatik/X86/OptMulSel.lean` reports
   `0 error(s)`, and final `./lean-bau` reports `Build completed successfully
   (511 jobs)`. The trail honestly shows intermediate red probes during
   development (unknown-identifier and implicit-argument errors), all resolved
   in the pinned snapshot. All listed `#print axioms` outputs are subsets of
   the standard goal set (`propext`, `Classical.choice`, `Quot.sound`).
4. **Reference fidelity (DESIGN).** All three DESIGN citations are real at base
   (`DIRECT-COMPILER-DESIGN.md`): §3A tile "3-operand `IMUL r, r/m, imm8/imm32`
   for constant multiplies with a proved range" (line 336); §7
   strength-reduction row "per-width flag/fault identity lemma (CF vs OF
   distinct) | A register rule | `imul r,8 → shl r,3` with live CF; ...
   `a*2.0 → a+a`" (line 518); CE-6 refusal "`imul r,8 → shl r,3` with live CF —
   same value, different flags" (line 552). The four `MulSelCert` fields, the
   `MulSelZert` shape ("local rewrite record plus recomputed analysis
   citations"), and the CE-6 selector refusal (`waehleShift_verweigert_live`)
   map one-to-one onto that row.
5. **Canonical vocabulary.** Every reused name resolves at the candidate's base
   (verified in this clone): `mulLow`/`mulHighU`/`mulTragU`/`mulTragS`/
   `mulLow_b64` (`Ganzzahl.lean`), `mulFlagsS`/`mulFlagsS_gueltig`/
   `MulGueltigS` (`MulDiv.lean`, `Ganzzahl.lean`), `shlW_keinUeberlauf`
   (`StaerkeReduktion.lean`), `imin`/`imax` (`Typen.lean` — plain
   `if`-definitions, so the `imin_selbst`/`imax_selbst` unfold+split proofs are
   genuine), `eval_weiter_n` (`InvariantenOpt.lean`, confirming the report's
   `weiter`-transparency note), and the witness apparatus `refD`/
   `vertragVon`/`refO`/`keinRuf`/`refP`/`refSp0`/`initB`/`MB`/
   `refEin_schreibt`/`refB_erreicht`/`refB_schreibt` (`ReferenzB.lean`,
   `Syntax.lean`, `Maschine.lean`).
6. **Target theorems.** `OptMulSel_verbindung` (generic over `x k : Int`, real
   `Syntax`/`Semantik` `execEnd` fragment at an arbitrary `Endblock.bind`
   continuation) and joint companion `OptMulSel_verbindung_zeuge` are both
   present under exactly the `ZEUGE:` names. The witness instantiates all
   premises jointly at `6 * 7 → 42` on non-degenerate `refD`
   (`refEin_schreibt`) beside the reached memory-changing F-machine run `MB`
   (`refB_erreicht`, `refB_schreibt`, slot `0 → 100`). The `_hW` binder is
   inhabited by a real proof (`by decide`), not discarded.
7. **Negative cases.** Four refusal theorems (range / imm / flags / float) plus
   decide-probes for admission, range-hope, imm-misfit and float-taint; the
   CE-6 live-flag shift refusal and the refused-certificate shift refusal; the
   sign probe `mulTragU .b8 0xFF 0xFF = true ∧ mulTragS .b8 0xFF 0xFF = false`
   (unsigned carry set, signed clear — the stated reason CF vs OF need distinct
   rows) is decided by computation, not asserted.
8. **Precedent.** The `verbindung` + `_zeuge` shape over `execEnd` fragments with
   a CUTS block follows the accepted sibling `X86.OptFoldConst` pattern.

## Claim boundary (bounded acceptance)

The connection's `execEnd` equality is definitional (`rfl`) at the SOURCE level:
both sides are source `Expr`s (`lit (x*k)` vs `weiter`-widened `mul` of lits),
so value/fault/observation preservation follows from proved source-fragment
identity plus the width-exact word read-back. The target `Imul3` form is NOT
executed by `schritt` anywhere — its value/flag facts hold over the canonical
word vocabulary (`mulLow`/`mulFlagsS`/`mulTragU` rows cited, not restated), and
byte encoding plus `Befehl`/`schritt`/decoder/image wiring is declared OPEN in
CUTS. That gap is forced by scope (the pilot `Befehl` has no multiply form;
wiring would require editing non-owned canonical files) and is stated
precisely rather than bridged by assumption. Likewise TSO/GX beyond
non-interference, the level-(c) machine-work bound, float selection, and
silicon correspondence stay OPEN per CUTS. Nothing in the file overclaims them.

## Minor notes (not verdict-changing)

- `waehleShift_verweigert_live` leaves `flagsLive` to autoImplicit (an implicit
  binder rather than an explicit parameter). It elaborates and proves the
  claimed refusal; style-only.
- There is no `decide`-probe for the `flagsOk = false` admission case (bereich/
  imm/gleit each have one). Covered by theorem + selector lemmas regardless.
- The section-5 comment mentions `orte = []` on both sides, but no explicit
  `orte` fact appears in the formal statement; access identity follows from the
  proved outcome equality. Comment precision only.

## Reproduction note

Independent re-execution of the queued wrappers from this lane was not possible
without touching non-owned files: the candidate lives staged under
`.tmp/review/author-888/` (outside the `grammatik/` tree, so `lean-probe`
cannot resolve its imports there), and this lane owns only the report. The
verdict rests on the pinned `PATCH.diff` inspection above plus the author's
complete queued-wrapper trail in `BUILD-EVIDENCE.json` (final 0-error probe,
511-job green build, standard axioms).

## Remaining work (not this lane's)

Byte codec + `Imul3` wiring into `Befehl`/`schritt`/decoder/image (Codec lane),
TSO/GX bridge, level-(c) work bound, and the final source-to-loaded-byte
closing theorem (validation lanes).
