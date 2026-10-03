# MUSE-REPORT-1026: Exact review of author 876 (flags peephole rule)

CANDIDATE: 876 86f151ffe0b878dd83acfdb1259f3cbc06e010ac
VERDICT: ACCEPT (bounded, source-level rule lemma; no byte/TSO/silicon claim)

## Scope of this review

- Reviewed the exact pinned snapshot from `.tmp/review/SNAPSHOT.json`
  (author 876, head `86f151ff...`, base `b040b155...`, clean, 3 files),
  the exact `OWNER-TASK.md`, `MUSE-REPORT-876.md`, `PATCH.diff`, and
  `BUILD-EVIDENCE.json` in `.tmp/review/author-876/`.
- Independently inspected the live tree for every architectural anchor:
  `X86/Ausfuehrung.lean` (`schritt_subReg64` sets flags),
  `X86/ExpressionLowering.lean` (source `.sub` lowers to
  `Befehl.subReg64`), `X86/Codec.lean` (`roundtrip_subReg64`),
  `X86/Zugriffe.lean`, `X86/FlagBeweis.lean`, `X86/FlagDependencies.lean`,
  sibling `X86/OptFoldConst.lean`, `ReferenzB.lean` witness fixtures,
  and `HARDWARE-REFERENCES/REFERENCES.json` (Intel SDM 325462-093US,
  verified 2026-10-02; no AMD snapshot available).
- Own only this file. No source touched, no patch applied in this clone
  (applying it here would measure my base, not the candidate), no live
  control files modified. No re-run of the candidate build in this clone
  for that reason; build evidence below is the pinned author evidence
  plus independent PATCH-level verification of every claim I accept.

## What the candidate does

- New file `grammatik/Grammatik/X86/OptPeepholeFlags.lean` + one import
  line in `grammatik/Grammatik.lean` + report. Owned-files, number, and
  reserved-file discipline clean: no diagnostic/gift/example/CLI numbers,
  no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files.
- Rule: cert-gated rewrite `sub (.lit x) (.lit x)` to `.lit (x - x)`
  over arbitrary `x : Int`, gated by `FlagPeepholeCert`
  (`flagTot`, `ganzzahlig`, `keinFMA`) via `peepholeZulassen`
  (conjunction). Refusal is identity (`umschreibenVerweigert_identitaet`),
  never a warning.
- TARGET `OptPeepholeFlags_verbindung`: at an arbitrary
  `Endblock.bind` continuation, the admitted rewrite preserves the
  evaluated bound value, the full `execEnd` outcome (same constructor,
  worlds, environments), the peephole result `x - x = 0`, and the
  canonical-word image. ZEUGE `OptPeepholeFlags_verbindung_zeuge`
  instantiates all premises jointly on `refD` (`5 - 5` to `0`,
  admitted cert, `leave` continuation) beside the memory-changing
  reached run (`refEin_schreibt`, `refB_erreicht`, `refB_schreibt`).

## Architecture checks (independent)

- Flag soundness: CONFIRMED load-bearing and correctly NOT proved here.
  `schritt_subReg64` sets `flags := (sub64 ...).2` and lowering emits
  `subReg64` for source `.sub`, so dropping the `sub` drops a real flag
  write. The candidate proves source-level `execEnd` equality only
  (the source model has no flags) and carries flag-deadness as the
  validator-recomputed `flagTot` citation. CUTS state exactly this
  ("no target-machine liveness fixpoint", validity "exactly under that
  citation"). No invented determinism, no zeroed/ignored defined effect:
  the effect is named, cited, and cut. Any consumer that fires this rule
  without recomputing liveness would be unsound, but that obligation is
  placed on the validator by the certificate shape, which is the DESIGN
  section 7 pattern the owner task ordered.
- Width: `hW : 0 <= x - x /\ x - x < 2 ^ 64` is redundant in the strict
  sense (`x - x = 0` always satisfies it) but it is USED (feeds
  `subSelbst_wort`), proved by `decide` at the witness, and harmless.
  Not a desired-correctness assumption: it is dischargeable, not
  load-bearing. No weakening, no repair warranted.
- IEEE: float refusal grounded by the kernel-model pin
  `subSelbst_float_kein_null` (quiet NaN minus quiet NaN is quiet NaN,
  not zero, by `decide`). No float fold is claimed. Correct.
- FMA: no fused op exists in the model; refusal is certificate-level
  (`keinFMA`) and CUTS say the one-vs-two-rounding equality "is not
  stated and not claimed". Correct boundary.
- Faults: integer `sub` on literals is total; `execEnd` equality is by
  `rfl` after firing (`hfire`), so no fault is added/removed and no
  guard is speculated above. Correct.
- Memory/concurrency: both sides have `orte = []` (by `rfl`), so no
  shared access is added or removed; the `bind`-window `execEnd`
  equality with arbitrary `rest` covers downstream contracts (same
  values in same environments), call logs (world untouched), and
  concurrency observations at once. Budget: `subSelbst_kosten`
  (`kostenExpr` literal `<=` removed `sub`, by `simp`); the formal
  level-(c) machine-work bound is left OPEN in CUTS. Precise.
- Byte/REX/register/TSO/MXCSR/interrupt gates: none claimed, all cut
  ("correspondence stops at canonical words and kernel-model floats",
  "no silicon correspondence, no TSO/GX bridge, no ABI/loader claim").
  `Codec.roundtrip_subReg64` and decoder soundness probes exist in-tree
  but are correctly NOT cited as execution correspondence. Bounded
  acceptance only; this is a source-level rule lemma in the same shape
  as the accepted sibling `OptFoldConst.lean`, not a byte-connected
  target rule.

## Mechanical checks

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere in the
  PATCH (verified by inspection; only `#print axioms` lines). No
  `Prop`-typed premise. Every premise is used (refusal hyps in `simp`,
  `hz` in `hfire`, `hW` in `subSelbst_wort`, all bind parameters in
  the connection conclusion). The witness's `_hz`/`_hW` names match the
  accepted sibling pattern: both are provided by `decide` as
  existential components beside the memory lemmas; nothing is
  discarded with `intro _`.
- Axioms: pinned evidence prints every theorem under subsets of
  `[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel`
  standard); the two TARGET/ZEUGE theorems use the full triple, same
  as the sibling. No axiom violation.
- Witness is non-degenerate: `refD` with a written table
  (`refEin_schreibt`) and a reached F-machine run that changes memory
  (`refB_erreicht`, `refB_schreibt`, slot `0 -> 100`). Verified the
  fixture names exist in `ReferenzB.lean` (lines 51, 123, 329, 910,
  987, 1007). Negative mutations present: admit/live/float/FMA
  probes, NaN pin, refusal-identity theorem.
- Build: pinned `BUILD-EVIDENCE.json` shows `./lean-probe` ending
  `== 0 error(s)` and `./lean-bau` `Build completed successfully
  (511 jobs)` on the candidate branch, including the new module
  import; intermediate `unsolved goals` entries are development
  history, final state green. `CUTS:` block plus per-theorem
  `#print axioms` present at file end per hard rule 6.
- No guarantee weakened: no `ensures` derived, refusals stay refusals,
  checker ranges (`weiter`/`narrow`) untouched and still enforced at
  the site per the section 6 doc string.

## Bounded acceptance (what ACCEPT does and does not cover)

ACCEPT covers: the literal-operand `x - x`-to-`0` source peephole with
validator-cited admission, value/outcome/zero/word-image preservation,
the three DESIGN refusal cases with probes, the IEEE NaN pin, and the
joint non-degenerate witness. It does NOT cover: machine flag
preservation (needs a recomputed liveness fixpoint), general
`.sub e e` over memory-reading operands (explicitly cut: `lese`
traces differ), float folding, FMA one-vs-two rounding, machine work
bounds, or any byte/TSO/silicon/ABI claim. The generalisation to
non-literal same-value operands is the sharp, honest boundary of this
lemma and must stay cut until a trace-aware formulation lands.

## Task feedback

Nothing in the owner task believed wrong. The "generic rule lemma over
arbitrary values" requirement is met as genericity over arbitrary
`x : Int` with the literal-operand shape by construction (same reading
as sibling `OptFoldConst`); the `lese`-trace restriction to literals
is a genuine, correctly recorded finding, not a silent weakening.

## Last build result (this clone)

No build run in this clone: report-only review, and this clone is at
the base without the candidate file, so any local `./lean-bau` would
measure the wrong tree. Candidate build evidence is the pinned author
record above (`lean-probe == 0 error(s)`, `lean-bau 511 jobs`
success). This report is the only file owned and the only file changed.
