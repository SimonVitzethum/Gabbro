# MUSE-REPORT-375: Independent exact-candidate A3 review of 337 ShiftLogic

Reviewer lane 375, branch `muse/375`, clone `/home/simon/Dokumente/gabbro-muse/a375`.
Owns ONLY this file; the candidate was staged privately and fully restored before this commit.

CANDIDATE: 337 a4d1329fe89569e409d8b285f3acf810e7dc9a7a
VERDICT: ACCEPT

ACCEPT covers only the precise bounded delivered obligations (NEG + per-shift/logic
flag evidence over reused canonical ops, count-mask pins, the three named refusals,
the joint memory witness, the §7 future-form interface), not the full compiler,
source correspondence, silicon behaviour, TSO/GX bridge, cost transfer, or any
final-byte/hardware acceptance, all of which the candidate keeps OPEN in CUTS.

## What was inspected

- Exact snapshot: `.tmp/review/author-337` — `SNAPSHOT.json` (head
  `a4d1329fe89569e409d8b285f3acf810e7dc9a7a`, base `f737a6f0`, clean, 3 files),
  `OWNER-TASK.md`, `PATCH.diff` (only `MUSE-REPORT-337.md`,
  `grammatik/Grammatik.lean` one additive import, new
  `grammatik/Grammatik/X86/ShiftLogic.lean` 467 lines), `BUILD-EVIDENCE.json`,
  `MUSE-REPORT-337.md`, and the supplied `grammatik/` file (sha256
  `1946c5c9d5c7894ab994dff8d6918dfc6bf8a70978e4a48698474cf7dc74dac7`).
- Actual accepted sources in my clone: `Ganzzahl.lean` (`andB`/`orB`/`notB`,
  `and64`/`or64`, `sVal`/`sMin`/`divS`, `schiebeZaehler`, `shlB`/`shrB`/`sarB`,
  `LogikGueltig`, `SchiebeNachweis`/`SchiebeGueltig`, `schiebe_gueltig_existenz`,
  `andB_b64`/`orB_b64`), `Wort.lean` (`negB`, `subB`, `afSub`, `zfTest`,
  `sfTest`, `parityEven`), `Speicher.lean` (`write64`/`read64`/`zeugenSpeicher`,
  `writeBytesN_hit`, `read64_nach_write64`, `addrOff_null`),
  `StaerkeReduktion.lean` (`sdiv_kein_shift`, `shlW_keinUeberlauf`),
  `Gleitkomma.lean` (`f64`, `sub`, `nanQ`, `nullP`), `Gleitprofil.lean`.
- Staged the candidate module plus additive umbrella import privately in my
  tree (base drift noted below), ran the queued wrappers, then restored both
  paths: `git status --short` is empty before this report commit.

## Verification reproduced

- `./lean-probe grammatik/Grammatik/X86/ShiftLogic.lean`: 0 errors. All
  `#print axioms` are subsets of `[propext, Classical.choice, Quot.sound]`.
- `./lean-bau`: `Build completed successfully (387 jobs)` (author saw 386;
  my tree has one extra module, `SpillPrivate`, from newer master).
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`: 0 errors;
  `gabbro_ziel` on exactly `[propext, Classical.choice, Quot.sound]`.
- Banned-token grep (`sorry|admit|axiom|native_decide|unsafe`): no hits in
  the candidate file. No `Prop`-typed premise. No redefinition of `Befehl`,
  `schritt`, `SchiebeGueltig`, `LogikGueltig`, value ops, or memory ops.
  No off-limits paths touched (no checker/Spec/goal/emitter/docs/friend files).

## Task-direction coverage (checked against actual definitions)

- Target: SHL/SHR/SAR/AND/OR/NOT/NEG with `schiebeZaehler` masking (6 bits at
  b64, 5 bits narrow — matches `Ganzzahl.lean`) and per-op flag facts. NEG
  CF (`trunc ≠ 0`) and OF (`sVal = sMin`) match the architectural contract;
  NEG AF (`afSub 0 (trunc b x)`, i.e. low nibble of operand nonzero) matches
  the `0 - x` borrow; SHL carry bit `bits - k`, SHR/SAR carry bit `k - 1`,
  SHL OF = sign change, SHR OF = original sign, SAR OF = false, all gated on
  masked-count-one with `none` elsewhere — consistent with the reused
  `SchiebeGueltig` and Intel's OF discipline. Logic snapshots clear CF/OF
  with AF `none`, agreeing with `and64`/`or64` at full width (proved).
- Witness: `shift_maskiert_speicher_zeuge` pins `shlB .b64 1 66 = 4`
  (masked count 2), carry `false`, result `4`, jointly with a real
  `write64`/`read64` roundtrip through `zeugenSpeicher` (zeroed bytes, so
  byte 0 `0x00 → 0x04`). Nonzero word, memory observably changed,
  non-degenerate. The proof follows the accepted `Speicher.lean` witness
  pattern (`read64_nach_write64`, `writeBytesN_hit`, `addrOff_null`).
- Refusals, each with a concrete `decide` counterexample, none a peephole:
  oversized counts wrap (`probe_zaehler_ueberlauf` plus the null lemmas);
  `sdiv_ist_kein_sar` (`sarB` floors −3 to −2 via `ediv`, `divS` truncates
  to −1 via `tdiv`); `float_sub_self_kein_null` (NaN − NaN = NaN ≠ +0 over
  binary64 `f64`, no width guessed); `staerke_braucht_bereich`
  (`2^63 << 1` wraps, consumer gate `shlW_keinUeberlauf` named).
- Policy/shape: no `Befehl`/`schritt` change; `ShiftOp`/`shiftOpWert` is
  data-only dispatch routed to canonical ops by `rfl` — no second evaluator,
  no duplicated IR. No source tightening. Inhabitation: no theorem
  quantifies over program syntax and the task names no `ZEUGE:` target, so
  no `_zeuge` companions are owed; the joint memory witness is the
  task's Witness deliverable, as reported.

## Remarks (not repair-grade)

- Three `intro _` occurrences (`shlNachweis_eins`, `shrNachweis_eins`,
  `sarNachweis_eins`): each discards the antecedent of the unfolded
  `SchiebeGueltig` implication clause while the theorem premise `h` (the
  same proposition) IS used two lines later via `simp [..., h]` /
  `if_pos h`. Every theorem premise is used; this is style, not a rule 4(d)
  substance violation.
- CF past the width is pinned (`false` for SHL, saturated sign bit for
  SHR/SAR) where silicon leaves CF undefined for counts at/past the operand
  size. The file discloses exactly this in CUTS ("stated executable
  semantics, not verified against silicon") and claims no silicon
  correspondence; reshaping it would mean changing the reused canonical
  `SchiebeNachweis` (`trag : Bool`), which is another owner's vocabulary.
  Recorded as a bounded caveat for the future consumer, not a defect in the
  delivered claim.
- Base drift: author base `f737a6f0` adds the import after `Byteschritt`;
  current master also has `SpillPrivate` after it. Merge takes the union
  (standard `Grammatik.lean` resolution). Compatibility confirmed by the
  staged probe/build above.
- `sarUeberlauf` carries `_x` for uniform dispatch (documented); a
  definition parameter, not a discarded theorem premise.

## Open (agreed, per CUTS)

No `Befehl` extension, codec, TSO/GX bridge, source correspondence, cost
transfer, silicon verification, or final-image acceptance. Correctly stated
as OPEN. English throughout; CUTS + `#print axioms` present.
