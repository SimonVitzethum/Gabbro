# MUSE-REPORT-1266: exact review of 1265 (AVX2 join)

CANDIDATE: 1265 e7157c4a30ef66c136e06e6bf1e85bc1f14d4e62

Clone verified: `/home/simon/Dokumente/gabbro-muse/a1266`, branch `muse/1266`.
Reviewed input: `.tmp/review/SNAPSHOT.json` (head above, base
`c8bb42086282d1e2a7c5874a40303e7f060d3fad`, clean) via
`.tmp/review/author-1265/PATCH.diff` (1461 lines), the full
`Avx2Join.lean` snapshot (1352 lines), `OWNER-TASK.md`,
`MUSE-REPORT-1265.md` and `BUILD-EVIDENCE.json`. No files outside this
clone were touched. This lane adds no Lean code and changes no existing
file; it owns only this report.

## Checks performed

- Diff scope: exactly 3 files, 1439 insertions, 0 deletions:
  new `grammatik/Grammatik/X86/Avx2Join.lean`, new `MUSE-REPORT-1265.md`,
  one added line `import Grammatik.X86.Avx2Join` in
  `grammatik/Grammatik.lean`. No existing theorem weakened or deleted.
- Banned tokens over the new file: no `sorry`, no `admit` tactic (the
  single word match is English prose "admit" inside a doc comment),
  no `axiom` declaration, no `native_decide`, no `unsafe`, no
  `split_ifs`, no `norm_num`/`ring_nf`, no `intro _`, no `have _ :=`.
- Axioms: build evidence prints every main theorem; all reported
  dependencies are subsets of `[propext, Quot.sound]` (standard).
  File ends with a `CUTS:` block plus `#print axioms` per main theorem.
- Lifting, not copying: register evaluation (`avx2RegAuswertung` and 10
  agreement theorems) applies the accepted `ymm*` evaluators by
  reference; the 32-byte store is definitionally the accepted
  `issueListe` fold (`ymmSpeichern_ist_issueListe`, append/no-mem-change
  reused); loads use 4x accepted `ladeAcht`; addresses use accepted
  `effAddr`/`ripNach`; the old-row cross-check reuses
  `stufe_avx256_verweigert`. No piece model is duplicated.
- Premises used: spot-checked bridge theorems (both directions consume
  every named extra conjunct via `simp_all`), the 32-case membership
  induction, the plug equation, and the `Avx2Schritt` constructors;
  every hypothesis appears in its proof term.
- Refusals that really refuse (all `decide`): absent gate on all three
  paths, register/memory path separation both ways, misaligned
  `vmovdqa` store, VEX.128 shape, non-VEX bytes, byte shifts and
  `.b64` arithmetic shift (matching the accepted unencodable widths).
- Witness `avx2Wit_zeuge` (13 conjuncts): reached two-step run
  (`vpaddb` with lane separation `0xFF+2=1`, `1+1=2`), 32-entry buffered
  store with canonical memory unchanged, owner-only forwarding
  (core 0 sees `1`, core 1 sees `7`), full-word load-back, and a
  memory-changing flush (`7` to `1`). Non-degenerate: actual shared
  memory changes. Both cores observe; gate/`#GP`/shift/VEX.128/old-row
  refusals sit beside the run.
- Silicon (SDM extracts are not in this reviewer clone; encodings
  verified structurally by hand): all four pinned VEX rows derive
  correctly under Vol. 2A 2.3.5 (C4, inverted R/X/B = 0/0/0, W/vvvv/L/pp
  fields give VPADDQ/VPXOR `ymm0,ymm1,ymm2` with L=1/pp=01, and
  VMOVDQU load/store `ymm0,[rax+0]` with vvvv=1111/L=1/pp=10; ModRM
  bytes `C2`/`40` match register-register and mod=01 shapes). The
  aligned `#GP` rule (32-byte boundary) matches VEX.256 aligned-fault
  behaviour; absent-gate refusal is the `#UD` class. Ordering is
  per-byte TSO oldest-first with torn intermediates admitted, never
  whole-vector atomicity.
- No over-claim: CUTS explicitly leaves open decoder coverage, YMM
  legacy semantics, fault taxonomy, whole-vector atomicity, W/GX
  simulation and source correspondence. No hardware-correspondence
  claim is made.

## Findings (not blocking)

1. The import line lands mid-file (after `Avx2Ops`, before
   `TsoAddressCarrier`), not at the end of `Grammatik.lean`. Cosmetic;
   one line only, build green.
2. Only `Avx2Ops` (1239) exists in the tree; Vex/State/Mem substitutes
   are defined in the new file and marked as such. Honest scope note,
   re-pointing stays mechanical future work.
3. `avx2Addr` zero-extends disp8; silicon sign-extends. Openly recorded
   in CUTS and findings; the witness uses disp 0 where both agree.
   Not counted as a pass.
4. The profile-to-leaf bridge is conditional both ways with each missing
   conjunct named; no unconditional equivalence is claimed. Correct.
5. No bare `HwAdapter` is instantiated (`HwKern` has no YMM slot); the
   extended step relation with exact `einbettet`/`projiziert` is used,
   which the owner task allows as the alternative. Documented in the
   section 6 header.

## Build

- Own-clone `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (662 jobs)`. (Own clone holds
  the base tree, not the snapshot file.)
- Snapshot `BUILD-EVIDENCE.json`: final `./lean-probe` 0 errors and
  `./lean-bau` 658 jobs green on the pinned snapshot including the new
  import; intermediate red probes during development were repaired
  before the final commit.

VERDICT: ACCEPT
