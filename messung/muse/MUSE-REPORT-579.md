# MUSE-REPORT-579: Independent exact-candidate connection review of 561

## Scope

Reviewed the exact candidate for lane 561 (relocated rel32 bytes to
re-decoded instruction execution) from `.tmp/review/SNAPSHOT.json`,
`author-561/OWNER-TASK.md`, `author-561/MUSE-REPORT-561.md`,
`author-561/PATCH.diff` and the full 1088-line candidate module
`author-561/grammatik/Grammatik/X86/RelocatedExecution.lean`.
Verified branch `muse/579` in `/home/simon/Dokumente/gabbro-muse/a579`
before starting. Own only this report; no other paths touched.

## Method

- Resolved every claimed producer name against the live tree:
  `dispWort`, `dispSigned`, `rel32Enc64`, `rel32Passt`, `rel32Enc`,
  `rel32_adress_gleichung`, `rel32_next_rip`, `rel32Fuer`, `direktZiel`,
  `ripNach`, `kanonisch_schritt_ueberein`, `schritt_jump32`,
  `schritt_call32_erfolg`, `schritt_jumpIf32_genommen/nicht`,
  `ladenByte`, `abteilFinden`, `geladenByte_datei`, `dateiByte`,
  `geladen`, `wohlgeformt`, `RelArt(.codeOperand/.datenFeld)`,
  `zweig_jump32_len/call32_len/jumpIf32_len`,
  `roundtrip_jump32/call32/jumpIf32`, `condCode`, `witnessFlags`,
  `read64_nach_write64`, `writeBytesN_hit`, `addrOff_null` — all present,
  none redefined by the candidate (no second decoder, loader, executor,
  ISA, or IR; no `OptimizationRules`/`OptimizationWitnesses` reference).
- Grepped the candidate for `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`:
  the only match is the English word "admit" in a doc comment. No
  `intro _`, no `have _ :=`, no `forall rho/v` contract quantification.
- Reproduced the build: copied the candidate module plus its one-line
  umbrella import into this clone, ran `./lean-probe` (0 errors, all
  `#print axioms` within `[propext, Classical.choice, Quot.sound]`)
  and the full `./lean-bau` (exit 0, 437 jobs on this newer base vs the
  428 reported at the candidate base — the delta is base drift, not
  candidate content). Reverted both afterwards; the tree is clean and
  this commit is report-only.

## Findings

1. Real connection, not decoration: `patchSite_ziel` derives decoded
   target = intended mapped target through the relocation address
   equation plus the new `dispWort_bridge`; the four `_schritt`
   theorems reach the target via `kanonisch_schritt_ueberein` on the
   actually fetched window (`geholt z = relocBytes …`), and the three
   `bildSite_*_dekode` theorems tie those bytes to the real `datei`
   list through `geladenByte_datei`. The chain is
   file bytes -> loaded window -> decode -> execution, never metadata.
2. Joint witnesses are non-vacuous: `vor_akzeptiert`,
   `rueck_akzeptiert`, `versetzt_akzeptiert`, `ruf_akzeptiert` (forward
   +16, backward -16, nonzero bias 0x100000, call +16) all hold by
   `decide` over `wohlgeformt` images; `ruf_schritt_zeuge` shows a real
   `write64` (return address 0x1005 at 0x1FF8), read-back, and an
   observable byte change 0x00 -> 0x05. Planted refusals:
   `aussen_verweigert`, `aussen_rel32Fuer` (displacement 2^31, also at
   the producer `rel32Fuer` level), `innen_verweigert` (0x1002 inside
   its own site bytes).
3. Honest bounds: the not-taken conditional carries no unneeded target
   premises (stated openly); `siteArtOk` refuses `datenFeld`; CUTS
   lists abs64/rel8/other-instruction sites, multi-site convergence,
   loader execution, source correspondence and TSO/GX as open. No
   exaggerated closure, no contract-duty weakening, no guessed ISA
   (opcodes/widths come from `Codec`/`BranchLayout` round-trips).
4. Owned paths only: `PATCH.diff` touches exactly `MUSE-REPORT-561.md`,
   `grammatik/Grammatik.lean` (one additive import) and the new module.
   No checker/Spec/goal/emitter changes.
5. Nothing in the owner task turned out to be wrong. Minor note, not a
   defect: `testBit_div_pow` depends only on `[propext, Quot.sound]`
   (no `Classical.choice`), slightly stronger than the report's blanket
   phrasing — the report's claim "within standard axioms" remains true.

## Accepted bounded claim

One checked rel32 site at its final layout: `patchSiteOk` +
`patchSite_ziel` + the matching `patchSite_*_schritt` theorem
discharges a jump/call/taken-conditional site from actual image bytes
to actual-memory execution, with out-of-range and interior-target
refusal. Consumer: feed `fenster5`/`fenster6` from a real emitted image
to close one `valX86` site obligation.

CANDIDATE: 561 059e87ee1c95eaf47cd197542a02c8d1e9e19cba

VERDICT: ACCEPT
