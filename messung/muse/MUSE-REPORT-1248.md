# MUSE-REPORT-1248: Independent exact review of author lane 1247 (HwContextState)

Reviewer lane 1248, second round. Clone verified:
`/home/simon/Dokumente/gabbro-muse/a1248`, branch `muse/1248`, tree
clean. Review-only lane: I own only this file, added no Lean code and
touched no existing files. This round the coordinator delivered the
pinned snapshot (base `ca33ef1b`, three files, clean true) plus the
full evidence directory (PATCH.diff, author report, owner task, build
evidence, candidate file copies) inside this clone, so the complete
exact-review checklist below was executed against the real candidate.
The prior round's procedural outcome is thereby superseded.

CANDIDATE: 1247 b601ae989cd5f3e66146344be7ce5c8e76627cfd

VERDICT: ACCEPT

## Scope reviewed

Three files, confirmed from PATCH.diff (1707 lines total): new file
`grammatik/Grammatik/X86/HwContextState.lean` (1587 lines), exactly one
appended line `import Grammatik.X86.HwContextState` in
`grammatik/Grammatik.lean` (line 645, after `TsoRmwLink`), and the
author's owned report. Per the build evidence, the new pinned head
differs from the prior pinned head only by the author's report
addition; the Lean content is unchanged, so this review covers the
entire deliverable with nothing stale.

## Independent verification performed (not just read)

1. Ran `./lean-probe` on the delivered candidate file copy in this
   clone: `== 0 error(s) in the COMPLETE output; exit 0`. The file
   elaborates green against this clone's accepted tree, so there is no
   hidden base drift and no unproved step.
2. The probe output reproduces all 19 author `#print axioms` lines:
   every main theorem depends only on `[propext]` or
   `[propext, Quot.sound]`, a subset of the `gabbro_ziel` standard.
   Axiom lists verified for `mxcsr_rundlauf`, `ctxRundlauf_pur`,
   `neuestens_append`, `ctxLade_geladen`, `fxDekodiere_kongr`,
   `ctxSpeichern_puffer`, `ctxSpeichern_kein_speicher`,
   `ctxRundlauf_maschine`, `ctxWiederherstellen_fehlerGP_reserviert`,
   `ctxXSave_ist_fxSave`, `ctxXRundlauf_maschine`,
   `asyncMasch_fp_still`, `handlerErhaeltKontext`, `wechselStelltHer`,
   `ctxSchritt_wf`, `ctxLade_ist_hw`, `adapterContext_fxsave_wf`,
   `ctxWitStart_wf`, `ctxWit_zeuge`.
3. Grepped the delivered copy for forbidden tokens: no `sorry`, no
   `admit`/`axiom`/`native_decide`/`unsafe` as tactics or commands, no
   anonymous `intro _`, no `have _ :=`. The only `admit` substrings sit
   inside the English words "admitted"/"admits" in doc comments.
4. Grepped this clone's accepted tree for every load-bearing reused
   name: `issueByte`/`loadByte`/`flushKern`/`issueListe` (TSO.lean),
   `issueListe_haengt_an`/`issueListe_kein_speicher`/`setTso_wf`/
   `setKernDaten_wf`/`setTso_ansicht`/`tsoAnsicht`/`setTso`/
   `setKernDaten`/`HwSchritt` (`lade`/`gibAus`/`spuele` legs)/
   `HwAdapter` (HardwareExecution.lean), `mxcsrReserviertFrei`/
   `mxcsrReserviertFrei_verweigert`/`ldmxcsrArchOk`/
   `ldmxcsrArchOk_reserviert_verweigert` (FpControlHardwareForms.lean),
   `xcr0SseBereit`/`Xcr0Bild` (VectorHardwareProfile.lean),
   `asyncMasch`/`asyncSchritt`/`witNmi`/`witSteuerNmi`/`intWitStart`
   (HwInterrupts.lean), `bytesWort_wortByte` (Speicher.lean),
   `vecJoin_split` (Vektor.lean), `mxcsr_sticky_egal_gueltig`/
   `kontextReset`/`FPKontext` (Gleitprofil.lean), `zeugeFlags`
   (Ausfuehrung.lean), `basisHw`/`basisBereit` (FeatureProfile.lean).
   All present: the family evaluator is lifted, never copied, and no
   canonical model is duplicated.
5. Read the full PATCH.diff line by line (all eight sections plus CUTS).

## Checklist results

- Forbidden tactics/decls: PASS (item 3 above).
- Standard axioms: PASS, independently reproduced (item 2 above).
- Existing files untouched except one import line: PASS (PATCH proves it).
- Every premise used: PASS. The remaining `unusedVariables` linter
  hints attach to vacuous-case branches (`neuestens_einmal` nil case,
  `ctxLade_geladen` nil case) where underscore-prefixed names mark
  intentionally unneeded hypotheses; each flagged binder (`hb`,
  `hk512`, `hnd`, `hm`, `hl`, `base`, `s'`) is visibly used in a
  non-vacuous branch of the same proof. No anonymous discard anywhere.
- No conclusion restates a premise; no `Prop`-typed premise; no
  universal over program syntax anywhere (rule-13 per-theorem duty is
  vacuous here; the joint `ctxWit_zeuge` covers the mechanism anyway).
- Agreement leg exact: PASS. `ctxLade_ist_hw`, `ctxGibAus_ist_hw`
  conclude the coherent `HwSchritt` step definitionally;
  `ctxSpuele_ist_hw` wraps the existential only because
  `HwSchritt.spuele` takes its successor state explicitly. Request
  legs (save/restore/XSAVE/XRSTOR) are new steps with nothing prior to
  embed, which the task mechanism expressly permits.
- Planted refusals really refuse: PASS. Kernel-checked `decide`
  equalities evaluate genuine refusal paths: misaligned save address
  4104 (4096+8, truly 16- and 64-misaligned) faults, the no-component
  request is refused rather than a silent no-op, XSAVE without XCR0
  SSE readiness faults, misaligned XSAVE faults, and the bit-18
  MXCSR probe image faults on restore through the accepted
  reserved-bit threshold.
- Witness non-degenerate: PASS. Two cores each buffer a full
  260-entry save image; owner-only forwarding is observed (core 0
  reads `0x80`/`7`, core 1 reads zeros at the same cell); one drain
  observably changes shared memory (0 becomes `0x80`, a genuine
  memory-changing step); the machine round trip restores `0x1F80`;
  NMI delivery preserves the control word over the accepted
  `intWitStart` image; `HwWf` and the pure round trip close the
  conjunction in `ctxWit_zeuge`.
- Silicon facts: PASS within reviewer reach. Layout (MXCSR at 24-27,
  XMM0-15 at 160-415), 16-byte FXSAVE/FXRSTOR alignment fault,
  reserved-MXCSR fault on restore, 64-byte XSAVE/XRSTOR alignment
  fault, and RFBM-gated SSE component all match established x86-64
  architecture behavior. The SDM extract offsets cited by the author
  could not be opened here (extracts are clone-local to the author
  side and were not delivered), so this item is verified against
  known architecture, not against the cited text. The sparse 260-byte
  footprint with zeros elsewhere is an honest documented scope cut,
  and CUTS claims no hardware correspondence beyond self-consistency.
- CUTS honest, no claim larger than the proof: PASS. No W/GX bridge,
  no timing, no whole-word atomicity, no loader/entry/budget link is
  claimed; every gap (x87, MXCSR_MASK, XSAVE header, AVX, further
  fault classes, FINIT, handler bodies) is named.

## Minor observations (not defects, no action required)

- `CtxSchritt` has no restore-side refusal self-loops (misaligned or
  reserved-bit restore outcomes have no step constructor). Refusal
  there means absence of a step plus an explicit `.fehlerGP` outcome
  at function level, covered in the witness, so nothing is silent;
  a follow-up may add the constructors for symmetry.
- `ctxWit_schief`-style `decide` witnesses with deep `maxRecDepth`
  budgets are elaboration-heavy but kernel-checked and green.

## Last `./lean-bau` result line (this clone, unchanged Lean tree)

`== exit 0; 0 error line(s) in the COMPLETE output` —
`Build completed successfully (665 jobs).`

## New definitions/theorems by the reviewer

None. Review-only lane.

## What remains open

Nothing on this candidate from this reviewer. Integration (merge,
post-merge `lean-bau`, publication) is coordinator business. The
named gaps live in the candidate's own CUTS block for future lanes.
