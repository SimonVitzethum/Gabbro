# MUSE-REPORT-1242: exact review of candidate 1241 (AVX2 YMM state)

Clone `/home/simon/Dokumente/gabbro-muse/a1242`, branch `muse/1242`: verified
(`pwd` + `git branch --show-current`). Own file only: this report.

## Candidate

Lane 1241, pinned HEAD `8f34e3f83e5c6543266bf3d5b0eb2ed9be488259`, base
`ca33ef1b3eaa30c178343517c9fd20f32a914b58` (from `.tmp/review/SNAPSHOT.json`;
the lane task's `<full pinned HEAD>` placeholder is resolved by that file).
Reviewed material (read-only, exact): `.tmp/review/author-1241/PATCH.diff`
(998 lines), `.tmp/review/author-1241/grammatik/Grammatik/X86/Avx2State.lean`
(909 lines, line count matches the PATCH `+1,909` hunk),
`.tmp/review/author-1241/grammatik/Grammatik.lean` (one appended import),
`MUSE-REPORT-1241.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`.
Files in the candidate: only `MUSE-REPORT-1241.md`,
`grammatik/Grammatik.lean` (exactly one added line,
`import Grammatik.X86.Avx2State`), and the new `Avx2State.lean`. No accepted
module is edited.

## Method and builds

No temp-apply: with `rm`/`git checkout` denied, placing the candidate in my
tree would be irreversible, and my HEAD `6d62a089` is newer than the
candidate base (my `./lean-bau` builds 653 jobs vs the candidate's 642), so
a local build would test a different tree, not the pinned candidate.
Candidate-side build proof is the author's full `BUILD-EVIDENCE.json`:
step-by-step `./lean-probe` history (every intermediate error shown repaired:
projection fixes, the `avx2Bereit` rename after the
`CpuFeatureHardwareForms` collision, the `avxWit*` renames after the
`SourceMemory`/`MemoryTypeHardwareExecution` collisions, TSO-witness
repairs) ending in `== 0 error(s)` and
`./lean-bau: Build completed successfully (642 jobs).`
My tree is green: `./lean-bau` last result line
`Build completed successfully (653 jobs).`
(First attempt exceeded a 15-minute timeout in the shared single Lean slot;
retry completed. No blocker remains.)

## Checks against the review bar

- Banned tokens: own `rg` over the snapshot file for
  `\badmit\b|\bsorry\b|native_decide|split_ifs|\bunsafe\b|^axiom |^Axiom `
  returns nothing (exit 1). Remaining matches for `admit` are prose
  ("admits", "admitted") and `#print axioms` lines only.
- Axioms: per build evidence, every printed theorem uses none, `[propext]`,
  or `[propext, Quot.sound]` — subsets of the goal standard. The joint
  witness `avx2Zustand_zeuge` is `[propext, Quot.sound]`. Standard.
- Premise use: every theorem consumes all premises; no `intro _`, no
  discarded hypothesis, no `Prop`-typed premise. `ymmEinbettung` repackages
  `h : HwSchritt s.hw m' e` into an existential, but the new content is the
  extended-machine frame (`s'.ober = s.ober`); the real content sits in
  `ymmEinbettung_wf` via accepted `hwSchritt_wf`. Not a rule-4(a) fake.
- Lift, not copy: `xmmSet` + `xmmSet_gleich`/`xmmSet_fremd` for both files,
  reused `xcr0AvxBereit` (XCR0 x87/SSE/AVX) and `kontrollSseFrei` (+
  `cr4Osxsave`), `setKernDaten` + `setKernDaten_wf`, `hwSchritt_wf`,
  `adapterInteger666.schritt`, `vektorLegacyZugelassen`, full TSO vocabulary
  (`issueByte`/`loadByte`/`flushKern`/`pufferSetze` +
  `load_nach_issue`/`issue_kein_speicher`/`issue_anderer_kern`/
  `load_ohne_eintrag`), `setTso`/`setTso_wf`, `HwSchritt.gibAus`. The new
  `avx2ZustandBereit` is at the structured-profile level (mirrors accepted
  `hwVektorBereit`); accepted raw-observation `avx2Bereit` (CPUID leaves +
  XCR0 word) is a different vocabulary level, so this is no duplication, and
  the observation-to-gate link is explicitly left with `ComposeFeatureGate`
  in CUTS. No contradiction with accepted
  `stufenZugelassenHw ... .avx256 = false` (that refuses the 256-bit
  execution tier; the candidate admits no 256-bit traffic).
- Refusals refuse: per-conjunct gate refusals (`avx2_ohne_cpu`,
  `avx2_ohne_xcr0`, `avx2_ohne_osxsave`, `avx2_ohne_osxmm`), concrete
  `decide`d baseline refusal (`avx2_basis_verweigert`) with the #UD outcome
  (`avx2_basis_ud : ... = some .ud`), `ymmStepVex_verweigert` paired with the
  outcome (`ymmStepVex_ud`), `adapterAvx2Tor_verweigert` with #UD beside it.
  Refused legs are `none`, never executed.
- Witness non-degenerate: `avx2Zustand_zeuge` joins admitted gate with no
  fault, core-0 VEX transition with zeroed upper + wf, core-1 legacy
  transition with kept uppers + wf, refused baseline gate with #UD,
  buffered store issue, owner-only forwarding (`avxWitTso_fwd_eigen`),
  foreign canonical read (`avxWitTso_fremd_kanonisch`), memory-changing
  drain (`avxWitTso_speicher_aendert`: byte 0 is 0 then 1), coherent
  `HwSchritt.gibAus` issue step with preserved `HwWf`. Two cores, a
  memory-changing step, owner-only forwarding — the owner task's bar, met.
  INHABITATION does not trigger (no syntax premises); author notes this.
- Silicon vs supplied Intel SDM ed. 093 extract: VEX-128 zeroes 255:128 and
  legacy SSE leaves them unmodified (extract lines 34056-34057); VZEROUPPER
  zeroes bits >= 128 keeping low halves; VZEROALL zeroes all; closed-gate
  #UD covers XCR0[2:1] != 11b, CR4.OSXSAVE = 0, CPUID.AVX = 0 (Type 8
  table, which covers VZEROALL/VZEROUPPER). The gate's extra conjuncts
  (CR0.EM/TS via reused `kontrollSseFrei`, OS `osXmm` bit) only add
  refusals — the safe direction; `kontrollSseFrei` reuse follows the
  accepted SSE-tier discipline.
- Scope honesty: CUTS disclaim bytes/decoder, per-bit silicon
  correspondence, the CPUID/XGETBV observation link, 256-bit TSO/GX,
  source/budget/progress/call-log, transition-penalty timing, and
  loaded-image execution. The report's "Open / not claimed" matches. No
  hardware-correspondence or W/GX claim anywhere.

## Observation (non-blocking, for the integrator)

`ymmStepVzeroUpper`/`ymmStepVzeroAll` are total ungated state functions
("only clears state"). On silicon both instructions are Type 8 and fault
#UD behind a closed gate. Inside this file that is in-scope: it models
clearing effects only and claims no byte executes. Any future consumer
wiring these steps to fetched `VEX.128.0F.WIG 77` / `VEX.256...77` bytes must
add the Type 8 gate there (sibling Vex/Ops/Mem lanes own bytes).

## VERDICT: ACCEPT

Candidate 1241 at `8f34e3f83e5c6543266bf3d5b0eb2ed9be488259` is accepted as
reviewed: green build evidence at the pinned HEAD, standard axioms, honest
CUTS, real refusals, non-degenerate two-core witness, silicon-checked
shapes, no over-claim.
