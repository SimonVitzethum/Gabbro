# MUSE-REPORT-1241: AVX2 YMM state, XCR0 gating and upper-half rules

Clone `/home/simon/Dokumente/gabbro-muse/a1241`, branch `muse/1241` (verified via `.git/HEAD`).
Owned files only: `grammatik/Grammatik/X86/Avx2State.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

New file `grammatik/Grammatik/X86/Avx2State.lean` (~910 lines), connected to the
coherent machine without editing any accepted module:

- §1 YMM upper-half file `YmmDatei` (`XmmReg → Vektor`, YMMn low 128 = XMMn)
  and `ymmNull`.
- §2 AVX2 enabled-state gate `avx2ZustandBereit` (silicon AVX, reused
  `xcr0AvxBereit` for XCR0 bits 2:1, reused `kontrollSseFrei` plus CR4.OSXSAVE,
  OS vector-state bit) with needs/refusal theorems per conjunct and witness
  constants `avxZeugeCpu`/`avxZeugeXcr0`.
- §3 Closed gate = `#UD` outcome in the accepted `ArchFehler` vocabulary
  (`avx2Fehler`, `avx2TorFehler`); open gate carries no fault. Refused legs
  are `none` with the `.ud` outcome beside them, never executed.
- §4 Upper-half rules on the full pair `YmmVoll`: `vex128Voll` (low takes
  result, dest upper zeroed, others kept), `legacy128Voll` (upper file
  untouched), `vzeroOberhalb`, `vzeroAlle`. Low-half writes reuse accepted
  `xmmSet` and its lemmas. Transition-penalty timing stated as NOT modelled.
- §5/§6 Extended machine `YmmMaschine` (coherent machine + per-core upper
  files), gate-checked steps `ymmStepVex`/`ymmStepLegacy`/`ymmStepVzeroUpper`/
  `ymmStepVzeroAll` with wf preservation, exact `HwSchritt` embedding
  (`ymmEinbettung`, `ymmEinbettung_wf`), AVX-leg memory-freedom
  (`ymmAvx_kein_speicher`), and gate-checked adapter plug `adapterAvx2Tor`
  over accepted `adapterInteger666` (agreement, refusal-with-#UD, wf).
- §7/§8/§9 Reached non-degenerate joint witness `avx2Zustand_zeuge`: admitted
  gate with no fault, core-0 VEX transition with zeroed upper, core-1 legacy
  transition with kept uppers, refused baseline gate with #UD, buffered store
  issue with owner-only forwarding (`avxWitTso_fwd_eigen`,
  `avxWitTso_fremd_kanonisch`), memory-changing drain
  (`avxWitTso_speicher_aendert`: byte 0 → 1), coherent `HwSchritt.gibAus`
  issue step with preserved `HwWf`.
- CUTS block and `#print axioms` for every main theorem (all standard:
  none or propext, some with Quot.sound).

## Checks

- `./lean-probe grammatik/Grammatik/X86/Avx2State.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (642 jobs).`
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`split_ifs` in the new
  file (only prose "admits" and `#print axioms` lines match).
- Name collisions with accepted modules repaired by renaming: `avx2Bereit`
  (taken by `CpuFeatureHardwareForms`) → `avx2ZustandBereit`; `witKern`
  (taken by `MemoryTypeHardwareExecution`), `witV` (taken by `SourceMemory`),
  `witHw` (taken by `SourceMemory`) → `avxWit*` family.

## Open / not claimed

Per CUTS: no VEX decoder or byte encodings (sibling Vex/Ops/Mem lanes own
bytes); silicon correspondence of every gate bit position stays OPEN (SDM
extracts per MUSE-REPORT-660 named as provenance, not proof); the
observation-to-gate link (CPUID/XGETBV chain) stays with `ComposeFeatureGate`;
no 256-bit memory-traffic TSO/GX claim, no source/budget/progress/call-log
link, no new `PerfMerkmal` (AVX2 stays explicitly optional).

## Task notes

The generic mechanism text (§11-style adapter + two-core memory witness) fits
a memory-touching family; YMM state touches no memory, so the adapter is the
gate-checked register path and memory traffic is witnessed on the shared TSO
view both cores observe, with the drain as the memory-changing step. The
INHABITATION rule does not trigger (no premise quantifies over program
syntax), but the joint witness is still named `avx2Zustand_zeuge`.
