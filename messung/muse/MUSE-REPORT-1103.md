# MUSE-REPORT-1103: Exact review of candidate 1102 (port/device execution on the common machine)

Clone `/home/simon/Dokumente/gabbro-muse/a1103`, branch `muse/1103`.
Review-only lane: the single owned file is this report. No source, private,
root or network changes.

## Candidate under review

CANDIDATE: 1102 d5f75c7a401432538b02d4dca2f4b8c5b2815187

- Author lane 1102, pinned HEAD `d5f75c7a401432538b02d4dca2f4b8c5b2815187`
  (per `.tmp/review/SNAPSHOT.json`: base `f31f93197c59c64371b654a960ccbdf6f166f40d`,
  `clean: true`).
- Files: `MUSE-REPORT-1102.md` + `grammatik/Grammatik/X86/DeviceCommonExecution.lean`
  (780 lines, namespace `Gabbro.Grammatik.X86.DeviceCommon1102`).
- The candidate file is NOT present in this clone's `grammatik/` (verified by
  glob: no `DeviceCommonExecution.lean` under `grammatik/Grammatik/X86/`), so
  this review changed no build input.

## Verdict

VERDICT: ACCEPT

The candidate meets every checked gate. Evidence below is verified against this
clone's accepted modules and by an independent probe run in this clone.

## Evidence

1. **Independent probe, exact candidate bytes, this clone's tree: 0 errors.**
   `./lean-probe .tmp/review/author-1102/grammatik/Grammatik/X86/DeviceCommonExecution.lean`
   returns `== 0 error(s) in the COMPLETE output; exit 0`. The file elaborates
   against this clone's accepted 676/694/704/728 modules, so acceptance does not
   rely on author-side tree state. Axiom report is standard only: every main
   theorem depends on `[]`, `[propext]`, or `[propext, Quot.sound]`.
2. **Baseline `./lean-bau` in this clone: `== exit 0; 0 error line(s) in the
   COMPLETE output`, `Build completed successfully (555 jobs).`** Tree is green
   without the candidate (expected: the umbrella import line is the merger's
   one-line addition).
3. **No forbidden tactics or axioms.** Full 780-line read plus mechanical grep
   over the snapshot: no `sorry`, `admit` (only the English word "admits" in a
   comment), `axiom` (only `#print axioms`), `native_decide`, `unsafe`,
   `intro _`, `have _ :=`, or `Prop`-typed premise. Rule-4 shapes hold: the
   three targets derive substantive conjunctions from used premises (selection
   lemmas produce both the computed successor AND the reached generic step;
   `deviceCommon_tso_verweigert` uses both `hstep` and `hro`; every premise of
   the `*_fetch` lemmas appears in the proof term).
4. **No rebuilt bus, no second TSO, no parallel descriptor model.** Imports are
   exactly eight accepted modules (`Typen`, `Speicher`, `TSO`,
   `DeviceHardwareForms`, `HardwareExecution`, `DeviceBusHardwareExecution`,
   `MemoryTypeHardwareExecution`, `InterruptDescriptorHardware`); no unaccepted
   import, no umbrella import (no cycle possible). The generic step reuses
   `Bus704.BusSchritt` on the core projection with `setKernDaten` re-embedding
   (which updates only `kerne`, so the `mem`/`puffer` frames hold by `rfl`);
   constructor applications match the accepted `.aus`/`.ein` shapes checked in
   this clone (`DeviceBusHardwareExecution.lean:259-284`). The file's only
   `structure` is the `PendingResp` gate record; TSS/CPL data is read from the
   accepted 728 `Steuerstand` (6-field shape confirmed in this clone) and checked
   with the accepted `tssBitFrei`/`karte_fehlt_verweigert`/`dplZugelassen`/
   `dpl_verweigert_software` lemmas. Denial stays in the accepted `#GP` family
   (`busFehler false`, `alsArch (.limitFehler v)`).
5. **TSO exclusion covers every device-byte path in the accepted vocabulary.**
   Port path: `devSchritt_puffer` (buffers unchanged by construction) plus
   `issue_verweigert` at the device address; `issueByte` is the only TSO insert
   rule in `TSO.lean` and refuses exactly on `¬ schreibbar`, which is the
   theorem's `hro` premise (a memory-map fact, discharged by `decide` in the
   witness — not a correctness wish). MMIO path: `deviceCommon_mmio_ordnung`
   reuses the accepted `ucStore_bypass` (6-conjunct shape confirmed) and
   `busFortschritt_fifo` (7-component shape confirmed); `MmioMaschine` carries
   no `TSOZustand` buffer and both legs frame `pending` equal, so no MMIO row
   can smuggle a device byte into WB ordering. No DMA path exists in the
   accepted vocabulary (out of scope, disclosed in CUTS).
6. **Pending gate refuses, never answers.** `pendingLeer` is a premise of every
   `DeviceCommonSchritt` (`devSchritt_pending_leer` exhibits it) and a conjunct
   of the fetched-step guard; no definition maps a `PendingResp` to an answer
   value (the list appears only in gate checks). Probe
   `dev_probe_pending_verweigert` shows a pending response refusing a reached
   step, by `decide`.
7. **Joint witness is non-degenerate, three probes present.** Joint theorem
   `deviceCommon_zeuge_gemeinsam` conjoins the reached IN/OUT run (device
   `0x1234` to 52, two observations, ordered two-event log, RIP 4100, empty
   buffers, zeroed cell 8192) with the accepted memory-changing pilot store
   (`ioWit_dritter_speichert`: cell 8192 reads 52 after the run;
   `ioWit_anfang_null`: it read 0 before — confirmed in this clone's
   `DeviceHardwareForms.lean:1139-1149`). All three planted refusals are
   present and refused by evaluation: `dev_probe_tso_verweigert` (device-window
   byte refused by the RAM TSO rule), `dev_probe_privileg_karte` /
   `dev_probe_privileg_schritt` / `dev_probe_privileg_dpl` (denying
   728-derived card refuses; CPL 3 vs IOPL 0 with missing TSS window confirmed
   against the 6-field `Steuerstand`), `dev_probe_pending_verweigert`. Target
   companions `deviceCommon_byteschritt_zeuge`,
   `deviceCommon_tso_verweigert_zeuge`, `deviceCommon_mmio_ordnung_zeuge`
   (with `ordWitM`, `ordWit_kette`) are present.
8. **CUTS honest; merger note correct.** The `CUTS:` block (lines 723-752) claims
   only reuse-level results and leaves hardware correspondence, pending answers,
   per-access W/GX simulation and source/ABI/budget links OPEN. `#print axioms`
   covers every main theorem (with a harmless duplicated pair for the two
   pending lemmas). The missing umbrella import line is correctly flagged as
   the merger's one line; the file needs only `import
   Grammatik.X86.DeviceCommonExecution` appended to `grammatik/Grammatik.lean`.

## What remains open / merger note

- Nothing for the author to repair. Integration: add the one import line, then
  run the standard gates (full `./lean-bau`, axiom check, emission/key scans)
  at merge time.
- Scope limits are the candidate's own honest CUTS: no hardware correspondence
  beyond cited SDM entries, no device-answer claims, no target-to-W/GX leg.

## Task feedback

Nothing in the review task was wrong. One note: the candidate snapshot was
reviewed from the in-clone exact byte copy
(`.tmp/review/author-1102/grammatik/...`) rather than the sibling author clone,
per the touch-nothing-outside-this-directory rule; the pinned HEAD in
`SNAPSHOT.json` (`d5f75c7a...`) identifies the reviewed bytes.
