# MUSE-REPORT-1133: Device/MMIO and memory types on the coherent machine

Lane 1133, clone `/home/simon/Dokumente/gabbro-muse/a1133`, branch `muse/1133`.
Base HEAD `8744590d`. Owned files only:
`grammatik/Grammatik/X86/HwDevices.lean` (new, ~990 lines),
`grammatik/Grammatik.lean` (one import line),
this report.

## What was done

New module `Grammatik.X86.HwDevices` (namespace `HwDev1133`) lifts the
accepted UC MMIO evaluator (lane 694, `MemoryTypeHardwareExecution`) and the
generic port bus (lane 704, `DeviceBusHardwareExecution`, `Bus704`) onto the
coherent machine (lane 660, `HardwareExecution`). Nothing is redefined: every
step runs the accepted functions on a per-core projection. Related work
checked for overlap: lane 1102 (`DeviceCommonExecution.lean`, present in tree
but NOT imported in `Grammatik.lean`) covers port IO on the machine with its
own relation; this lane instead puts UC/MMIO on the machine, exposes
bus/device events as `HwAdapter` plugs (which 1102 does not do), and states
the UC ordering rule plus DMA as named assumptions.

- §1 Named assumptions: `dmaAnfrage` (refused stub) + `dmaAnfrage_verweigert`,
  `DmaAnnahme` + `dmaAnnahme_gilt` + `dmaAnnahme_verweigert`,
  `UcBusAnnahme` (pins present the retired log in order) + `ucPinsLaenge`.
- §2 Projection `devProj` onto the accepted `MmioMaschine`
  (+ `devProj_kern/pending/profil`), `HwDevWf` (+ `hwDevKern_wf`,
  `hwDevGeraet_wf`).
- §3 `DevEreignis1133` + `HwDevSchritt` (ucSpeichern/ucLaden/busVollendung).
- §4 Agreement: `hwDevStore_bypass`, `hwDevStore_puffer`,
  `hwDevLaden_rahmen`, `hwDevLaden_register_bei`, `hwDevBus_fifo`,
  `hwDevSchritt_wf`.
- §5 UC plug: `UcZugriff1133`, `ucAdapterSchritt`, `adapterUc1133`,
  `ucAdapterSchritt_speichern`, `ucAdapterSchritt_lade_verweigert`,
  `ucAdapterSchritt_nichtUc_verweigert`, `adapterUc1133_wf`,
  `adapterUc1133_stimmt_ueberein`.
- §6 Port plug: `PortZugriff1133`, `portAusKern`, `portEinKern`,
  `portAdapterKern`, `portAdapterSchritt`, `adapterPort1133`,
  `portAdapter_aus_fetch`, `portAdapter_ein_fetch`,
  `portAdapter_fetch_verweigert`, `portAdapter_falschDecodiert_verweigert`,
  `portAdapter_ohneBerechtigung_verweigert`,
  `portAdapter_vollerPuffer_verweigert`, `adapterPort1133_wf`.
- §7 DMA plug: `DmaZugriff1133`, `adapterDma1133`,
  `adapterDma1133_verweigert`.
- §8 Witness: `witProfil1133`, `witDev1133`, `witRam1133`, `witKern1133`,
  `witMasch1133`, `witStart1133` + `witStart1133_wf`, `witD11133`,
  `wit_schritt1_1133`, `witBus1133`, `wit_bus_ausstehend_1133`,
  `wit_bus_log_1133`, `wit_bus_geraet_1133`, `wit_schritt2_1133`,
  `witIssue1133`, `wit_eigen_1133`, `wit_fremd_1133`, `witFlush1133`,
  `wit_spuelung_1133`, `wit_fremdNeu_1133`, `wit_ramNull_1133`,
  `wit_dma_1133`, `wit_art_1133`, `wit_ueberlapp_1133`, `wit_nichtUc_1133`,
  joint `hwDev_zeuge` (both named assumptions as premises, discharged
  into concrete facts; non-degenerate: device byte 0->7 AND RAM cell
  0->42, owner-only forwarding, two cores).

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwDevices.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (601 jobs).`
- `#print axioms`: all main theorems depend on `[propext, Quot.sound]`
  or less; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (grep-checked; only prose "admitted" and `#print axioms` lines match).
- No `Grammatik.lean` theorems touched; one import line appended.

## What remains open (see CUTS in the file)

No hardware correspondence beyond cited SDM entries; UC profile
population is user logic. No WC/WT/WP, no DMA engines, no
chipset-posting model, no liveness/timing. The port plug is stateless
across steps by construction; the UC-load leg refuses on the bare
machine. No target-to-W/GX simulation, no source/checker/goal links.

## Notes on the task

- The task names `DeviceCommonExecution.lean` as family, but that file is
  not wired into the build (no `Grammatik.lean` import); depending on it
  would have pulled an unbuilt module into the build, so this lane reuses
  only built family modules (`Bus704` directly). No overlap with its
  `DeviceCommonSchritt` content was created.
- Two genuine Lean pitfalls were hit and repaired, no weakening:
  `cases` on the indexed step relation names one fewer binder than the
  constructor has (the fixed first index takes no name), and `⟨{`
  adjacency misparses (newline between `⟨` and `{` required).
- The UC-store gate adds no drain premise beyond the accepted
  conjunction (the accepted model does not require it); adding one
  would have been a tightening, not a lift.
