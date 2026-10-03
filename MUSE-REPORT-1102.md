# MUSE-REPORT-1102: Port and device execution on the common machine

Clone `/home/simon/Dokumente/gabbro-muse/a1102`, branch `muse/1102`. Base `f31f9319`.
Owner-only files: `grammatik/Grammatik/X86/DeviceCommonExecution.lean` (new, 780 lines),
`MUSE-REPORT-1102.md` (this file). Four commits: `70274175`, `0b1b1408`, `4df2388d`,
`086921f6`.

## What was done

New module `Gabbro.Grammatik.X86.DeviceCommon1102` lifts the accepted port/device rows
(676 codecs, 694 UC machine, 704 bus with IO permissions) onto `HwMaschine`, reusing only
accepted modules (`Typen`, `Speicher`, `TSO`, `DeviceHardwareForms`, `HardwareExecution`,
`DeviceBusHardwareExecution`, `MemoryTypeHardwareExecution`, `InterruptDescriptorHardware`).
No second decoder, no parallel descriptor model, no second IN/OUT interpreter, no new machine.

- Pending gate: `PendingResp`, `pendingLeer`, `pending_belegt_verweigert`, `pending_leer_ok`.
  Outstanding pending responses refuse every step, never answered by fiat.
- 728-derived privilege: `devKarteAusSteuer` / `devRechtAusSteuer` (TSS window and CPL read
  from `Steuerstand`), `dev_karte_fehlt_verweigert` (missing-map rule lifted),
  `dev_dpl_verweigert_software` (accepted DPL check), `dev_verweigerung_ist_gp` (port #GP
  beside the 728 #GP member, no parallel fault class).
- Generic step: `hwKernAusZustand`, `ordnungOk_zaun` (both IO directions share the one
  fence-readiness gate), inductive `DeviceCommonSchritt` reusing `BusSchritt` on the core
  projection (successor only re-embeds core data), with frames `devSchritt_speicher`,
  `devSchritt_puffer`, `devSchritt_spur_waechst`, `devSchritt_xmm`, `devSchritt_pending_leer`.
- Fetched step: `DevCommonAusgang`, TARGET `deviceCommon_byteschritt` (accepted `fetchIo`,
  `ausKern`/`einKern`, computable `geraetAntwort`), bridges `latchAus_paar`, `latchAus_ant0`,
  `latchEin_paar`, `latchEin_ant`, and both selection lifts `deviceCommon_aus_fetch`,
  `deviceCommon_ein_fetch` (every computed successor is a reached generic step).
- TARGET `deviceCommon_tso_verweigert` (buffer frame plus `issue_verweigert` at the device
  address) and TARGET `deviceCommon_mmio_ordnung` (`ucStore_bypass` plus `busFortschritt_fifo`:
  UC retire and bus completion both pass the WB buffer by).
- Witnesses: `devWitKern`, `devWitStart` (core 0 on the accepted port image), `devWitO1`,
  `devWitO2`, observers, `dev_fetch_s1` (exact 13-byte remainder, decide), exhibited reached
  generic step `deviceCommon_schritt_zeuge`, joint `deviceCommon_zeuge_gemeinsam` (run into
  the accepted memory-changing pilot store plus all three probes), companions
  `deviceCommon_byteschritt_zeuge`, `deviceCommon_tso_verweigert_zeuge`,
  `deviceCommon_mmio_ordnung_zeuge` (with `ordWitM`, `ordWit_kette`), probes
  `dev_probe_tso_verweigert`, `dev_probe_privileg_karte`, `dev_probe_privileg_schritt`,
  `dev_probe_privileg_dpl`, `dev_probe_pending_verweigert`. Full `CUTS` block and `#print
  axioms` for every main theorem.

## Verification

- `./lean-probe grammatik/Grammatik/X86/DeviceCommonExecution.lean`: 0 errors. Axioms are
  standard only (`propext`, `Quot.sound`, or none). No `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe` (grep clean). Every premise of every theorem is used.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed
  successfully (512 jobs).`

## What remains open / merger note

- The umbrella import `import Grammatik.X86.DeviceCommonExecution` at the end of
  `grammatik/Grammatik.lean` is NOT applied: this lane owns only its two files and the lane
  file permissions deny editing `Grammatik.lean`. The merger adds the one line (as usual for
  `Grammatik.lean` import conflicts). The file was verified standalone; its imports are all
  accepted umbrella members, so no cycle is possible (it imports only lower/peer producer
  modules, none of which import it).
- CUTS as tasked: hardware correspondence stays OPEN (as in 676/694); pending responses
  enumerated, never answered; no per-access target-to-W/GX simulation; no source/ABI/budget
  link.

## Task feedback

Nothing in the task was wrong. One interpretation worth recording: "privilege outcomes derived
through the 728 descriptor layer" was implemented as reuse (TSS window/CPL from `Steuerstand`,
accepted DPL check, shared #GP family) rather than routing IO permission through the IDT gate
check itself, which would be semantically wrong (IDT gates and IO bitmaps are different tables).
`geraetAntwort` takes 4 arguments (no port), which shaped the OUT successor terms.

