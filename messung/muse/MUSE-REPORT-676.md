# MUSE-REPORT-676: Port IO and device memory profiles

## Branch / scope

- Clone `/home/simon/Dokumente/gabbro-muse/a676`, branch `muse/676` (verified).
- OWN ONLY: `grammatik/Grammatik/X86/DeviceHardwareForms.lean` (new, ~1370 lines),
  `grammatik/Grammatik.lean` (one additive import line), this report.
- No source/checker/Spec/goal/emitter file touched; no friend-reserved
  optimiser file touched; no syscall/interrupt scope (lane 672).

## What was built

Exact selected port instructions (IN/OUT, widths 8/16/32, immediate-port
versus DX-port forms) with canonical byte encode/decode, fetched execution
over canonical `Zustand`, a finite privilege profile, a typed memory-kind
interface (RAM admitted, MMIO/DMA refused), and a GENERIC hardware
device-response interface (data register plus observation counter, ordered
IO events, no OS/library contract). Reuses canonical `Zustand`/`Speicher`/
`TSO`-vocabulary only by reference: device bytes never enter a RAM TSO
buffer by construction (no `TSOZustand` appears); accumulator effects reuse
the accepted `mergeRegNarrow`/`trunc` (8/16-bit preserve upper bits,
32-bit zero-extends); fetch follows the `fetchDekodiert` discipline
(`geholt`, length equation, `laengeOk`, `ausfuehrbarN`).

Key definitions: `IoBreite`, `IoDir`, `PortQuelle`, `IoOp`, `IoDec`,
`ioBreiteBits/Bytes`, `breiteAusNat`, `encodeIo`, `ioLen`, `decodeIo`,
`IoProfil`, `ioZugelassen`, `ioProfilZeuge`, `SpeicherArt`,
`SpeicherProfil`, `speicherArtZugelassen`, `speicherProfilZeuge`,
`GeraetZustand`, `IoEreignis`, `ioMaske`, `geraetAntwort`, `portVon`,
`ausGabe`, `einMische`, `IoZustand`, `ioSchritt`, `fetchIo`,
`ioByteschritt`, `hw660Schritt`, `hw660Laenge`, `ioValOk`,
witness image/state/run `ioWitBild/Bytes/Code/Daten/Speicher/Reg/Kern/
Start/Schritt1-3`, observers `ioBeobAkk/Rip/Geraet/Spur`.

Main theorems: `roundtripIo` (+12 per-form round trips),
`decodeIo_consumes` (arbitrary-input length soundness),
`ioZugelassen_heisst_alle` + 3 refusal directions + `ioZugelassen_zeuge`,
`speicherArt_zeuge`, device facts + `geraetAntwort_zeuge`,
`ausGabe_passt`, `ausGabe_ist_trunc`, `einMische_p32_fits` + 3 pins,
`ioSchritt_*` selection/refusal/frame facts (memory never touched,
flags kept, RIP advanced, one ordered event, OUT keeps registers),
`fetchIo_erfolg`, `ioByteschritt_weiter/verweigert`,
`hw660Schritt_kern/xmm/fp/verweigert`, `ioValOk_heisst/_zeuge`,
joint `ioWit_lauf_zeuge` (fetched IN answers 52, fetched OUT stores 52
into the device, pilot store moves 52 into real cell 8192 from zero,
plus pilot-byte and privilege refusals), companions
`decodeIo_consumes_zeuge`, `ioSchritt_aus/ein_erfolg_zeuge`,
`ioZugelassen_heisst_alle_zeuge`, `hw660Schritt_xmm/fp_zeuge`,
`hw660Schritt_zeuge`, plus planted refusals (empty/truncated/unknown/
pilot-RET/prefix/width-24/width-64/port-0x61/IOPL/switch/forged-byte).

## Verification

- `./lean-probe grammatik/Grammatik/X86/DeviceHardwareForms.lean`:
  `== 0 error(s)`, exit 0.
- `./lean-bau`: `Build completed successfully (460 jobs).`
- `#print axioms`: main theorems depend on subsets of
  `[propext, Classical.choice, Quot.sound]` (standard `gabbro_ziel`
  set; `Classical.choice` inherited from reused `narrowTruncMod`/
  `mergeRegNarrow_b32_fits` only). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` (checked by search; only the English word
  "admitted" matches).
- No premise has type `Prop` itself; every premise is used
  (selection/frame/refusal shape throughout).

## What remains OPEN (see CUTS)

- No hardware correspondence: `.tmp/HARDWARE-REFERENCES/REFERENCES.json`
  is absent on this machine, so no manual heading/page is cited;
  encodings are a stated canonical subset (E6/E4/E7/E5/EE/EC/EF/ED
  plus 0x66 16-bit forms) with self-consistency only.
- MMIO/DMA refuse by admission; their memory-type/order rules are
  unmodelled. No INS/OUTS/REP, no timing, bitmap population is user logic.
- `hw660Schritt`/`hw660Laenge` export the 660 adapter against the
  documented interface expectation; owner 660 confirms the fit.
- Full system/device scope OPEN where an essential emitted device form
  lacks covered architectural rules.

## Task remarks believed correct to flag

- The task's "negative port-width" case is covered as non-selected-width
  refusal (`breiteAusNat_24_verweigert`, `breiteAusNat_64_verweigert`);
  widths are an inductive, so negativity is unrepresentable by construction.
- "Stores a received value into real canonical memory" is composed, not
  single-stepper: the port stepper provably never touches `Speicher`
  (`ioSchritt_speicher`), and the reached pilot store moves the received
  word -- port and pilot execution share the one `Zustand`.
