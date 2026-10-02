# MUSE-REPORT-694: UC MMIO architectural access and ordering

Lane 694, clone `/home/simon/Dokumente/gabbro-muse/a694`, branch `muse/694`.
OWN ONLY: `grammatik/Grammatik/X86/MemoryTypeHardwareExecution.lean` (new, 1440 lines),
`grammatik/Grammatik.lean` (one additive import line), this report.

## What was done

Closed selected UC MMIO read/write behavior and ordering as a disjoint producer
(no import of unmerged lane 676, no edits outside the owned files). Normal WB RAM
keeps the accepted TSO discipline (referenced as explicit `pending` state, never
redefined); selected UC device access follows documented architecture constraints
with one generic named hardware device-response interface (`Geraet`).

Provenance checked (local `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
Intel SDM 325462-093US, September 2026): Vol.1 §20.5 (UC MMIO program order on the
pins; chipsets may post UC writes), Vol.3A §14.3 Table 14-2 incl. x87/SIMD UC
re-access NOTE (only GP-register forms admitted to UC), §14.3.3 (UC code-fetch
limits noted), §§11.1.2/11.2.5 (UC lock serialization; no universal fence claimed).
No AMD provenance (retrieval failed); nothing about silicon or vendors is claimed.

Key mechanics:

- UC membership (`istUc`/`decktUc`) by explicit software-established region list;
  WB is the uncovered default. No trusted `osMemoryOk` Bool: every UC step carries
  membership, window (`imFenster`), and width-admission (`breiteZugelassen` over the
  accepted `HwProfil`/`BereitProfil`) checks.
- Generic device: 8-byte window at 65536, width-indexed LE reads/writes, an access
  counter (reads observably have side effects); exact counter and refusal lemmas.
- CPU-retired UC stores are POSTED (`ausstehend`), never WB-buffered, never
  device-applied (`ucStore_bypass`); only FIFO `busFortschritt` completes them.
  UC loads over overlapping posted writes refuse (no silent forwarding).
  UC-UC program order is the event log; pending WB stores are preserved by every
  UC and bus step (explicit non-drain; a stale WB entry seeds the witness).
- Fetched level reuses the accepted dispatcher: `fetchExt` over actual executable
  memory, `stepExt` for every non-UC instruction (delegiert), `effAddr`/`ripNach`/
  `mergeRegNarrow`/`trunc` reused. Covered fetched forms: pilot 64-bit load/store,
  narrow 32-bit store. All seven accepted FP DOUBLE memory rows addressing UC
  refuse (`fpUcBetroffen`); vector rows are register-only and delegate.
- Joint reached run (all `decide`-computed from fetched bytes): fetched UC store
  of 42 (RIP 4096→4103, posted, device still 0) → bus completion (device byte 42,
  queue drained) → fetched UC load (rcx = 42, counter = 2) → fetched WB store
  (RAM[8192] = 42, RIP 4117, log ordered, stale WB store preserved).
- Planted refusals: wrong-kind (empty profile delegates to unwritable RAM),
  FP-to-UC, past-image, width straddle, 64-bit wrap, missing profile, missing
  silicon, overlapping posted write. Footprint disjointness device-vs-RAM proved.
- `ucStore_bypass_zeuge`, `busFortschritt_fifo_zeuge`, `wit_joint_zeuge` jointly
  instantiate the main results with memory-changing reached runs.

## New definitions/theorems (exact names, namespace `Gabbro.Grammatik.X86`)

Defs: `UcProfil`, `decktUc`, `istUc`, `breiteMerkmal`, `breiteZugelassen`,
`geraetBasis`, `Geraet`, `geraetAnfang`, `geraetOff`, `imFenster`, `fin8`,
`datenSetze`, `geraetLiest`, `geraetSchreibt`, `UcEreignis`, `PostedSchreib`,
`MmioMaschine`, `MmioAusgang`, `postedUeberlappt`, `ueberlapptPosted`,
`ucStoreZugriff`, `ucLoadZugriff`, `maschineRegLaden`, `busFortschritt`,
`fpUcBetroffen`, `delegiert`, `maschineSchrittWeiter`, `mmioByteschritt`,
witness defs `witBild`, `witBytes`, `witCode`, `witDaten`, `mmioWitSpeicher`,
`mmioWitReg`, `witKern`, `witFp`, `witProfil`, `witDevAddr`, `witM0`,
`witSchritt1`, `witBus`, `witSchritt2`, `witSchritt3`, accessors `witRip`,
`witRam`, `witRegAus`, `witGeraetByte`, `witZaehler`, `witLog`, `witPosted`,
`witPending`, `witVerweigert`, `witFpBild`, `witFpBytes`, `witFpCode`,
`witFpSpeicher`, `witFpReg`, `witFpKern`, `witFpM0`, `witM0HinterBild`,
`witM0Posted`.
Theorems: `istUc_leer/kopf/mem`, `breiteZugelassen_hat/bereit`, `nicht_wahr`,
`imFenster_off/ohneUmbruch`, `fin8_gleich/nichts`, `datenSetze_gleich/anders`,
`geraetLiest_zaehlt`, `geraetSchreibt_zaehlt`, `geraetLiest/schreibt_b8_verweigert`,
`ueberlapptPosted_leer`, `ucStoreZugriff_erfolg`, `ucStore_bypass`,
`ucStore_verweigert_ohne_profil/fenster/merkmal`, `ucLoadZugriff_erfolg`,
`ucLoad_verweigert_bei_ausstehend`, `ucLoad_rahmen`, `busFortschritt_leer/fifo`,
`fpUcBetroffen_speichere/lade`, `maschineSchrittWeiter_rip/ucLog/speicher/flags/
register/xmm/fp/pending/ausstehend`, `mmioByteschritt_ohne_fetch`,
`mmioByteschritt_uc_laden/speichern/speichern32`,
`mmioByteschritt_delegiert_laden/speichern`, `mmioByteschritt_fp_uc_verweigert`,
`mmio_uc_speichern/laden_fakten`, `wit_s1_rip/posted/geraet_noch_null`,
`wit_bus_geraet/geleert`, `wit_s2_reg/zaehler`, `wit_s3_ram/geraet/log/rip`,
`wit_anfang_ram`, `wit_pending_erhalten`, `wit_joint_zeuge`,
`wit_falsch_art/fp_uc/nachBild/fenster/umbruch/profil/merkmal/ueberlapp_verweigert`,
`wit_fuss_disjunkt`, `ucStore_bypass_zeuge`, `busFortschritt_fifo_zeuge`.

## Last check results

- `./lean-probe grammatik/Grammatik/X86/MemoryTypeHardwareExecution.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (467 jobs)`, file green.
- `#print axioms` for all 22 main theorems: only `propext`, or
  `propext + Quot.sound`. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- `grammatik/` untouched except the owned module + one import line; no source,
  checker, Spec, goal, emitter or optimizer files touched.

## What remains open (see CUTS in the file)

UC-vs-WB is closed for the selected window; the full hardware model is not:
WC/WT/WP/NT/DMA have no profile kind here; fetched 8/16-bit forms and 32-bit
fetched loads have no accepted decoder rows (access-level widths exist, byte path
refuses); no completion liveness/fairness/timing; no interrupt/LOCK/fence
integration beyond bypass/preservation; no UC code-fetch gating; richer device
semantics refine the counter interface; no source/checker/goal correspondence.
Missing essential MMIO beyond this scope keeps the milestone OPEN by design.

## Task notes / disagreements

- The task asks for "fetched scalar selected 8/16/32/64-bit load/store forms".
  Only pilot-64 and narrow-32-store have accepted decoder rows; inventing
  8/16-bit decoders here would collide with the codec lanes, so fetched coverage
  is exactly the decoded subset and the rest is access-level plus explicit
  refusal. I consider this the correct reading, not a task error.
- The task's "no trusted osMemoryOk Bool" is honored structurally: the profile
  is an explicit region list and every UC step re-checks membership, window and
  feature admission; the profile list itself is data supplied by software logic.
- Two Lean syntax lessons recorded for other lanes: function-application
  arguments must not continue on a less-indented line; struct-instance fields
  with trailing commas must stay on one line (newline-separated fields take no
  commas); `.b64`-style literals fail inside named struct-instance fields
  (positional `⟨…, Breite.b64, …⟩` works).
- Name collisions avoided: `witSpeicher`/`witReg` already exist in
  `ControlFlow.lean`; mine are `mmioWitSpeicher`/`mmioWitReg`.
