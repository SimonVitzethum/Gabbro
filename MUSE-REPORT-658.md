# MUSE-REPORT-658: Scalar FP final-byte validator admission and MXCSR entry

## What was done

New file `grammatik/Grammatik/X86/FloatValidatorAdmission.lean`
(+1 import line in `grammatik/Grammatik.lean`), implementing the lane
task: an independent OPTIONAL strengthened FP admission for actual
loaded scalar MOVSD/ADDSD bytes.

- **State interface (shared, not a new executor):** `fpBildT` builds the
  accepted `FpZustand` over `LoadedExecution.bildZustand` (canonically
  loaded image memory) with caller XMM/MXCSR. All execution goes
  through the untouched `fpByteschritt`/`fpSchritt`.
- **Admission Bool:** `valFpEintrittStark` = checked image mapping
  (`wohlgeformt`) AND entry containment (`eintragEnthalten`) AND
  executable byte at entry (`ladenAusfuehrbar`) AND successful
  fetch-and-decode of actual loaded bytes (`fpFetchDekodiert ... .isSome`,
  derived with `fpDecode`, never a caller-supplied `FpDecodiert`) AND
  MXCSR profile admission (`fpEintritt`) AND entry discipline
  (`mxcsrOk`) with the control word bound to the entry word
  (`k.mxcsr = z.mxcsr`).
- **Generic soundness:** `valFp_gibt_bereit` (readiness at `.sseDoppel`
  with OS vector state on), `valFp_gibt_bytes` (entry-at-decoded-start:
  containment, execute byte, decoder equation, length consistency,
  `laengeOk`, executable prefix, readiness), `valFp_schritt` (the same
  decoded step runs via `fpByteschritt`, successor keeps the admitted
  control word, mapping/entry/permission observations stay put).
- **Joint loaded FP STORE:** `fpStoreBild` (8 canonical
  `MOVSD [rbx+0], xmm0` bytes + data section at `0x2000`), accepted
  (`fpStore_wohlgeformt`, `fpStore_ok`), fetched (`fpStore_fetch`),
  executed (`fpStore_schritt`: `+∞` stored, reads back, top footprint
  byte observably changed) with executable bytes (`fpStore_code_bleibt`)
  and control word (`fpStore_fp_bleibt`) untouched.
- **Four planted refusals:** truncated bytes (`fpStumpf_verweigert`),
  FTZ word at three doors (`fpFtz_verweigert`), W^X map + data-section
  RIP (`fpMap_verweigert`), forged entry word
  (`fpEintritt_geschmiedet_verweigert`).
- **Joint witness:** `fpVal_gelenk_zeuge` pairs the admitted loaded FP
  store (real memory change) with the reached source table write from
  `FloatSourceObservations.null_beobachtung_zeuge` (slot `-0 -> +0`,
  disagreeing bit patterns). Side by side; no lowering claimed.

## Exact exported producer/consumer interfaces

Producers (for downstream source lowering / validator consumers):
`fpBildT`, `valFpEintrittStark`, `valFp_gibt_bytes`, `valFp_schritt`,
`valFp_gibt_bereit`, `fpStoreT`, `fpStore_schritt`, `fpStore_liest`,
`fpVal_gelenk_zeuge`, plus all seven projections
(`valFp_wohlgeformt/_eintrag/_ausfuehrbar/_fetch_exist/_fpEintritt/_mxcsrOk/_kontext`).
No new Rust/checker/emitter API; Lean-only consumer API.

## Verification

- `./lean-probe .../FloatValidatorAdmission.lean`: `0 error(s)`.
- `./lean-bau`: `Build completed successfully (458 jobs)`.
- Axioms: every theorem `propext` (+ `Quot.sound` / `Classical.choice`
  where inherited from reused producers, e.g. the joint witness via
  `null_beobachtung_zeuge`); standard goal axioms throughout. No
  `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. Every premise of
  every theorem is used.
- No file outside the owned new module (+ its one import line) was
  touched; no checker/Spec/goal/Rust/emitter/friend-reserved edit.

## What remains open (precise cuts, in-file CUTS block)

No `valX86_sound`; no source-to-final-loaded-bytes closure (IR287
pending); no hardware correspondence; sequential-only (TSO/GX bridge
with its owner); canonical subset only (low XMM/GPR, no REX;
control-word establishment from bytes open).

## Notes on the task text

- `ScalarFloatCodec565`, `FloatEntryState626`,
  `FloatSourceObservations624` resolve to the accepted
  `ScalarFloatCodec` / `FloatEntryState` / `FloatSourceObservations`
  modules in this clone (numbers are lane IDs, not filenames).
- No `ExtendedExecution575` file exists in this clone; the shared
  certificate/state interface used IS `FpZustand`/`fpByteschritt`
  (reused untouched), which such an extension can consume without
  conflict. Nothing was edited outside the owned file to achieve this.

## Next useful independent task

Prove the ADDSD register loaded-byte consequence through this
admission (fetched ADDSD computes the model sum into the low half on
the admitted loaded state, reusing `fpByteschritt_addsdRR_rechnet`),
or close one OPEN leg: relocation-patched FP byte re-decoding.
