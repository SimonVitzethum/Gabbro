# Muse Report 575: Unified extended decoder and executable byte-step

## Task
Assemble the ACCEPTED extension decoder interfaces into ONE selected-profile
byte-facing execution path over canonical `Codec.decode` /
`Ausfuehrung.schritt` (14 pilot forms) plus one new-form family per accepted
helper, with actual-memory fetch/execute permission, disjoint prefix
dispatch, exact evaluation selection, and a mixed reached run changing
actual memory from fetched bytes.

## Deliverable (owned paths only)
- `grammatik/Grammatik/X86/ExtendedExecution.lean` (new, ~830 lines)
- `grammatik/Grammatik.lean` (additive umbrella import, one line)
- this report

## What was built
- `ExtInstr`: pilot + narrow + muldiv + shift + setcc + cmov + fp + vec.
- `extLen`, `decodeExt`: sequential fallback (pilot, narrow, muldiv,
  shift, SETcc, CMOVcc, scalar FP, packed integer). Dispatch theorems
  `decodeExt_kanonisch/_narrow/_muldiv/_shift/_setcc/_cmov/_fp/_vec/_nichts`.
- Whole-chain pins per family (`pin_ext_*`: ret, mov32, mul, shl-imm,
  setcc, cmov, movsd, pxor, empty, unknown opcode) plus explicit
  pilot-refusal pins (`pin_pilot_weist_*`) so no pilot form is shadowed.
- `ExtAusgang` (weiter/halt/verweigert), `stepExt` with 18 selection
  theorems routing each arm to its accepted evaluator (`laufAlt`,
  `stepNarrow`, `mulDivSchritt`, `shiftSchritt`, `setccSchrittBytes`,
  `cmovSchrittBytes`, `fpSchritt`, `stepVector`). Divide trap is `halt`.
- `extZugelassen` + `fetchExt` + `extByteschritt`: actual-byte fetch
  (`Byteschritt.geholt`), consumed-length check, `laengeOk`, execute
  permission (`fetchExt_erfolg` extracts all four facts).
- Reached witness: image = pilot `store64` (7 B) ++ FP `movsdSpeichere`
  (8 B); two byte-steps store 42 into two data cells, RIP 4096 -> 4111,
  cells start zeroed. Joint `_zeuge` adds the past-image refusal.
- Planted refusals: past-image RIP (`extWit_nachBild_verweigert`),
  packed-integer without OS state (`extWit_vec_ohne_os_verweigert`).

## Verification
- `./lean-probe`: 0 errors. `./lean-bau`: success, 458 jobs, including
  `Grammatik.X86.ExtendedExecution` and umbrella `Grammatik`.
- `#print axioms`: `[propext]` to `[propext, Quot.sound]` only; no
  `sorry/admit/axiom/native_decide/unsafe`; goal axioms untouched
  (nothing near `Zielsatz/Spec.lean` was modified).

## Apparatus findings (2, both handled in-lane)
1. `lean-probe` crashed repeatedly with `failed to create thread`
   (exit 134) once the file grew past ~10 `simp only [stepExt, h]`
   selection proofs, under heavy host swap pressure (7+ GiB swap used
   by the user's own processes, which were not touched). Bisected to
   cumulative elaboration load, not one bad theorem.
2. Fix: all selection proofs rewritten to kernel-cheap
   `have e : ... := rfl; rw [e, h]` style; the one proof needing
   pair injectivity uses `simp`-injected `h` + `rw`. No proof was
   weakened. Recommendation: lanes doing heavy `simp` with big
   match-definition equation sets should prefer `rfl`-equation +
   `rw` under load.

## What remains open (CUTS, also in file)
No hardware correspondence; no LOCK; SIMD only PXOR/PADDQ + four
scalar-DOUBLE byte rows; no source/IR/TSO/GX/ABI/loader/entry/budget
connection; high XMM/REX FP forms refused by absence; divide `halt`
carried, not proved.

## Stable producer/consumer interface for next integration
- Producer: `decodeExt : List Byte -> Option (ExtInstr x List Byte)`,
  `extLen`, `stepExt : ExtInstr -> FpZustand -> BereitProfil ->
  ExtAusgang`, `fetchExt`, `extByteschritt : FpZustand ->
  BereitProfil -> ExtAusgang`.
- Consumer contract: fetch a window with `geholt`, admit with
  `fetchExt_erfolg`, step with `extByteschritt_weiter`.
- Measurable next step: a loaded-image runner placing `extWitBild`
  through `Bild`/relocation mapping and re-decoding (owners 559-561
  interfaces), or a W-bridge consumer reading `stepExt` footprints.

## What I believe is wrong in the task
Nothing blocking. One note: "Show a mixed reached pilot-integer/FP
or narrow/store run" is satisfied by pilot-store + FP-store; a
narrow row run from fetched bytes is not shown (narrow dispatch and
step selection are proved and pinned, only the end-to-end narrow
memory run is absent). A follow-up can add it in ~10 lines.
