# MUSE-REPORT-857: Composition closing — permission-check closing

## Task
Close the per-access permission check to the fetch/decode/execute chain:
unchecked access is unrepresentable, not merely absent. Compose
already-accepted modules into one checked closing step; never re-prove
their internals, never duplicate an interpreter or executor. Prove the
composition generically over arbitrary admitted inputs, with reached
memory-changing runs plus planted refusal cases. Missing producer legs are
explicit CUTS, never assumed.

ZEUGE: `ComposePermCheck_verbindung` with companion
`ComposePermCheck_verbindung_zeuge` (jointly inhabited, non-degenerate,
memory-changing reached run).

## What was done
New module `grammatik/Grammatik/X86/ComposePermCheck.lean` (registered at
the end of `grammatik/Grammatik.lean`; no other existing file touched),
closing this producer/consumer interface:

- Producers: the accepted permission primitives (`Speicher.read64` /
  `write64` with their `lesbar8` / `schreibbar8` checks, `Byteschritt`
  fetch with its `ausfuehrbarN` check) and the accepted step/footprint
  theorems (`Zugriffe` extraction equations + `schritt_*_verweigert`
  refusals, `AccessExecution.byte_aus_weiter`,
  `Byteschritt.fetchDekodiert_entspricht` /
  `byteschritt_verweigert_ohne_schritt`,
  `WordAtomicity.read64_braucht_lesbar` / `write64_braucht_schreibbar`,
  `Speicher.write64_verweigert`, `Zugriffe.fuss_mem`).
- Consumer: the checked closing step, which runs only the existing
  `byteschritt` — a conjunction of checks is not execution.

New definitions:
- `PermGeprueft (s : Zustand) (d : Decodiert) : Prop` — consumed fetch
  prefix executable plus every footprint byte permission-checked.
- `permStoreDec`, `permStoreRest`, `permStoreReg`, `permStoreBytes`,
  `permStoreErlaubt`, `permSchreibVerweigertStart` — witness vocabulary:
  one accepted `store [rbx], rax` encoding at 4096, executable code apart
  from readable/writable data (allowed twin) vs write-denied twin.

New theorems:
- `lesbar8_gibt_byte`, `schreibbar8_gibt_byte` (checked 8-byte footprint
  grants each byte; via accepted `fuss_mem`), `lesbar8_aus_byte_falsch`,
  `schreibbar8_aus_byte_falsch` (contrapositives),
  `read64_aus_lesbar_falsch` (mirrors accepted `write64_verweigert`).
- `zugriff_perm_aus_schritt` — success direction over all 14 pilot forms:
  realised reads went through `read64`, realised writes through `write64`,
  pure forms touch no byte.
- `schritt_versagt_ohne_perm` — refusal direction: one denied footprint
  byte admits no transition.
- `ComposePermCheck_verbindung` — the closing, generic over arbitrary
  states: every realised byte step yields its fetched instruction with
  fetch-permission agreement, per-byte footprint permissions and the
  running `schritt`; any footprint permission failure on a fetched
  instruction refuses the byte step.
- `perm_fetch_store`, `perm_fetch_store_verweigert` (fetch pinning, both
  twins decode identically — fetch never consults data permissions),
  `perm_schreib_erlaubt_schreitet` (byte 8192 zero to 7 through the
  composed step), `perm_schreib_verweigert_rip`,
  `perm_schreib_verweigert` (planted data refusal; refusal proved via the
  accepted `ausgangRip` pattern since `ByteAusgang` equality is not
  decidable), `ComposePermCheck_verbindung_zeuge` (joint witness: pinned
  8-byte store footprint at 8192 with zero-to-7 change, refusal direction
  derived through the closing on the denied twin, execute-denied refusal).

## Verification
- `./lean-probe …/ComposePermCheck.lean`: `== 0 error(s) …; exit 0`
  (final; two intermediate failures repaired: undecidable `decide` goal
  reworked to the `ausgangRip` pattern, one `List.Mem` anonymous-constructor
  fix via `fuss_mem`).
- `./lean-bau` (full project): `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (511 jobs).`
- Axioms: every new theorem depends only on `[propext, Quot.sound]` or
  `[propext]` — within the standard goal set; no `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe` (grep shows only comment words and
  `#print axioms` lines).
- `gabbro_ziel` axioms: not re-printed (no wrapper for it); unaffected by
  construction — no existing Lean file was modified except the additive
  import line in `Grammatik.lean`, and the full 511-job build (which
  includes the Zielsatz) is green.

## What remains open (also in the file CUTS)
- No extended-ISA closing: narrow, mul/div, shift, SETcc/CMOVcc, scalar
  FP, packed-integer, LOCK/RMW/fence forms have no `zugriff` extraction;
  their per-access permission legs stay with their owners.
- No TSO/W/GX bridge (footprints stay byte sets), no source/image/entry/
  ABI/relocation/cost claims; `verweigert` is absence of transition.

## Task assessment
Nothing in the task statement appears wrong. The pilot-only scope is
honest: the composition is generic over all 14 admitted pilot forms, and
the extended forms are named as CUTS with their owning lanes rather than
assumed. No numbers, counters, source/checker/Spec/emitter files, or
friend-reserved optimiser files were touched.
