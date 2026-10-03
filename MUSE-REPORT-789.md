# MUSE-REPORT-789: Hardware completion: CVTSI2SD from 64-bit int

## Task
Lane 789: cover int64-to-binary64 conversion with the width obligation
and RNE rounding, pinned bytes, refusal of unadmitted widths, reusing
canonical `Zustand`/`FpZustand`/`Speicher`/TSO vocabulary and the
accepted `ExtendedExecution` byte-facing dispatcher; never duplicate
old arithmetic or source interpreters. Ground encodings in the official
local manuals. Target: `Cvtsi2sdW64_verbindung` with companion
`Cvtsi2sdW64_verbindung_zeuge`.

## What was done
Created `grammatik/Grammatik/X86/Cvtsi2sdW64.lean` (new file, 324 lines)
and added `import Grammatik.X86.Cvtsi2sdW64` at the end of
`grammatik/Grammatik.lean`. No other file touched: no diagnostic/gift/
example/CLI numbers, no `MARKE_EMIT` changes, no source/checker/Spec/
goal/emitter edits, no friend-reserved optimiser files.

The module is a thin completion over accepted work, reusing (never
redefining): `ScalarFloat` (`FpZustand`, `fpSchritt`, `cvtsiErg`,
`xmmSchreibeTief_tief`, `fpSchritt_cvtsi2sd*`, `cvtsiErg_42`),
`Gleitprofil` (`ofInt`/`rundeExakt`, `mxcsrRundungRNE`), and
`ScalarFloatHardwareForms` (`fpHwEncodeCvtsi`, `fpHwDecode`,
`fpHwByteschritt`, `fpHwFetchDekodiert`, round trips, refusal pins,
W2 witness states/theorems).

Sections:
- §1 pinned bytes: `cvtsiW64_len` (5 bytes), `cvtsiW64_roundtrip`
  (decode inverts encode over the full register file),
  `cvtsiW64_pilot_weist_zurueck` (pilot disjointness).
- §2 width obligation: `cvtsiW64_w0_verweigert` (REX.W = 0 refuses:
  doubleword source vs the whole-register conversion),
  `cvtsiW64_speicher_verweigert` (memory-source bytes refuse:
  register sources only, no second evaluator).
- §3 RNE rounding: `cvtsiW64_ist_rne` (`cvtsiErg` IS `ofInt f64`,
  hence `rundeExakt` RNE), `cvtsiW64_rne_pfand` (exact-value RNE
  path), `cvtsiW64_profil_rne` (admitted MXCSR carries RNE control),
  `cvtsiW64_42` (`42` -> `42.0` pattern).
- §4 fetched execution: `cvtsiW64_rechnet`, `cvtsiW64_flags`,
  `cvtsiW64_speicher`, `cvtsiW64_hoch` (each runs the accepted
  `fpSchritt` equation via the accepted gated byte step from an
  explicit fetch premise).
- §5 `Cvtsi2sdW64_verbindung`: the conjunction (RNE value, flags
  preserved, memory preserved, high half preserved per legacy SSE,
  RIP past decode length). Every premise is used.
- §6 `Cvtsi2sdW64_verbindung_zeuge`: joint witness instantiating
  ALL connection premises together on the accepted W2 image
  (`xmm0`/`rax`, `fpHwW2_fetch1`, `rfl`, `fpHwW2Fp`,
  `fpHwW2Gate1`, `fpHwW2_schritt1`), concluding the converted value
  plus a reached second fetched store step with real memory change
  (`fpHwW2_schritt2`, `fpHwW2_liest`, `fpHwW2_aendert`: word reads
  back `0x4045000000000000`, top footprint byte changed).

Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
`REFERENCES.json` (Intel SDM 325462-093US, September 2026):
opcode rows txt lines 48890-48895 (`F2 0F 2A /r`, `F2 REX.W 0F 2A /r`),
description txt lines 48921-48924 (width split, low quadword stored,
high unchanged, MXCSR.RC rounding), operation txt lines 48969-48976
(`DEST[63:0]` conversion, `DEST[MAXVL-1:64]` unmodified).

## Exact new names
`cvtsiW64Breite`, `cvtsiW64Breite_ist64`, `cvtsiW64_len`,
`cvtsiW64_roundtrip`, `cvtsiW64_pilot_weist_zurueck`,
`cvtsiW64_w0_verweigert`, `cvtsiW64_speicher_verweigert`,
`cvtsiW64_ist_rne`, `cvtsiW64_rne_pfand`, `cvtsiW64_profil_rne`,
`cvtsiW64_42`, `cvtsiW64_rechnet`, `cvtsiW64_flags`,
`cvtsiW64_speicher`, `cvtsiW64_hoch`, `Cvtsi2sdW64_verbindung`,
`Cvtsi2sdW64_verbindung_zeuge`.

## Verification
- `./lean-probe grammatik/Grammatik/X86/Cvtsi2sdW64.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
  Axioms: marker/width/RNE-identity/42 with no axioms; round trip,
  pilot/width refusals and profile-RNE with `[propext]` (plus
  `[Classical.choice, Quot.sound]` on the memory-decode refusal via
  inherited `parseLe32`); step/connection lemmas with
  `[propext, Quot.sound]`; joint witness with
  `[propext, Classical.choice, Quot.sound]` -- all within the
  standard `gabbro_ziel` set. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`; no `Prop`-typed premise; every premise
  used.
- `./lean-bau` (whole `grammatik/`): NOT green at report time for
  apparatus reasons outside this lane: our module plus 483 others
  build (`[484/485] Building Grammatik`), then the final
  `Grammatik.lean` import-all link step fails intermittently with
  `std::bad_alloc`, `failed to create thread`, or stale
  `.olean.private` reads (toolchain/stdlib oleans), varying run to
  run. `./lean-probe` on an unrelated large module
  (`VectorIntegerHardwareForms.lean`) fails the same way
  (`failed to create thread`), confirming machine-wide resource
  exhaustion under ~15 concurrent models, not a defect of this
  file. Retried 5 times with identical 484/485 progress and varying
  link-step errors. Last line: `error: build failed`
  (`[484/485] Building Grammatik`, `failed to create thread`).

## What remains open
- A quiet-machine `./lean-bau` re-run to confirm the whole project
  green with this import added (expected: green; the lane file is
  probe-green and adds no new build dependency beyond two accepted
  imports).
- The inexact input case (`2^53+1` ties-to-even at binary64) is
  covered abstractly (`ofInt` IS `rundeExakt` RNE) rather than by a
  closed `decide`: a concrete large-value `decide` was avoided as a
  build-cost risk under the current resource pressure.
- Silicon correspondence stays OPEN by design (byte shapes are
  stated contracts, round-trip consistency is not hardware proof).

## Task feedback
Nothing in the task is believed wrong. Note: the accepted
`ScalarFloatHardwareForms` W2 witness already executes a fetched
REX.W CVTSI2SD (`rax = 42`) into a store; this lane adds the missing
dedicated width-obligation/RNE/connection layer on top without
duplicating that execution, which is why the witness reuses W2
states and theorems rather than forging a second image.
