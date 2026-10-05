# MUSE-REPORT-1135: CPUID/feature enabled-state gating inside HwSchritt

## What was done

NEW FILE `grammatik/Grammatik/X86/HwFeatureGates.lean` (~700 lines, 46 theorems),
plus one `import Grammatik.X86.HwFeatureGates` line in `grammatik/Grammatik.lean`.
No other file touched; every accepted definition reused unchanged (lifted, never
redefined or copied).

- §1 Gate predicates: `hwTorMerkmal` (ExtInstr → Option PerfMerkmal), `hwTorBereit`
  (finite `merkmalZugelassen` on `m.hw`/`m.bereit c`), `hwTorZustand` (`fpEintritt`/
  `vecEintritt`), `hwTorBeobachtet` (`beobachtungsTor` over reached CPUID/XCR0
  answers), `hwTorOffen` (conjunction), `hwTorFehler` (closed = `ArchFehler.ud`).
- §2 Generic refusal over ALL dispatcher families (`hwTor_verweigert_bei_zustand`,
  case split over `ExtInstr`), incl. the `m.bereit c` profile leg for the vector arm
  under present silicon (`hwTor_vec_bereit_verweigert` via `vecEintritt_merkmal`).
- §3 Family event type `HwTorEreignis`, `HwAdapter` plug `adapterFeatureTor`
  (refusal/admission equations), gated relation `HwTorSchritt` with exact
  `HwSchritt.reg` embedding (`hwTorSchritt_ok_reg`), `HwWf` preservation and
  #UD classification of the refused leg.
- §§4-5 Closed Bool gate equations, executed vector (PXOR) + scalar-FP (MOVSD)
  steps with unchanged memory, TSO issue/drain facts, planted refusals per closed
  leg (OS state off, FTZ word, absent observed bit).
- §§6-7 Half-gated two-core machine (core 0 executes, core 1 takes #UD), closing
  theorem `hwTor_verbindung` (admitted step + exact embedding + Wf + gate/step
  fault silence + TSO forward/drain leg, every premise used) and joint witness
  `hwTor_verbindung_zeuge` (15 conjuncts: two executed family steps, 0→42 memory
  change, owner-only forwarding, three #UD refusals).

## Exact names

Definitions: `hwTorMerkmal`, `hwTorBereit`, `hwTorZustand`, `hwTorBeobachtet`,
`hwTorOffen`, `hwTorFehler`, `HwTorEreignis`, `adapterFeatureTor`, `HwTorSchritt`,
`hwTorWitV`, `hwTorWitF`, `hwTorWitT'`, `hwTorWitU'`, `hwTorUnbereit`, `hwTorFtz`,
`hwTorS1`, `hwTorS2`, `hwTorHalb`. Main theorems: `hwTor_verweigert_bei_zustand`,
`hwTorSchritt_ok_reg`, `hwTorSchritt_wf`, `hwTorSchritt_ud_klasse`,
`hwTor_verbindung`, `hwTor_verbindung_zeuge` (plus 40 supporting lemmas, see file).

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwFeatureGates.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (601 jobs)`.
- `#print axioms` for all 46 theorems: only `[propext]` or `[propext, Quot.sound]`
  (standard subset; no `Classical.choice` even needed).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no new `axiom`; one
  definition checked per addition; English only.

## What remains open / honest limits

- Scalar-FP `BereitProfil` leg, CPUID-observation leg and silicon-absent profile
  refusal are wrapper-enforced (`HwTorSchritt`/`adapterFeatureTor`), NOT
  step-enforced: the accepted FP step ignores `BereitProfil` and no accepted step
  reads CPUID answers (stated in CUTS).
- Memory-touching family forms must use the `HardwareExecution` issue events, never
  the register plug (same discipline as `adapterInteger666`).
- No new silicon claim: all encodings/bit positions/fault classes are the accepted
  producers' (provenance in their CUTS; snapshot `.tmp/HARDWARE-REFERENCES/`,
  Intel SDM 325462-093US). Two SDM text greps for #UD-row phrasing found nothing
  (phrasing differs) and one `bash` listing of that dir was rejected by the
  permission classifier; neither affects the result since nothing new is claimed.
- No source/checker/emitter correspondence, no per-access W/GX bridge, no
  image/loader/entry/budget link (all in CUTS).

## What I believe is wrong in the task (minor)

- "a theorem about EVERY admitted family step" for `m.bereit c` holds at step level
  only for the vector arm; the FP arm's `BereitProfil` leg is genuinely absent from
  the accepted `stepExt` (it reads `t.fp`, not `b`). Delivered wrapper-enforced
  instead, documented. Nothing was weakened to fit.
