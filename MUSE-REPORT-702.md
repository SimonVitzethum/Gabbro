# MUSE-REPORT-702: Essential scalar binary32 SSE2 architectural forms

Clone `/home/simon/Dokumente/gabbro-muse/a702`, branch `muse/702` — verified.
Owned files only: `grammatik/Grammatik/X86/ScalarFloat32HardwareForms.lean`
(new, 1851 lines), `grammatik/Grammatik.lean` (one additive import),
this report. No other agent/model calls, no network/push.

## What was delivered

Selected legacy SSE scalar SINGLE forms — MOVSS/ADDSS/SUBSS/MULSS/DIVSS/
UCOMISS/CVTSS2SD/CVTSD2SS/CVTSI2SS/CVTTSS2SI (18 `S32Befehl` constructors:
register + m32-memory arithmetic/compare, three MOVSS shapes, register
conversions with explicit REX.W width) — through the ACCEPTED genuine
binary32 kernel (`Gleitprofil.fadd32/fsub32/fmul32/fdiv32`,
`muster32`/`bites32`, `read32`/`write32`) on the ACCEPTED shared state
`FpZustand`. No new IEEE interpreter; no source/checker/Spec/goal/emitter
or friend-reserved file touched. 68 definitions, 141 theorems, zero
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `Prop`-typed premise,
every premise used.

- §1 32-bit lane: `xmmTief32`, `setzeTief32`, `xmmSchreibeTief32`
  (low-32 recovery, upper-96 and upper-64 preservation, foreign
  registers kept), `xmmLadeTief32` (load clears upper 96).
- §2 genuine f32 arithmetic `s32Rechne` (definitional routing to the
  kernel) with raw-bit witnesses: 1+2, +0+-0, subnormal growth,
  1/0=+inf, 0/0=NaN class, and the joint no-silent-promotion pair
  (`s32_stallt_bei_2hoch24`, `s32_f64_steigt_weiter`: f32 stalls at
  2^24 where f64 advances; reuses `f32_rundet_16777217` lineage).
- §3 conversions: `cvtSS2SD`/`cvtSD2SS` via `wertExakt`/`rundeExakt`
  (+ `wertExakt_none_klasse` justifying the fallthrough arms),
  `cvtSI2SS32/64` via direct `ofInt` at f32 (never via f64),
  `cvttSS2SI` with truncation and the hardware integer indefinite
  (32-bit zero-extended / 64-bit). `cvtt_trennt_vom_saettiger` proves
  bare CVTT is NOT the saturating wrapper `gleitRoh` (NaN gives
  `0x8000...` vs `0`).
- §§4-6 `s32Schritt` on shared `FpZustand` (length/profile/memory
  guards), 25 successor equations, frames: register-MOVSS preserves
  upper 96 vs memory-MOVSS clears them, arithmetic preserves them in
  both shapes, CVTSS2SD keeps upper 64, UCOMISS/CVTT touch only their
  documented state, store readback (`s32_speichere_liest_zurueck`),
  four-byte footprints (`read32_wert_klein`,
  `read32_braucht_lesbar`, `write32_braucht_schreibbar`), UCOMISS
  ZF/PF/CF rows.
- §§7-8 independent REX byte codec/decoder (F3/F2/NP families, REX.R/B
  high-XMM, REX.W width rows, REX.X refusal, opcode-first register-kind
  dispatch, SIB rule, both SIB shapes): 10 all-XMM register round
  trips, 4 memory round trips, closed high-register REX instances
  (`s32_rex_waehlt_hoch_addss`, both REX.W rows), cross-width
  (F2 arithmetic/MOVSD), prefix, REX.W/X, ModRM-mode, truncation and
  FTZ/sticky control refusals.
- §9 fetched `s32Byteschritt` from actual executable memory (reused
  `geholt`/`ausfuehrbarN`/`laengeOk`), fail-closed
  silicon/OS/profile gate (`S32Hw`, `s32Zugelassen`,
  `s32ByteschrittTor`), legacy upper-YMM preservation
  (`s32SchrittVoll_ymm`), and the joint fetched witness
  (`s32Zeuge_fetched_lauf`): fetched ADDSS then fetched MOVSS-store
  change real RAM (byte `0x2002` `0x00`->`0x40`) with exact readback,
  plus conversion witness, NaN-payload mutation (class agreement,
  differing bits), unreadable-memory refusal, and the overlap frame.

## Checks run (actual)

- `./lean-probe grammatik/Grammatik/X86/ScalarFloat32HardwareForms.lean`
  → `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` → `Build completed successfully (469 jobs).`
  (module built in 45s; umbrella `Grammatik` built; axiom lines are
  subsets of the standard set, e.g. `s32Zeuge_fetched_lauf` depends on
  `[propext, Quot.sound]`, `s32_nan_nutzlast_mutation` on none.)

## Provenance checked (exact)

Local snapshot `.tmp/HARDWARE-REFERENCES/` (`REFERENCES.json`, Intel
SDM 325462-093US September 2026): Vol. 1 Chap. 5 `INSTRUCTION SET
SUMMARY` §5.5.1.1 (MOVSS), §5.5.1.2 (ADDSS/SUBSS/MULSS/DIVSS),
§5.5.1.3 (UCOMISS), §5.5.1.6 (CVTSI2SS); Chap. 10 §10.4.1.2 (scalar
single stores the low doubleword); Chap. 11 §11.5.2.1–§11.5.2.4 +
Table 11-1 (masked responses: SNaN->QNaN, 0/0 and inf/inf->QNaN
indefinite, int-conversion invalid->integer indefinite). Vol. 2 opcode
pages are absent from the extracted `.txt`, so byte rows are stated
canonical contracts mirroring the accepted F2 rows — recorded in the
file header, never a silicon claim.

## Findings during the work (all repaired)

1. My first SIB decoder consumed one byte too many (off-by-one vs the
   encoder); the new memory round trips exposed it, fixed to the pilot
   shape.
2. `simp_all` over the memory round trips looped: my extra `natByte`
   in the simp set unfolded `natByte` to `ofNat` and broke the
   cons-lemma match (plus a stalled decoder dispatch). Mirroring the
   accepted simp recipe exactly fixed it.
3. Two of my own closed test expectations were wrong (REX 0x4D=77
   not 79; r/m=1 is rcx not rax) — the decoder was right both times.
4. `simp` normalizes `ofNat`-of-`toNat` to `setWidth` and OfNat
   literals unpredictably: statements were aligned to the normal form
   (`setWidth64_wert` bridge) and one witness rewrite was rephrased to
   avoid simp-normalized terms.
5. Structure-update terms must stay on one line in this toolchain's
   parser (multi-line `{ x with ..., ... }` failed to parse).

## Open (essential, in file CUTS)

NaN payload/quiet-bit discipline of computed results; SNaN vs QNaN;
rounding beyond RNE/witnessed rows; DAZ/FTZ execution; sticky-flag
accumulation; denormal conversion inputs; all-input CVTSS2SD
exactness; memory-source integer conversions; VEX/EVEX and AVX
zeroing; packed SIMD; TSO tearing/GX bridge; fault delivery beyond
explicit refusal; timing/budget; integration into `decodeExt`/`stepExt`
and a single-precision `PerfMerkmal` feature (local `S32Hw` gate is the
sharing point). Lane 668 (f64 sibling) was still unmerged at probe
time, so no interface of it was assumed: sharing is by construction
over `xmmTief32`/`mxcsrGueltig`/`FpZustand`, documented in CUTS.

## On the task text

Nothing factually wrong found. One scoping note: the task's "stable
generic raw-state/MXCSR adapter with 668 once accepted" could not be
concretized because 668 is unaccepted; the module instead exposes the
narrow shared surface both lanes already reuse and names the exact
integration points. No desired correctness is hidden in premises; no
subset is claimed as closure.
