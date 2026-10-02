# MUSE-REPORT-674: SIMD and architectural enabled-state gates

## Task

Lane 674 (hardware completion): close architectural enabled-state and actual
vector byte-execution admission for the selected SSE2 packed-integer tier,
replacing the bare `BereitProfil.osXmm` Bool with checked hardware-control
requirements; derive width/lane/upper-lane effects, alignment faults, and
per-access footprint/tearing; refuse or scalar-fallback the optional AVX2
tier; export an adapter for lane 660 / validator consumers.

## What was done

NEW file `grammatik/Grammatik/X86/VectorHardwareProfile.lean` (761 lines),
plus one additive import line in `grammatik/Grammatik.lean`. No other file
touched (`git status`: only these two). No redefinition of any accepted
evaluator; everything reuses `FeatureProfile`, `VectorCodec`,
`VectorFootprints`, `Vektor`, `ScalarFloat`, `ExtendedExecution`.

1. **Enabled-state (§1):** `CpuMerkmal` (SSE2/AVX presence), `Xcr0Bild`
   (x87/SSE/AVX bits), `KontrollBild` (CR0.EM/TS, CR4.OSFXSR/OSXSAVE);
   `xcr0SseBereit`, `kontrollSseFrei`, `hwVektorBereit` (silicon + XCR0 +
   controls + OS bit; integer SSE needs no MXCSR, stated), tier admission
   `vektorHwZugelassen` (finite `paketInt128` admission AND hardware
   readiness), four projection theorems, and the safe refinement
   `vektorHw_verfeinert` (checked gate implies the old `vecEintritt`).
2. **Gated byte-execution (§2):** `stepVectorHw` (accepted `stepVector`
   under the gate, `none` otherwise); refusal theorems for missing
   CPU/XCR0/controls; width fact `vektorBreite_spur` (two `.b64` lanes;
   profile label `.b32` stated alongside, NOT redefined); low-lane PXOR,
   high-lane PXOR/PADDQ lane theorems; rFLAGS preservation.
3. **Memory forms (§3):** `VektorSpeicherForm` (aligned/unaligned);
   `vektorGpFehler` (#GP exactly on 16-byte misalignment for the aligned
   form, never for unaligned); `vektorSchreibZugelassen` (no #GP + both
   chunk permissions); footprint `vektorHw_fuss` (16-byte `vecFuss`);
   `vektorHw_teilt` (torn intermediate state — no atomicity claimed).
4. **AVX2 + fallback (§4):** `VektorStufe`; `xcr0AvxBereit`,
   `stufenCpuBereit`; `stufenZugelassenHw` (128-bit row IS the gate,
   256-bit row always `false`); `avx_braucht_xcr0`; scalar fallbacks
   `skalarPaarXor`/`skalarPaarAdd` over canonical `xorB`/`addB` with
   half lemmas, four lane bridge lemmas, and `skalarPaarXor_gleich`
   (fallback reads back exactly the packed `vecXor` word lane by lane).
5. **Adapter + witnesses (§5):** `vektorValidatorZugelassen`
   (`extZugelassen` AND hardware gate) with both projection theorems;
   `stepExt_vec_hw`; `vectorHw_fetch_bridge` (fetched form through the
   unified `extByteschritt` + gated-step identity); baseline
   `basisCpu`/`basisXcr0`/`basisKontrolle` with `basis_hw_bereit` and
   `basis_vektorHw_zugelassen`; joint `vectorHw_zeuge` (pinned bytes
   decode, gate admits, gated step + unified dispatch reach the same
   successor, MOVSD store changes a memory byte); seven negatives
   (missing CPU/XCR0/controls/OS-bit, misalignment, alias overlap,
   unknown opcode).

## Checks

- `./lean-probe grammatik/Grammatik/X86/VectorHardwareProfile.lean`:
  `== 0 error(s)`, no warnings.
- `./lean-bau`: `Build completed successfully (460 jobs)`.
- `#print axioms`: every theorem depends only on subsets of
  `[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel` set);
  most on `[propext]` or nothing. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`.
- `gabbro_ziel` statement/proof untouched (only a leaf import added),
  so its axiom set cannot have moved.

## What remains open (also in file CUTS)

- Manual provenance: `.tmp/HARDWARE-REFERENCES/REFERENCES.json` is
  absent in this clone (checked 2026-10-02), so no manual heading/page
  is cited; bit positions are explicit checked inputs, silicon
  correspondence stays OPEN.
- Only PXOR/PADDQ register forms; no vector memory opcode, packed-FP
  lane, VEX/AVX encoding, or other SSE2 row. Profile `.b32` label vs
  `.b64` lane reconciliation stays with the profile owner.
- Execute permission is an adapter conjunct, not a constructed loaded
  image. TSO/GX refinement, source correspondence, budget transfer,
  progress, call-log effects open; `simdFreigabe` untouched (`false`).

## Findings / deviations

None blocking. One design note: the tier's profile width label
(`.b32`) differs from the admitted lane width (`.b64`); both facts are
stated side by side in `vektorBreite_spur` rather than silently
redefining either — reconciliation is flagged for the profile owner.
