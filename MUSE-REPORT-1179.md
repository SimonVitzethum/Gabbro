# MUSE-REPORT-1179: Loaded-image fetch obstructions for all extension families

## Task

Follow-up of lane 1137 (`HwLoadedImage.lean`, merged): only the narrow row
was pinned as `fetchDekodiert`-refused while the Hw machine steps it
(`hwBild_erweitert_ohne_pilot`). State and prove the same for muldiv,
shift, setcc, cmov, fp and vec, then a GENERIC theorem over `ExtInstr`
(every non-pilot family) instead of six copies, and the fetch-agreement
for each family on a checked mapping.

## What was done

NEW FILE `grammatik/Grammatik/X86/HwBildFamilien.lean` (+1 import line in
`grammatik/Grammatik.lean`). No existing file was otherwise touched; every
accepted definition is reused unchanged (no second decoder, evaluator,
loader or ISA model).

Definitions/theorems (all in `Gabbro.Grammatik.X86`):

- `istErweitert` (def) + `istErweitert_nicht_pilot`: extension-row predicate.
- GENERIC dispatch inversion `decodeExt_nicht_pilot_zeigt_decode_none`:
  any unified non-pilot `decodeExt` outcome implies `decode = none`
  (first dispatch arm decides on `decode` alone).
- GENERIC obstruction `hwBildFamilien_erweitert_ohne_pilot`: a fetched
  extension row refuses `fetchDekodiert` while the Hw machine steps it.
  Subsumes the narrow-only `hwBild_erweitert_ohne_pilot`; no per-family
  proof is copied.
- Six one-line obstruction corollaries: `hwBildFamilien_muldiv_ohne_pilot`,
  `_shift_`, `_setcc_`, `_cmov_`, `_fp_`, `_vec_ohne_pilot`.
- Six fetch liftings on the core projection (mirror of
  `hwBild_fetchExt_pilot` with the exact fallback chain per family):
  `hwBildFamilien_fetch_muldiv/_shift/_setcc/_cmov/_fp/_vec`.
- Six loaded-image fetch agreements: `hwBildFamilien_muldiv_bild`,
  `_shift_bild`, `_setcc_bild`, `_cmov_bild`, `_fp_bild`, `_vec_bild`.
  Image-window decoder premises are moved to the core window via the
  reused `hwBild_geholt_gleich`; byte provenance from the checked map is
  inherited from `hwBild_geholt_aus_datei` (cited, not repeated).
- `hwBildFamilien_schritt_wf` (lifts `hwSchritt_wf`, as in lane 1137).
- Joint witness `hwBildFamilien_zeuge`: all six extension rows decode
  through `decodeExt` exactly once (the accepted `pin_ext_*` pins) with
  all six pilot refusals beside them (`pin_pilot_weist_*_zurueck`).
  The reached two-core memory-changing run (forwarding, drain 0 to 42)
  is inherited from `hwBild_zeuge`, cited not duplicated.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwBildFamilien.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s)`; `Build completed
  successfully (618 jobs)`.
- `#print axioms`: `[propext]` for every theorem except
  `hwBildFamilien_schritt_wf` (`[propext, Quot.sound]`, via the reused
  `hwSchritt_wf`); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- No premise has type `Prop` itself; every premise is used by its proof.

## What remains open / what I believe is worth noting

- Per-family REACHED fetch instances with a memory-changing step are not
  established here beyond narrow (lane 1137): the obstruction theorems are
  universal implications whose decode-level premises are jointly witnessed
  on real byte rows, while the two-core TSO run is inherited. A reviewer
  wanting per-family `fetchExt`-success instances on concrete `FpZustand`
  values (e.g. over `hwBildStart`-style images containing one family row
  each) should file that as follow-up work; it needs six small images.
- No hardware correspondence is claimed (accepted canonical subsets,
  self-consistency only); no per-access W/GX bridge; no LOCK RMW path.
  See the CUTS block at the end of the file.
- Nothing in the task description looked wrong; the generic-first shape
  made the six copies one-liners as requested.
