# MUSE-REPORT-887: Optimiser rule — shift selection (imm/CL, per-width masking)

## What was done

New file `grammatik/Grammatik/X86/OptShiftSel.lean` (~370 lines) plus one
import line in `grammatik/Grammatik.lean`. No other file touched: no source,
checker, Spec/goal, emitter, diagnostic/gift/example/CLI numbers, no
MARKE_EMIT changes, no friend-reserved optimiser files.

Rule lemma (DESIGN section 7 row: strength reduction / flags-aware
peepholes, phase L): select shifts by imm/CL under per-width
count-masking semantics, with checked-arithmetic stop points preserved
exactly.

- Admission: `ShiftSelCert` (`breiteOk`, `zaehlerGleich`, `flaggenTot`,
  `keinePruefung`) with `shiftSelZulassen` (Bool AND). Refusals proved of
  the decided Bool: `shiftSelVerweigert_zaehler` (disagreeing masked
  counts), `shiftSelVerweigert_flaggen` (live CF/OF survivor — the
  `imul r,8 -> shl r,3` with live CF shape, DESIGN CE-4),
  `shiftSelVerweigert_breite` (width mismatch),
  `shiftSelVerweigert_pruefung` (widened/hoisted checked stop, incl. any
  IDIV/DIV motion). Probes for the admitted and two refused shapes.
- Generic selection rule over arbitrary words/counts, reusing the
  canonical `schiebeZaehler`/`shlB`/`shrB`/`sarB` (`Ganzzahl.lean`):
  `shiftSel_shl/shr/sar` (masked-count agreement gives equal values),
  pins `probe_shiftSel_65` (imm 65 = 1 at 64 bits), 
  `probe_shiftSel_33_schmal` (imm 33 = 1 at 32 bits), `probe_shiftSel_null`.
- Source shape: `shiftQuelle_shl/shr_wert` (value depends only on the two
  numbers; checked premises `hw1 hw2 h0 h0'` forwarded unchanged) and
  `zahlShl_kongr` (count congruence by cases, never a rewrite into
  dependent range proofs).
- CONNECTION `OptShiftSel_verbindung`: replacing the count spelling under
  an `Endblock.bind` with arbitrary continuation preserves the bound value
  AND the full `execEnd` outcome (same constructor/worlds/envs: stop
  classes `logik`/`hardware` agree, contracts at their place, call logs,
  footprints via `hOrte`, int-only bound so IEEE untouched, same block
  shape so budget accounting unchanged). Premises: admitted cert (`hz`),
  conditional count-equality obligation (`hEq`, discharged by `hz` — the
  recomputed-analysis citation), same read footprint (`hOrte`). Every
  premise is used; nothing derives `ensures`, no refusal becomes a
  warning, no faulting form is speculated above its guard.
- JOINT WITNESS `OptShiftSel_verbindung_zeuge`: `3 << (1+1)` selects
  `3 << 2` on the non-degenerate `refD` (writes via `refEin_schreibt`)
  beside the reached run `MB` (`refB_erreicht`, `refB_schreibt` slot
  0 -> 100). Certificate shape named in the file: `ShiftSelCert` record
  (layer A) plus the recomputed `hEq`/`hOrte` obligations per site.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs)`. `./lean-probe` on the new file:
0 errors, 0 warnings. Axioms: admission none; refusals `[propext]`;
masking/source/congruence `[propext, Quot.sound]`; connection and witness
`[propext, Classical.choice, Quot.sound]` — within the `gabbro_ziel`
standard set. Goal files untouched, so `gabbro_ziel` axioms are unaffected
(full build includes `Beweis.lean`).

## What remains open (see CUTS in the file)

No byte codec/decoder claim (ShiftCodec owns bytes); no lowering-side
flag-identity proof (`flaggenTot` is admission citing reused
`SchiebeGueltig`); no layer-B/C block-map/duty binding (`hEq`/`hOrte`
name the per-site obligations); only `shl` gets the `Endblock`
connection (`shr`/`sar` values select); no level-(c) machine-work bound
(OPEN per IR-VALIDIERUNG lane 278); no TSO/GX bridge beyond footprint
equality; no silicon correspondence.

## Task feedback

Nothing in the task appears wrong. One note: the task asks for
"IEEE, contracts, call logs, concurrency and budget" preservation in one
rule lemma — this is carried jointly by the outcome equality (same
successor worlds/envs, same shape, int-only bound) rather than five
separate transfers; the file documents exactly which leg each conjunct
covers. The `_hz/_hEq/_hOrte` witness binders follow the `_hW`
precedent of lane 860 (values still provided jointly in the tuple).
