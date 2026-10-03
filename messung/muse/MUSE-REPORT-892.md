# MUSE-REPORT-892: MOV-immediate selection rule

## What was done

New file `grammatik/Grammatik/X86/OptMovImmSel.lean` (~660 lines) plus the
one import line in `grammatik/Grammatik.lean`. It states the DESIGN
section 2B MOV-immediate rows (imm32 zero-extending / sign-extended vs
imm64) as a layer-A local rewrite in the section 7 register discipline:
a rule lemma over arbitrary values with validator-decided side
conditions.

- Tiles: `MovTile` (`weit`/`kompakt`/`sign`) with `tileWert` reusing the
  pilot word, the accepted `compactWert`, and canonical `sext`.
- Certificate: `MovImmCert` (`oberTot`, recomputed liveness) with gates
  `passtU32`/`passtI32` (exact: `passtU32_genau`, `passtI32_genau`) and
  `nullZulassen`; selector `waehleMovImm` in DESIGN 2B order
  zero/sign/wide; lengths in `tileLaenge` (10 vs 5/6 vs 7).
- Value preservation over arbitrary values: `waehle_wert` via
  `kompaktWert_rundgang` and the `sext` identity `signWert_rundgang`
  (bit bridge `movSelBit_div_pow`/`movSelBit31` restates the accepted
  `RelocatedExecution` pattern under selection-local names; remainder
  fact `movSelMod64_32`).
- Exact firewall where the rule must NOT fire:
  `waehle_kein_kompakt_ohne_tot`, `waehle_kein_kompakt_bei_gross`,
  `waehle_kein_sign_ohne_bereich` (plus `nullVerweigert_oberLebendig`,
  `nullVerweigert_gross`, `passtU32_verweigert_gross`); admitted site
  equation `waehle_null`.
- Execution agreement for the byte-connected pair: `weitSchritt_wert/
  flags/speicher/fremd`, `kompaktSchritt_wert/flags/speicher/fremd`,
  downstream flag agreement `movSelBedingung_gleich` for every
  `Bedingung` (integer and float unordered rows alike).
- Byte grounding through accepted rows only: `movSelBytes_weit`
  (pilot `roundtrip`), `movSelBytes_kompakt` (`roundtripCompact`); pins
  `pin_waehle_fuenf`, `pin_waehle_minus_eins`,
  `pin_waehle_gross_bleibt_weit`, `pin_nullZulassen_oberLebendig`.
- Target theorems: `OptMovImmSel_verbindung` with companion
  `OptMovImmSel_verbindung_zeuge` (jointly instantiated at
  `rax := 0x80000001` over hostile all-ones registers from
  `kompaktWitState`, plus the reached `lauf` run taking cell 8192 from
  0 to 42; non-degenerate: register-changing step plus store-changing
  run).

No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise is
used (unused-`c` premises were removed, not silenced); no new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved files
touched.

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptMovImmSel.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (511 jobs).`
- `#print axioms` for every main theorem: standard only (`propext`,
  `Classical.choice`, `Quot.sound`; several pins depend on no axioms).
- `gabbro_ziel` re-checked: depends on axioms
  `[propext, Classical.choice, Quot.sound]` (unchanged).

## What remains open (see CUTS in the file)

- Sign-row codec/fetch/byte-step belong to lane 747; this file defines
  no C7/0 bytes, decoder or step and duplicates none of its names. Until
  747 lands, a validator must refuse to EMIT the sign tile and keep the
  certified wide fallback.
- Source-side range evidence is consumed, never re-derived;
  `TableLayout`/`CostSummary` stay consumers (read, not imported).
- TSO/W/GX per-access bridge, `FpZustand`/`stepExt` lift, and layer-C
  ghost-event transfer stay with their owner lanes.
- No hardware correspondence is claimed (round-trip consistency is not
  silicon proof).

## Note on the task text

The task asks for premises "from the DESIGN section 7 row", but the
section 7 inventory table has no MOV-immediate row; the applicable rows
are DESIGN section 2B (zero/sign selection rules and obligations), used
here, with section 7 supplying only the certificate discipline
(layer-A lemma + re-decided side conditions). Nothing else in the task
looks wrong.
