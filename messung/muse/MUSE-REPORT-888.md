# MUSE-REPORT-888: Optimiser rule: multiply selection rule

## Task

Lane 888: state the DESIGN section 3A tile (3-operand `IMUL r, r/m,
imm8/imm32` for constant multiplies with a proved range; strength
reduction cites the section 3 row, never a bare pattern) as a generic
rule lemma over arbitrary values with validator-decided side
conditions (DESIGN section 7 strength-reduction row), proving
value/fault/observation preservation including IEEE, contracts, call
logs, concurrency and budget; name the exact certificate shape and the
precise refusal case. Target: `OptMulSel_verbindung` with companion
`OptMulSel_verbindung_zeuge` (jointly inhabited, non-degenerate,
memory-changing reached run).

Owned files only: `grammatik/Grammatik/X86/OptMulSel.lean`,
`grammatik/Grammatik.lean` (one import line appended),
`MUSE-REPORT-888.md`.

## What was done

New file `grammatik/Grammatik/X86/OptMulSel.lean` (about 460 lines),
reusing the canonical vocabulary only (`Typen`, `Syntax`, `Semantik`,
`ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.Ganzzahl`,
`X86.StaerkeReduktion`, `X86.MulDiv`). The single accepted IR is not
available, so the connection is stated over the real
`Syntax`/`Semantik` `execEnd` fragment it covers, as the task allows.

Exact new definitions/theorems:

- Section 1 (refusal): `MulSelCert` (`breiteOk`, `immPasst`,
  `flagsOk`, `keinGleit`), `mulSelZulassen`,
  `mulSelVerweigert_bereich`, `mulSelVerweigert_imm`,
  `mulSelVerweigert_flags`, `mulSelVerweigert_gleit`,
  `probe_mulSelZulassen_ok`, `probe_mulSelZulassen_bereich`,
  `probe_mulSelZulassen_imm`, `probe_mulSelZulassen_gleit`.
- Section 2 (target form + overflow row): `Imul3`, `imul3Wert`,
  `imul3Wert_b64`, `imul3Flags_gueltig` (cites accepted
  `mulFlagsS_gueltig`), `imul3Traegerfrei` (cites the `mulTragU`
  row), `probe_imul3Wert`, `probe_imul3Traeger`,
  `probe_mulTragVorzeichen` (`-1 * -1 = +1` at 8 bits: unsigned
  carry set, signed carry clear -- the reason CF and OF need
  distinct rows).
- Section 3 (value/word/shift): `mulKonst_wert`, `mulWort_liest`,
  `mulShift_stimmt` (cites accepted `shlW_keinUeberlauf`),
  `probe_mulKonst`, `probe_mulWort`, `probe_mulShift`.
- Section 4 (proved range): `imin_selbst`, `imax_selbst`,
  `vierEcken_unten`, `vierEcken_oben`, `vierEcken_weiter_unten`,
  `vierEcken_weiter_oben` (the four-corner `imin`/`imax` range
  collapses on literal operands -- the validator's range proof,
  never a range hope).
- Section 5 (connection): `OptMulSel_verbindung` -- eval value
  preserved (`x * k`), `execEnd` outcome equal at an arbitrary
  `Endblock.bind` continuation (same block shape, `orte = []`: no
  fault added or removed, contracts read the same values, no call-log
  event, no shared access, unchanged step-budget accounting), and the
  proved-range product reads back whole through the canonical word.
  The source multiply is widened to the continuation type by
  `weiter` with the section 4 evidence. IEEE by refusal
  (`keinGleit`). Nothing derives `ensures`; no refusal becomes a
  warning; no faulting form is speculated above its guard (only total
  `mul` is selected -- `div`/`sdiv`/`srem` nowhere).
- Section 6 (joint witness): `OptMulSel_verbindung_zeuge` -- ALL
  premises of `OptMulSel_verbindung` instantiated jointly (`6 * 7`
  selects to `42` under `bind`/`leave`) on non-degenerate `refD`
  (`refEin_schreibt`) beside the reached memory-changing F-machine
  run `MB` (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`).
- Section 7 (selector + certificate): `waehleImul3`,
  `waehleShift`, `waehleImul3_zugelassen`,
  `waehleImul3_verweigert`, `waehleShift_verweigert_live` (the CE-6
  refusal: `imul r,8 -> shl r,3` with live flags keeps IMUL),
  `waehleShift_erlaubt_tot`, `waehleShift_verweigert_zert`,
  `MulSelZert` (local rewrite record `ziel` plus recomputed citation
  `freigabe`), `mulSelZertOk`, `mulSelZertOk_heisst`,
  `mulSelZertOk_verweigert`.

The precise refusal cases where the rule must NOT fire: unproved
range, constant outside imm8/imm32, undischarged flag/fault identity
(in particular shift with live flags), and any float multiply.

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptMulSel.lean`: 0 errors;
  every `#print axioms` is within the standard goal set (subsets of
  `propext`, `Classical.choice`, `Quot.sound`); no `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe`.
- Last `./lean-bau` result line: `Build completed successfully (511
  jobs).`
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes,
  no source/checker/Spec/goal/emitter edits, no friend-reserved
  optimiser files touched.

## What remains open

Per the file's CUTS block: byte encoding/decoding and wiring of
`Imul3` into `Befehl`/`schritt`/decoder/image (Codec lane); the
TSO/GX bridge beyond non-interference (`orte = []` on both sides);
the formal level-(c) machine-work bound; any float selection;
silicon correspondence. The full source-to-final-loaded-byte closing
theorem stays with the validation lanes.

## Task feedback

Nothing in the task is believed wrong. One elaboration note for
reviewers: unlike `add` (exact range), source `mul` carries the
four-corner `imin`/`imax` range, which does not reduce on variable
operands -- so the connection carries the `weiter` widening with the
proved corner-collapse evidence (section 4) rather than a direct
type ascription. This is a faithful modelling of the source typing,
not a weakening: the collapse lemmas are proved, and the `weiter`
is value-transparent (`eval_weiter_n` is `rfl`).
