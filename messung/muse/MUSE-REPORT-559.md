# MUSE-REPORT-559: Arbitrary-input pilot decoder soundness

Lane 559, clone `/home/simon/Dokumente/gabbro-muse/a559`, branch `muse/559`.
Owned paths only: `grammatik/Grammatik/X86/DecoderSoundness.lean` (new),
`grammatik/Grammatik.lean` (one additive import line), this report.

## What was done

Created `grammatik/Grammatik/X86/DecoderSoundness.lean` (343 lines): the
Codec CUT for arbitrary successfully decoded bytes is closed from the
decoder side, reusing `Codec.decode` (no second decoder, no new ISA facts)
and deriving everything through the existing proved components:

- `laengeOk_grenzen`: `laengeOk l = true` unfolds to `1 ≤ l ∧ l ≤ 15`.
- `decode_verbraucht_praefix` (generic agreement): for ARBITRARY `bs` with
  `decode bs = some (d, rest)`, `d.laenge + rest.length = bs.length`,
  `rest = bs.drop d.laenge`, `1 ≤ d.laenge ∧ d.laenge ≤ 15`. Combines the
  reused `DecodingCoverage.decode_abdeckung` with
  `decode_fenster_kongruenz`; no encoder round trip is used anywhere.
- `fetch_verbraucht_praefix` (fetched agreement): for
  `fetchDekodiert s = some (d, rest)`, the window equation, the
  drop-suffix, the 1..15 bounds, `d.laenge ≤ (geholt s).length`,
  `(geholt s).length ≤ fetchCap`, and the executable consumed prefix
  `ausfuehrbarN s.speicher s.rip d.laenge = true`. Derived through the
  reused `fetchDekodiert_entspricht` plus the generic agreement plus
  `fetch_nutzt_nur_praefix`; the runtime length check is implied, never
  assumed.
- 20 hand-written non-roundtrip probes, every one literal bytes (never
  `encode` output) with a trailing byte proving suffix passthrough,
  covering every pilot dispatch branch: `sonde_ret_mit_rest`,
  `sonde_call32_mit_rest`, `sonde_jump32_mit_rest`,
  `sonde_jumpIf32_mit_rest`, `sonde_push64_niedrig_mit_rest`,
  `sonde_pop64_niedrig_mit_rest`, `sonde_push64_hoch_mit_rest`,
  `sonde_pop64_hoch_mit_rest`, `sonde_movImm64_rax_mit_rest`,
  `sonde_movImm64_r8_mit_rest`, `sonde_movReg64_mit_rest`,
  `sonde_addReg64_mit_rest`, `sonde_subReg64_mit_rest`,
  `sonde_xorReg64_mit_rest`, `sonde_cmpReg64_mit_rest`,
  `sonde_addReg64_erweitert_mit_rest`, `sonde_load64_ohne_sib_mit_rest`,
  `sonde_store64_ohne_sib_mit_rest`, `sonde_load64_sib_mit_rest`,
  `sonde_store64_sib_mit_rest`.
- 9 truncated/corrupted refusal probes (all `rfl`):
  `decoder_weist_rex73_allein_zurueck`,
  `decoder_weist_imm_abgeschnitten_zurueck`,
  `decoder_weist_sib_versatz_kurz_zurueck`,
  `decoder_weist_sib_falsch_zurueck` (forged SIB 37 at full length),
  `decoder_weist_opcode_falsch_zurueck` (byte 198),
  `decoder_weist_modus_eins_laden_zurueck`,
  `decoder_weist_zweig_pseudo_zurueck` (0F second byte 200),
  `decoder_weist_call_kurz_zurueck`, `decoder_weist_schub_falsch_zurueck`.
- 2 joint witnesses tying the agreement to real memory-changing
  execution (data cell zero to 42, reusing the `DecodingCoverage`
  witness states shapes, proved independently here):
  `decode_verbraucht_praefix_zeuge` (hand-written store bytes plus
  trailing byte, agreement facts, `schritt` moves 42),
  `fetch_verbraucht_praefix_zeuge` (actual fetched bytes, window facts,
  `byteschritt` moves 42).

No `sorry`/`admit`/`axiom`/`native_decide`; every premise is used.
Axioms per in-file `#print axioms`: `[propext, Quot.sound]` for the
agreement theorems and witnesses, `[propext]` for the probes, none for
`laengeOk_grenzen` — all within the standard goal axioms.

## Checks

- `./lean-probe grammatik/Grammatik/X86/DecoderSoundness.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (428 jobs).` Whole
  project green, including the new umbrella import.
- The goal statement (`Zielsatz/Spec.lean`, `Beweis.lean`,
  `BeweisAtomar.lean`) was not touched.

## Producer/consumer interface (stable)

- Producers reused (unchanged): `Codec.decode`/`natByte`,
  `Ausfuehrung.laengeOk`/`schritt`, `Byteschritt.geholt`/
  `fetchDekodiert`/`fetchDekodiert_entspricht`/
  `fetch_nutzt_nur_praefix`/`ausgangByte`/`byteschritt`,
  `DecodingCoverage.decode_abdeckung`/`decode_fenster_kongruenz` and its
  witness states `dcStart`/`dcAbholStart`.
- Consumers: lanes 560 (loaded image to fetch), 561 (relocated bytes to
  re-decoded execution) and 575 (unified extended decoder) can call
  `fetch_verbraucht_praefix` directly — one hypothesis
  (`fetchDekodiert s = some (d, rest)`) yields the window equation,
  bounds, cap fit and executable prefix with no further decoder case
  analysis. `decode_verbraucht_praefix` is the same single entry point
  at pure-decode level.
- Measurable next integration: lane 560's entry-window theorem can
  replace its length-side derivation with `decode_verbraucht_praefix`;
  success criterion is fewer decoder case splits in 560 with identical
  `eintritt_abdeckung` conclusions.

## What remains open (not claimed)

See the file's `CUTS` block: no hardware correspondence, no complete
x86 coverage (only the 14 canonical pilot forms), no source/TSO/
concurrency/cost/ABI/entry/relocation claim, no whole-image validation,
no termination claim.

## Findings and task notes

1. Overlap (not a defect): the core arbitrary-input proof already
   exists as `DecodingCoverage.decode_abdeckung` (lane 435) plus
   `decode_fenster_kongruenz`. This lane therefore delivers the
   task-asked packaging (explicit numeric 1..15 bounds instead of the
   `laengeOk` Bool, the single combined decode/fetch statements), the
   full hand-written branch coverage with trailing bytes, new refusal
   probes, and the joint memory-changing witnesses — not a second proof
   of the same statement. No decoder defect was found; all 20 literal
   byte sequences decoded exactly as computed, and no counterexample
   exists to report.
2. Inhabitation mapping: the theorems quantify over `List Byte` /
   `Zustand`, not over source syntax (`Vertrag`/`Stmt`/…), and the task
   names no `ZEUGE:` targets, so rule 13 triggers no mechanical
   obligation. The two `_zeuge` theorems still jointly instantiate
   every premise with concrete values on non-degenerate runs (real
   reached memory change 0 → 42); the planted refusals are the §5
   probes. There is no source-level table at byte level; the actual
   memory change is its byte-level analogue.
3. Foreign working-tree change (preserved, not merged): on resume, the
   clone held an uncommitted diff to `grammatik/Grammatik/X86/Typen.lean`
   adding four `Befehl` constructors (`callReg64`, `jmpReg64`,
   `callMem64`, `jmpMem64`) that I did not write and that is outside my
   owned paths; it breaks `Codec.encode` exhaustiveness and the whole
   build. I saved it to `.tmp/foreign-typen-diff.patch` (private,
   kept) and reverted the file to HEAD to restore green. If the owner
   of that change (possibly lane 575's extended-decoder work) lands
   it, this module's per-branch coverage must be extended to the new
   constructors — `decktAb`-style classification in `DecodingCoverage`
   will need the same extension first.
