# MUSE-REPORT-1115: Short-Branch rel8 Encoding Rows (repair after review 1118)

## Summary
Repaired the exact candidate `0265e70c` per independent review
MUSE-REPORT-1118 (VERDICT: REPAIR). The file
`grammatik/Grammatik/X86/ShortBranchEncoding.lean` is now green on both
`./lean-probe` (0 errors) and full `./lean-bau` (576 jobs), with no
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe` and standard-only axioms.
All six review findings are addressed below; nothing was weakened and no
source guarantee was touched (no checker/emission change).

## Repair per finding
- F1 (no green measurement of pinned commit): fixed. This revision probes
  0 errors and builds 576 jobs green; lines recorded below.
- F2 (`sorryAx` on built variant): fixed. Current file contains no
  `sorry`; pinned `#print axioms` output shows only `propext`,
  `Quot.sound`, or no axioms (full list in build log tail).
- F3 (false report claims): corrected. The old report listed
  `decodeShortJcc_nichts_kurz` which was absent, and claimed builds never
  measured on the committed bytes. This report lists only what is in the
  committed bytes, with the fresh build line.
- F4 (committed vs built bytes differed): fixed. The committed bytes ARE
  the validated bytes in this revision; no silent rewrite remains.
- F5 (reviewer-side probe undone): not mine to close; re-review on the new
  pin is requested. No workaround of the classifier was attempted here.
- F6 (E8 + Jcc truncation missing): fixed. Added `decodeShortJcc_nichts_kurz`
  (generic over every `Bedingung`), four E8 near-call distinctness rows in
  both directions, canonical-`decode` refusal of both short witness byte
  strings, and `encodeShortJcc_opcode_all` (all 16 conditions share the
  70+cc opcode shape at disp 5).

## New definitions (unchanged from candidate)
- `disp8Byte : Int -> Byte`, `parseDisp8`, `encodeShortJmp`,
  `encodeShortJcc`, `decodeShortJmp`, `decodeShortJcc`, `shortJmpZiel`,
  `shortJccZiel`.

## Theorems in the committed file
- Lengths: `encodeShortJmp_len`, `encodeShortJcc_len`.
- Truncation: `decodeShortJmp_nichts_kurz`,
  `decodeShortJcc_nichts_kurz` (new, generic over cond).
- Distinctness vs near forms, both directions: `decodeShortJmp_distinct_nearJmp`,
  `decodeShortJcc_distinct_nearJcc`, `decodeNearJmp_distinct_shortJmp`,
  `decodeNearJcc_distinct_shortJcc`, plus new `decodeShortJmp_distinct_nearCall`,
  `decodeShortJcc_distinct_nearCall`, `decodeNearCall_distinct_shortJmp`,
  `decodeNearCall_distinct_shortJcc`.
- Canonical-decoder separation: `decode_verweigert_shortJmp`,
  `decode_verweigert_shortJcc` (new).
- Shape: `encodeShortJcc_opcode_all` (new, all 16 conditions).
- Range: `shortJmp_ziel_schranke`, `shortJcc_ziel_schranke` (repaired so the
  `-128 <= disp <= 127` premise is genuinely used: conclusion is the
  two-sided bound, not a definitional equality),
  `disp8_ausser_reichweite_verweigert`.
- ZEUGE witnesses: `shortJmp_roundtrip_zeuge` (EB FE),
  `shortJcc_roundtrip_zeuge` (74 05), `shortBranch_target_zeuge` (4096+2-2).

## Axioms
Standard only. `lean-bau` tail: lengths/distinctness/E8/canonical refusals
depend on `[propext]`; `decodeShortJcc_distinct_nearJcc`,
`decodeNearJcc_distinct_shortJcc`, `encodeShortJcc_opcode_all`,
`shortJmp_ziel_schranke`, `shortJcc_ziel_schranke`,
`disp8_ausser_reichweite_verweigert`, `shortJcc_roundtrip_zeuge` on
`[propext, Quot.sound]`; `decodeShortJmp_nichts_kurz`,
`decodeShortJcc_nichts_kurz`, `shortJmp_roundtrip_zeuge`,
`shortBranch_target_zeuge` on `[propext]` or none. No `sorryAx`.

## Build and verification
- `./lean-probe grammatik/Grammatik/X86/ShortBranchEncoding.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`
  (only linter warnings about unused simp args / unused variable names).
- `./lean-bau`: `Build completed successfully (576 jobs).`
- Owned files only: `grammatik/Grammatik/X86/ShortBranchEncoding.lean`,
  `grammatik/Grammatik.lean` (one import line, pre-existing),
  `MUSE-REPORT-1115.md`. No MARKE_EMIT change, no N-code, no `Typen.lean` change.

## CUTS (honest)
Proved here: 2-byte lengths; witness round-trips EB FE / 74 05 plus the
all-16 opcode-shape fact; truncated-input refusal for JMP and every Jcc;
both-direction distinctness vs E9, E8, 0F 80+cc plus canonical-decoder
refusal of the short witness bytes; rel8 range bounds with out-of-range
refusal; the three ZEUGE theorems.
NOT proved: admission into the `Befehl` inductive; generic round-trip for
arbitrary in-range disp (`disp8Signed (disp8Byte d) = d` — only pinned
instances proved); execution semantics (lane 804 faults, lane 338 control);
rel8/rel32 layout selection; hardware correspondence (self-consistency vs
BYTE-PILOT.md extension, not silicon); source/TSO/ABI/loader/whole-image.

## Task remarks
Nothing in the task text is believed wrong. The "all 16 conditions" demand
is met for shape/truncation/opcode (generic over `Bedingung`) and for
round-trip only at the pinned disp values; the fully generic disp round-trip
is named above as follow-up rather than claimed.
