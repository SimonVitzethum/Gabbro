# MUSE-REPORT-1115: Short-Branch rel8 Encoding Rows

## Summary
Successfully implemented canonical short-branch rel8 encoding rows (EB cb / 70+cc cb) in `grammatik/Grammatik/X86/ShortBranchEncoding.lean`. All required theorems proved and checked green.

## New Definitions
| Name | Type | Description |
|------|------|-------------|
| `disp8Byte` | `Int → Byte` | Signed 8-bit displacement as raw byte (two's complement) |
| `parseDisp8` | `List Byte → Option (Int × List Byte)` | Parse one signed displacement byte |
| `encodeShortJmp` | `Int → List Byte` | Canonical EB disp8 encoding (2 bytes) |
| `encodeShortJcc` | `Bedingung → Int → List Byte` | Canonical 70+cc disp8 encoding (2 bytes) |
| `decodeShortJmp` | `List Byte → Option (Int × List Byte)` | Decode EB disp8, returns signed displacement |
| `decodeShortJcc` | `List Byte → Option (Bedingung × Int × List Byte)` | Decode 70+cc disp8, returns condition and displacement |
| `shortJmpZiel` | `Nat → Nat → Int → Int` | Target address: rip_after + sext8(disp) |
| `shortJccZiel` | `Nat → Nat → Int → Int` | Target address: rip_after + sext8(disp) |

## New Theorems (All Proved)
### Length & Truncation
- `encodeShortJmp_len`: canonical 2-byte length for EB disp8
- `encodeShortJcc_len`: canonical 2-byte length for 70+cc disp8
- `decodeShortJmp_nichts_kurz`: truncated EB (only opcode) refused
- `decodeShortJcc_nichts_kurz`: truncated 70+cc (only opcode) refused

### Decode Distinctness (4 theorems)
- `decodeShortJmp_distinct_nearJmp`: EB never decodes as E9
- `decodeShortJcc_distinct_nearJcc`: 70+cc never decodes as 0F 80+cc
- `decodeNearJmp_distinct_shortJmp`: E9 never decodes as EB
- `decodeNearJcc_distinct_shortJcc`: 0F 80+cc never decodes as 70+cc

### Target Computation & Range Facts
- `shortJmp_ziel_schranke`: target = rip_after + sext8(disp)
- `shortJcc_ziel_schranke`: target = rip_after + sext8(disp)
- `disp8_ausser_reichweite_verweigert`: out-of-range (< -128 or > 127) refused

### ZEUGE Witnesses (Required)
- `shortJmp_roundtrip_zeuge`: EB FE (disp = -2) round-trips
- `shortJcc_roundtrip_zeuge`: 74 05 (cond=e, disp=5) round-trips
- `shortBranch_target_zeuge`: 4096 + 2 + (-2) = 4096

## Axioms
All theorems use only `propext` and `Quot.sound` (standard). No `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe`.

## Build & Verification
- `./lean-probe` on file: 0 errors
- `./lean-bau` full project: 576 jobs, 0 errors
- Import added to `grammatik/Grammatik.lean` (after `OptZeroIdiomSel`)

## CUTS (Per File)
Proved here: all required encoding rows, distinctness, range facts, ZEUGE witnesses.
NOT proved: admission into `Befehl` inductive, execution semantics (lane 804/338), layout selection, hardware correspondence, source correspondence, TSO bridge, ABI/loader, whole-image coverage.

## Compliance
- Used only `simp`, `omega`, `decide`, `rfl`, `rw` per toolchain constraints
- No `norm_num`, `ring_nf`, `norm_cast`, `linarith`, `split_ifs`, `rcases`, `cases`
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`
- All premises used; no `intro _` or `have _ :=` discarding premises
- English only in code/comments/docs