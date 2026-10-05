# MUSE-REPORT-1347: Opcode ledger 0F C0-FF plus 0F 38 / 0F 3A

## What was done

NEW FILE `grammatik/Grammatik/X86/OpcodeLedger0FC0.lean` (own namespace
`Gabbro.Grammatik.X86.Ledger0FC0`, self-contained schema, no other ledger
lane depended on) plus one import line appended to `grammatik/Grammatik.lean`.

- 139 rows covering every second byte C0-FF (op 192-255) with legal
  prefix/ModRM.reg splits, plus the 0F 38 / 0F 3A escapes as group rows
  (op 56/58). Status counts, all `decide`-proved:
  modelliert 4, verweigert 8, zurueckgestellt 2, ungueltig64 0, fehlt 125.
- Opcode map provenance actually used (not assumed): Intel SDM combined
  Vols 1-4 edition 325462-093US (Sep 2026), local snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
  (matches `REFERENCES.json` sha), Appendix A Tables A-3/A-4 and the
  Group 9 table. No AMD manual in the clone: no AMD provenance claimed,
  vendor differences stay FREE (rule 17).
- Checked part: the 4 modelliert rows decode (2 at `kapDecode` level by
  reusing accepted `kapKette_lock` / lifting accepted `pin_ext_vec_pxor`
  through `decodeMulDivWidth_prefers_ext`+`kapDecode_breit`; 2 at the named
  family-decoder level by reusing accepted `pin_lock_reg_ud_decodiert` /
  instantiating accepted `roundtrip_paddq`). The 8 verweigert rows refuse:
  8 × `kapDecode <closed bytes> = none`, each `by decide`, directions
  verified beforehand by reading every one of the 8 chain decoders' match
  arms (Codec, NarrowCodec, MulDivCodec, ShiftCodec, ControlCodec setcc/cmov,
  ScalarFloatCodec fp, VectorCodec, MulDivWidthHardwareForms prefix layer,
  s32, mxcsr, LOCK, LOCK-addr, CompactForms, IntegerCore, Avx2Join).

## Exact new names

Types: `LStatus`, `LEintrag`. Data: `ledgerTeilC/D/E/F`, `ledger0FC0`,
`ledgerSchluessel`, `istModelliert`, `istZurueckgestellt`, `istVerweigert`,
`istUngueltig64`, `istFehlt`. Coverage/counts: `ledger_nodup`,
`ledger_c0ff_vollstaendig`, `ledger_escapes_vorhanden`,
`ledger_anz_modelliert`, `ledger_anz_verweigert`,
`ledger_anz_zurueckgestellt`, `ledger_anz_ungueltig64`, `ledger_anz_fehlt`.
Modelliert: `ledger0FC1_kette`, `ledger0FC1_regUd`, `ledger0FD4_vec`,
`ledger0FEF_kette`. Verweigert: `ledger_weist_c7r0_zurueck`,
`ledger_weist_c7r2_zurueck`, `ledger_weist_d0_zurueck`,
`ledger_weist_d6_zurueck`, `ledger_weist_e6_zurueck`,
`ledger_weist_f0_zurueck`, `ledger_weist_ff_zurueck`,
`ledger_weist_c1ohneRex_zurueck`.

Last `./lean-bau` result line: `Build completed successfully (694 jobs).`
`./lean-probe` on the new file: 0 errors. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` in the file; `#print axioms` is `propext` alone
for data theorems and `propext + Quot.sound` where the decoder chain
evaluates (same footprint class as the accepted `kapW_*` theorems).

## Findings (the `fehlt` product, by compiler-output frequency)

1. Whole SSE2 integer ALU: PSUBB/W/D, PADDB/W/D (F8-FC/FD/FE, plain+66) —
   very common in vectorized loops; nothing models them.
2. BSWAP C8-CF (all 8 registers): byte-order/network code. `ByteSwap.lean`
   has only value helpers (`bswap32`/`bswap64`), no decoder covers it.
3. CMPcc C2 (all 4 prefix forms; CMPSS most common): scalar FP compare is
   everywhere; the s32 family lacks it.
4. PMOVMSKB D7, SHUFPS/SHUFPD C6: string/table and FP-shuffle code.
5. POR/PAND (EB/DB): of the logic group only PXOR/PADDQ (66 rows) exist.
6. Atomics gap: plain XADD (C0/C1), 8-bit LOCK XADD (C0), CMPXCHG8B/16B
   (C7/1) — `decodeLock` covers only LOCK+REX.W C1 / 0F B1 / 0F AE.
7. MOVQ/D6-66, PINSRW/PEXTRW, converts E6, MOVNTI/MOVNTQ, LDDQU, MASKMOVQ,
   ADDSUBPD/PS, PSADBW, PMADDWD, shifts D1-D3/F1-F3, and the full
   0F 38/0F 3A three-byte space (SSSE3/SSE4/AES incl. MOVBE).
8. Deferred (`zurueckgestellt`): RDRAND/RDSEED need a scope decision —
   probabilistic silicon, Spec NOT CLAIMED.
9. Corrections to common priors, verified in the snapshot: MOVBE is
   `0F 38 F0/F1`, NOT `0F F0/F1`; `0F FF` is UD0 (UD2 is `0F 0B`); bare
   D0/D6/E6/F0 are map blanks (reserved, correctly refused).

## Open / not claimed

- The 125 `fehlt` rows are findings for future family lanes, not proved here.
- `ungueltig64` is empty by measurement (no C0-FF byte is categorically
  64-bit-invalid; invalidity lives at prefix/ModRM level, captured by the
  8 `verweigert` rows).
- Map transcription is a NAMED assumption (CUTS); VEX/EVEX and
  supervisor/system forms are named, never modeled.
- No `_zeuge` owed: no premise quantifies over program syntax, no ZEUGE
  target in the task.
- Two shell calls were transiently refused mid-lane by the permission
  layer, then allowed again; no files outside the clone were touched.

## What I believe is wrong in the task

The CONTEXT/MECHANISM paragraphs (HwAdapter/`HwSchritt` embedding,
two-core memory-changing witness) describe a hardware-connection lane and
contradict the actual TASK (a stattics-only opcode ledger in one new file).
The owned filename, region and "ONE new file" instruction all agree with
the ledger task, so I implemented the ledger and ignored the adapter
mechanism. The two refused-then-allowed shell calls suggest the
environment, not the task, as the cause of the earlier stall.
