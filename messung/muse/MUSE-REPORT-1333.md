# MUSE-REPORT-1333: Opcode ledger one-byte 00-3F

## What was done

New file `grammatik/Grammatik/X86/OpcodeLedger1Byte00.lean`
(namespace `Gabbro.Grammatik.X86.Ledger00`), plus one import line in
`grammatik/Grammatik.lean`. Self-contained schema, no dependency on
other ledger lanes.

- `inductive LStatus`: modelliert, zurueckgestellt, verweigert,
  ungueltig64, fehlt.
- `structure LEintrag`: opcode (Nat), mnemonik, status, familie
  (module/decoder string), grund (one-line reason).
- `ledger00`: all 64 opcode bytes 0x00-0x3F, each exactly once.
- Counts (all `by decide`): modelliert 21, zurueckgestellt 5,
  verweigert 0, ungueltig64 11, fehlt 27.
- `abdeckung` (`by decide`): every n in 0..63 occurs exactly once.
- Checked pins, all `by decide`:
  - 6 chain pins with exact RHS: `kap_add_akzeptiert` (01, .breit/.ext/.pilot),
    `kap_sub_akzeptiert` (29), `kap_xor_akzeptiert` (31),
    `kap_cmp_akzeptiert` (39), `kap_or_akzeptiert` (09, .kern),
    `kap_and_akzeptiert` (21, .kern).
  - 15 family pins (`isSome`): `carry_10`..`carry_15`,
    `carry_18`..`carry_1d` via `decodeCarry`; `rax_05`, `rax_2d`,
    `rax_3d` via `decodeRax`.
  - 11 `ungueltig64` refusals (`ung_06`..`ung_3f`): `kapDecode [b] = none`.
  - 5 deferred-prefix refusals (`zur_0f`, `zur_26`, `zur_2e`, `zur_36`, `zur_3e`).
  - 27 gap refusals (`fehlt_00`..`fehlt_3c`): full canonical forms
    refused by `kapDecode`.
- Measurement first: a scratch probe (`#eval kapDecode` etc.) fixed
  every expected value before it was stated; no value was guessed.

## Last build results

- `./lean-probe grammatik/Grammatik/X86/OpcodeLedger1Byte00.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (694 jobs)`.
- Axioms: counts `[propext]`, coverage none, kap pins
  `[propext, Quot.sound]` (standard subset, no new axioms).

## Findings (`fehlt` entries, the product)

1. Load-direction ALU (0x03, 0x0B, 0x23, 0x2B, 0x33, 0x3B) is
   unmodelled in every width. 0x33 (XOR r32, the 32-bit zero idiom)
   and 0x3B (CMP r32) are among the most common instructions in
   compiler output.
2. Asymmetric rAX immediates: ADD/SUB/CMP (0x05, 0x2D, 0x3D) have
   `decodeRax` rows (REX.W only), but OR/AND/XOR (0x0D, 0x25, 0x35)
   have none.
3. All 8-bit ALU forms except ADC/SBB, and all AL-imm8 forms except
   ADC/SBB, are unmodelled.
4. Bare 32-bit forms of the modelliert REX opcodes (01, 05, 29, 2D,
   31, 39, 3D) are refused; only the REX(W) forms decode.
5. `verweigert` is honestly 0: nothing valid in 00-3F is deliberately
   refused.

## What remains open

- Other opcode regions belong to other ledger lanes; 0F escape and
  segment prefixes are marked zurueckgestellt for them.
- `fehlt` refusals are proved against the `kapDecode` chain only;
  out-of-chain family decoders were checked by reading dispatch
  tables, not by sweep (recorded in CUTS).
- Opcode map is a NAMED assumption (Intel SDM edition 093 from the
  supplied extracts); no AMD manual in this clone, no
  vendor-difference claim.

## Task feedback

The CONTEXT/MECHANISM paragraphs (HwAdapter embedding, multi-step
witness, two cores) do not match this lane's actual deliverable
(opcode ledger with decide pins); the operative spec is the TASK
paragraph, which this lane implements completely. No premise was
added, no conclusion weakened. Rule 13 needs no `_zeuge`: no theorem
quantifies over program syntax.
