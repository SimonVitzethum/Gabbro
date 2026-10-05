# MUSE-REPORT-1345: Opcode ledger 0F 80-BF (repaired per review 1346)

## What was done

NEW FILE `grammatik/Grammatik/X86/OpcodeLedger0F80.lean` (own namespace
`Gabbro.Grammatik.X86.OpcodeLedger0F80`, self-contained schema, no other
ledger dependency) plus one import line in `grammatik/Grammatik.lean`.

- Schema: `inductive LStatus | modelliert | zurueckgestellt | verweigert
  | ungueltig64 | fehlt`, `structure LEintrag` (legacy prefix as
  `Option Nat` defaulting to none, second opcode byte, mnemonic, status,
  modelling family module as string, one-line reason for every
  non-`modelliert` entry), key `schluessel` (prefix, byte) via
  `praefixNr`.
- `ledger`: 67 rows — one per second-opcode byte 128-191 (0F 80-BF) plus
  the three F3-prefixed rows (POPCNT, TZCNT, LZCNT). Opcode map Intel
  SDM Vol 2 Appendix A, Table A-3 (named assumption; local snapshot
  `.tmp/HARDWARE-REFERENCES/`, edition 325462-093US; no AMD manual
  snapshotted, no AMD provenance claimed).
- Counts: 43 modelliert / 3 zurueckgestellt (group 15 + TZCNT + LZCNT) /
  5 verweigert (0F A6, A7, AA, B8, B9) / 0 ungueltig64 / 16 fehlt. Key
  coverage exactly the region bytes at prefix 0 plus the three prefixed
  keys, no duplicate key (`ledger_opcodes`, `ledger_nodup`).
- Checked decodes (reused accepted decoders, never redefined): all 16
  near-Jcc rows via pilot `decode` (`jcc_alle_modelliert`, generic);
  all 16 SETcc rows in register-direct form (`setcc_alle_modelliert`,
  generic); BT/BTS/BTR/BTC register rows (generic `roundtripBtReg`
  reuse for BTS/BTR: `bts_reg_alle`, `btr_reg_alle`; pins for BTC),
  imm8, memory and memory-imm8 rows (`decodeBt`); BSF pin + generic and
  all BSR register rows (`decodeBs`); POPCNT F3 0F B8 pin
  (`popcnt_modelliert`); CPUID (`decodeCpuFeature`); IMUL via the
  capstone chain itself (`imul_modelliert`, reuses accepted
  `kapUeber_wd_ext_imul2`); LOCK CMPXCHG (`decodeLock`).
- Checked deferrals: TZCNT/LZCNT shapes refused by the family decoder
  (`tzcnt_zurueckgestellt`, `lzcnt_zurueckgestellt`, planted refusals
  reused).
- Group/extension mapping for the collapsed rows: Group 8 0F BA every
  /4../7 op in imm8 form (`gruppe8_alle`); Group 15 0F AE the MFENCE /6
  extension (`gruppe15_mfence`); Group 10 0F B9 the single reserved
  extension refused (`verw_b9`). Byte 184 carries the F3 exception in
  its reason (bare form refused, F3 form modelled).
- Checked refusals: all 5 verweigert rows prove `kapDecode ... = none`
  (`verw_a6`, `verw_a7`, `verw_aa`, `verw_b8`, `verw_b9`, closed
  `decide`). No `ungueltig64` row exists in this region, so that
  obligation is vacuous (count theorem is 0).
- No `herstellerabhaengig` marking was needed: no row pins
  vendor-variable values (BSF/BSR zero-input, CPUID leaf answers,
  LZCNT/TZCNT fallback stay FREE per the reused families).

## Repair 1346 (all items addressed)

1. Prefix/extension dimension added: `praefix` field on `LEintrag`,
   rows for F3 0F B8 POPCNT (modelliert, `decodeBs` pin) and F3 0F BC/BD
   TZCNT/LZCNT (zurueckgestellt, family refusals reused); byte-184
   reason notes the F3 exception; Groups 15/8/10 justified with
   per-extension witness mapping (`gruppe15_mfence`, `gruppe8_alle`,
   `verw_b9`).
2. Rows 171/179 now witnessed generically (`bts_reg_alle`,
   `btr_reg_alle` via `roundtripBtReg`); CUTS narrowed to what is proved.
3. Minors fixed: row 191 is plain MOVSX (MOVSXD is opcode 63);
   `bt_reg_modelliert` comment says 0F BB; row 174 names both fence
   modules; BSF has pin + generic like BSR; SETcc mnemonics say
   register-direct (fehlt MOV rows keep architectural r/m names).

## Exact new names

`LStatus`, `LEintrag`, `praefixNr`, `schluessel`, `ledger`,
`statusZaehlt`, `ledger_laenge`, `ledger_modelliert`,
`ledger_zurueckgestellt`, `ledger_verweigert`, `ledger_ungueltig64`,
`ledger_fehlt`, `ledger_opcodes`, `ledger_nodup`,
`jcc_alle_modelliert`, `setcc_alle_modelliert`, `bt_reg_modelliert`,
`bt_imm_modelliert`, `bt_mem_modelliert`, `bt_memimm_modelliert`,
`bsf_modelliert`, `bsf_alle_modelliert`, `bsr_alle_modelliert`,
`bts_reg_alle`, `btr_reg_alle`, `popcnt_modelliert`,
`tzcnt_zurueckgestellt`, `lzcnt_zurueckgestellt`, `gruppe8_alle`,
`gruppe15_mfence`, `cpuid_modelliert`, `imul_modelliert`,
`cmpxchg_modelliert`, `verw_a6`, `verw_a7`, `verw_aa`, `verw_b8`,
`verw_b9`.

## Last build result

`./lean-probe grammatik/Grammatik/X86/OpcodeLedger0F80.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
`./lean-bau`: `Build completed successfully (694 jobs).`
All `#print axioms` within `[propext, Classical.choice, Quot.sound]`
(goal-theorem standard); ledger/count/coverage theorems axiom-free.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. Rule 13 not
applicable (no premise over program syntax, no `ZEUGE:` lines).

## Findings (`fehlt`): real instructions no family models

- MOVZX 0F B6/B7, MOVSX 0F BE/BF: VERY COMMON in compiler output
  (every u8/u16 -> wider load). Biggest gap of this region.
- SHLD 0F A4/A5, SHRD 0F AC/AD: uncommon, emitted for multi-word
  shifts/rotates and some crypto.
- CMPXCHG r/m8 0F B0: uncommon but real (byte atomics); only the
  64-bit LOCK form (0F B1) is modelled.
- PUSH/POP FS/GS 0F A0/A1/A8/A9: rare in user code.
- LSS/LFS/LGS 0F B2/B4/B5: legacy far-pointer loads, absent from
  64-bit compiler output.
- Group 15 0F AE remainder (FXSAVE/XSAVE/CLFLUSH/...): common in
  OS/runtime code; fence rows already modelled.

## Open / not claimed

Ledger is data plus decode/refusal pins only: no execution, flag,
fault-class or timing claim; no W/GX bridge; no source/checker/contract
claim. Opcode map is a named assumption, not checked provenance.
Rel16 Jcc forms named but not separately witnessed.

## Task issues (unchanged)

- LANE.md line 25 is truncated mid-sentence ("Do no...").
- The CONTEXT/MECHANISM paragraphs describe a different lane family
  (one-family `HwAdapter` connection with two-core witnesses) and
  contradict the ledger TASK; I followed the TASK. The independent
  reviewer (1346) confirmed this reading.
- One `./lean-probe` run timed out with no output while the identical
  retry passed; treated as a transient build-slot queue effect
  (full `./lean-bau` green afterwards).
