# MUSE-REPORT-1345: Opcode ledger 0F 80-BF

## What was done

NEW FILE `grammatik/Grammatik/X86/OpcodeLedger0F80.lean` (own namespace
`Gabbro.Grammatik.X86.OpcodeLedger0F80`, self-contained schema, no other
ledger dependency) plus one import line in `grammatik/Grammatik.lean`.

- Schema: `inductive LStatus | modelliert | zurueckgestellt | verweigert
  | ungueltig64 | fehlt`, `structure LEintrag` (op2 byte, mnemonic,
  status, modelling family module as string, one-line reason for every
  non-`modelliert` entry).
- `ledger`: 64 rows, one per second-opcode byte 128-191 (0F 80-BF),
  opcode map Intel SDM Vol 2 Appendix A, Table A-3 (named assumption;
  local snapshot `.tmp/HARDWARE-REFERENCES/`, edition 325462-093US;
  no AMD manual snapshotted, no AMD provenance claimed).
- Counts: 42 modelliert / 1 zurueckgestellt (group 15, 0F AE: fence rows
  modelled, FXSAVE/XRSTOR/CLFLUSH deferred) / 5 verweigert (0F A6, A7, AA,
  B8, B9) / 0 ungueltig64 / 16 fehlt. No duplicate, no skip
  (`ledger_opcodes`, `ledger_nodup`).
- Checked decodes (reused accepted decoders, never redefined): all 16
  near-Jcc rows via pilot `decode` (`jcc_alle_modelliert`, generic over
  condition/displacement/suffix); all 16 SETcc rows via `decodeSetCC`
  (`setcc_alle_modelliert`, generic); BT/BTS/BTR/BTC register, imm8,
  memory and memory-imm8 rows via `decodeBt` (`bt_reg_modelliert`,
  `bt_imm_modelliert`, `bt_mem_modelliert` reuse accepted pins,
  `bt_memimm_modelliert` closed `decide`); BSF pin and all BSR register
  rows via `decodeBs` (`bsf_modelliert`, `bsr_alle_modelliert`); CPUID via
  `decodeCpuFeature` (`cpuid_modelliert`); IMUL via the capstone chain
  itself (`imul_modelliert`, reuses accepted `kapUeber_wd_ext_imul2`);
  LOCK CMPXCHG via `decodeLock` (`cmpxchg_modelliert`).
- Checked refusals: all 5 verweigert rows prove `kapDecode ... = none`
  (`verw_a6`, `verw_a7`, `verw_aa`, `verw_b8`, `verw_b9`, closed
  `decide`). No `ungueltig64` row exists in this region, so that
  obligation is vacuous (count theorem is 0).
- No `herstellerabhaengig` marking was needed: no entry in this region
  is defined differently by Intel vs AMD in a way this ledger pins
  (BSF/BSR zero-input and CPUID leaf answers stay FREE per the reused
  families; nothing new is pinned here).

## Exact new names

`LStatus`, `LEintrag`, `ledger`, `statusZaehlt`, `ledger_laenge`,
`ledger_modelliert`, `ledger_zurueckgestellt`, `ledger_verweigert`,
`ledger_ungueltig64`, `ledger_fehlt`, `ledger_opcodes`, `ledger_nodup`,
`jcc_alle_modelliert`, `setcc_alle_modelliert`, `bt_reg_modelliert`,
`bt_imm_modelliert`, `bt_mem_modelliert`, `bt_memimm_modelliert`,
`bsf_modelliert`, `bsr_alle_modelliert`, `cpuid_modelliert`,
`imul_modelliert`, `cmpxchg_modelliert`, `verw_a6`, `verw_a7`,
`verw_aa`, `verw_b8`, `verw_b9`.

## Last build result

`./lean-probe grammatik/Grammatik/X86/OpcodeLedger0F80.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
`./lean-bau`: `Build completed successfully (694 jobs).`
All `#print axioms` within `[propext, Classical.choice, Quot.sound]`
(goal-theorem standard); ledger/count/coverage theorems axiom-free.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

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

## Task issues

- LANE.md line 25 is truncated mid-sentence ("Do no...").
- The CONTEXT/MECHANISM paragraphs describe a different lane family
  (connect ONE family via `HwAdapter`, budget witnesses, two cores);
  they contradict the actual TASK (ledger file). I followed the TASK
  and ignored the HwAdapter mechanism, which would have violated
  "put new Lean work in the NEW file" scope and the ledger schema.
- One `./lean-probe` run timed out with no output while the next
  identical run passed; treated as a transient build-slot queue
  effect, not a file issue (full `./lean-bau` green afterwards).
