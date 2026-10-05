# MUSE-REPORT-1337: Opcode ledger one-byte opcodes 80-BF

## What was done

New file `grammatik/Grammatik/X86/OpcodeLedger1Byte80.lean` (own namespace
`Gabbro.Grammatik.X86.OpcodeLedger80`, self-contained schema, no other-ledger
dependency) plus one `import Grammatik.X86.OpcodeLedger1Byte80` line at the end
of `grammatik/Grammatik.lean`. Seven commits on `muse/1337` (skeleton + six
chunks; the last commit message underlabels chunk 7, content is complete).

Schema: `LPraefix` (ohne/rexW/rexB/lock/ops16), `LStatus`
(modelliert/zurueckgestellt/verweigert/ungueltig64/fehlt), `LEintrag`
(prefix, opcode, ModRM.reg extension, mnemonic, status, modelling family
module, one-line reason, expected `kapFam` tag, canonical witness bytes).
`kapFam` maps the `kapDecode` chain answer to a family tag
(0 breit, 5 kompakt, 6 kern, 7 avx2, 255 refusal).

Checked part (all `decide`/`rfl`-free closed computations, green):
- 238 ledger rows, each with one theorem: `kapFam witness = tag` for the 43
  modelled rows, `kapDecode witness = none` for all 195 others (so every
  refusal, not only `verweigert`, is a checked fact).
- 15 deferred-family pins (`pin_carry_*`, `pin_xchg_reg/mem`, `pin_lea`):
  `decodeCarry`/`decodeXchg`/`decodeLea` accept while the chain refuses.
- Summary: counts per status (43/14/28/40/113, total 238),
  `abdeckung_nodup` + `abdeckung_all` + `erwartet_nodup` combined into
  `abdeckung_vollstaendig` (exact-once coverage over the key space),
  `modelliert_tag_ok` / `abgewiesen_tag_ok` (row tags match the chain).
- CUTS block and `#print axioms` for all summary theorems and pins.
  Axioms are `[propext, Quot.sound]` (counts: none) — subset of the
  goal-theorem triple, no `Classical.choice` needed.

Last `./lean-bau` result line: `Build completed successfully (694 jobs).`
`./lean-probe` on the ledger file: `== 0 error(s)`.

## Findings (the product): what real software uses that the chain misses

Pervasive (in nearly every binary): bare Group-1 widths 80/81/83
(`add eax,5` = 83 C0 05); Group-1 memory forms even under REX.W
(`decodeCRex` needs mod=3, noted per row); TEST 84/bare-85/A8/A9
(`test eax,eax`); MOV 88/89/8A/8B bare and 8B-reg-reg; LEA 8D bare
(REX.W form deferred, family exists); NOP 90 (alignment padding);
POP 8F/0 (epilogues). Common: MOV r8,imm8; REP MOVSQ/STOSQ; LOCK+XCHG
mem (seq-cst stores, `atomic_exchange`); TEST r64,imm. Occasional:
PUSHF/POPF, CMPS/SCAS scans, byte XCHG. Rare: moffs A0-A3, LODS,
SAHF/LAHF (herstellerabhaengig: CPUID LAHF_SAHF_64-gated, stay FREE),
XCHG r,rax, REX.W byte forms.
Deferred integration debt (family modelled, chain unwired, 14 rows):
Group-1 ADC/SBB (12, `IntCarryForms`), REX.W+87 XCHG (`XchgOrderNeed`),
REX.W+8D LEA (`AddressEncoding.decodeLea`).
Refused by design (28): segment MOVs 8C/8E (no SReg state), WAIT
(no wait semantics), 16-bit converts (no 16-bit width). Invalid in
64-bit (40, all decode to nothing): 82 (SDM Vol 3B 25: #UD), 9A
(CALL entry: Invalid), 8F /1-7 (Group 1A defines /0 only), 8C/8E /6-7
(Table B-8 sreg3 reserved); plus 2 checked LOCK-reg #UD theorems.
Modelled (43): REX.W 81/83 non-carry reg-direct, TEST-reg64,
MOV-reg64/mem64, B8-BF all prefix classes, CWDE/CDQE/CWD/CQO.

## Open / not claimed

ModRM.mod/SIB/disp splits live in reason notes, not keys; REX R/X/B
combos beyond canonical witnesses, 66/67/F2/F3 not keyed (except
CBW/CWD-16); frequency grades are judgement, not measurement; no
execution semantics, no HwSchritt link, no W/GX bridge. Provenance is
the clone-local Intel SDM text 325462-093US only (no AMD manual, no
AMD claims). Scratch probes (.tmp/probe84*.lean, .tmp/out*.txt) are
uncommitted in `.tmp/`.

## Task issues believed wrong

1. The CONTEXT/MECHANISM paragraphs describe a different lane kind
   (HwAdapter family-to-machine connection, HwWf, two-core witness)
   contradicting the TASK paragraph and the owned file name. I delivered
   the ledger per TASK and did not build HwAdapter (would have broken
   OWN ONLY).
2. Task line 25 is truncated mid-sentence ("Do no..."); I followed the
   visible spec plus HARD RULES.
3. Rule 13 (inhabitation) is N/A: no theorem has a program-syntax
   premise and no ZEUGE target exists.
4. `set_option maxRecDepth 100000 in` (tree precedent: HwContextState,
   ScalarFloat32HardwareForms) was needed for three list-level decides;
   docstrings must precede nothing — `set_option` after `/--` is a
   parse error, placed before it instead.
