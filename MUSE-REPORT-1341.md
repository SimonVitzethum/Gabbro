# MUSE-REPORT-1341: Opcode ledger two-byte opcodes 0F 00-3F

## Done

NEW FILE `grammatik/Grammatik/X86/OpcodeLedger0F00.lean` (739 lines) plus one
`import Grammatik.X86.OpcodeLedger0F00` line appended to `grammatik/Grammatik.lean`.
Own namespace `Gabbro.Grammatik.X86.OpcodeLedger0F00`, self-contained schema:

- `inductive LStatus | modelliert | zurueckgestellt | verweigert | ungueltig64 | fehlt`
- `structure LEintrag` with `op : Nat`, `ext : String`, `mnemonik : String`,
  `status : LStatus`, `familie : String`, `grund : String`.

Checked part, all against the capstone chain `kapDecode` (`HwKapsteinDecoder.lean`,
reused unchanged):

- 5 `takes_*` theorems (`takes_movsd`, `takes_movss`, `takes_cvtsi2ss`,
  `takes_cvttss2si`, `takes_ucomiss`), each `decide`d to the exact family arm.
- 134 `refuses_*` theorems (`kapDecode <witness> = none`), each `decide`d.
- `ledger0F00`: 139 rows. Summary theorems, all `decide`d:
  `ledger_anzahl_modelliert` = 5, `ledger_anzahl_verweigert` = 36,
  `ledger_anzahl_ungueltig` = 34, `ledger_anzahl_fehlt` = 49,
  `ledger_anzahl_zurueck` = 15, `ledger_anzahl_gesamt` = 139,
  `ledger_schluessel_eindeutig` (key nodup), `ledger_deckt_ab`
  (every byte 0-63 occurs; needs `set_option maxRecDepth 10000 in`).
- CUTS block and `#print axioms` for all 147 theorems. Axiom report:
  takes/refuses depend on `[propext, Quot.sound]` only (subset of the goal
  standard axioms, no `Classical.choice` needed); the 8 summary theorems
  depend on no axioms at all. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

Last `./lean-probe` result line: `== 0 error(s) in the COMPLETE output; exit 0`.
Last `./lean-bau` result line: `== exit 0; 0 error line(s) in the COMPLETE output`
(`Build completed successfully (694 jobs)`).

## Findings (`fehlt` product)

49 missing rows. Most common in real compiler output, all refused by `kapDecode`:

- 0F 1F /0 NOP (alignment padding in every binary; the most common gap),
  0F 1E F3 ENDBR64 (every CET indirect-branch target),
  0F 10/11/28/29 MOVUPS/MOVUPD/MOVAPS/MOVAPD loads and stores,
  0F 14/15 UNPCKL/UNPCKH, 0F 12/16/17 MOVLPS/MOVHPS family,
  0F 2E/2F 66 UCOMISD/COMISD and 0F 2F COMISS,
  0F 0B UD2 (Rust panics, kernel BUG), 0F 31 RDTSC, 0F 01 F9 RDTSCP,
  0F 01 D0 XGETBV, 0F 18 PREFETCHh, 0F 0D PREFETCHW, 0F 2B MOVNTPS/MOVNTPD.
- Asymmetric gaps (same family, one form decodes, the sibling refused):
  MOVSS/MOVSD stores refused while loads decode; CVTSI2SD, CVTTSD2SI,
  CVTSD2SI, CVTSS2SI refused while CVTSI2SS/CVTTSS2SI decode.
- Only 5 of 139 rows decode: the model covers almost nothing of 0F 00-3F.

## What remains open

Decoding classification only; no execution, fault, ordering or W/GX claim.
Only the listed canonical byte strings are decided (redundant prefixes and
other ModRM/SIB shapes are not pinned). Folded rows (Group 7 mod=11 exotics,
0F 38/0F 3A escapes) carry one witness each. Map transcription is a named
provenance (clone-local Intel 325462-093US snapshot), not a checked claim.

## Task issues (believed wrong)

1. The CONTEXT/MECHANISM paragraphs describe a different lane kind (connect a
   family to `HwMaschine` via `HwAdapter`, multi-core witness, `HwWf`).
   The TASK/PURPOSE/FILE/CHECKED-PART/FINDINGS lines describe the opcode
   ledger. I implemented the ledger; the adapter work is untouched.
2. The task line is truncated after "Do no..." (2000 chars), so trailing
   requirements may exist unseen; the visible requirements are all met.
3. Corrections made from the snapshot (not from memory): SYSENTER/SYSEXIT are
   Valid in 64-bit mode (privileged entry, `verweigert`, not `ungueltig64`);
   0F 1C is Group 18 (CLDEMOTE /0, rest reserved NOP); 0F 18 has /6,/7 IT
   hints; 0F 38/0F 3A are the Table A-4/A-5 escapes.
4. No `herstellerabhaengig` marking was needed: PREFETCHW/MPX rows are refused
   (nothing pinned), so no vendor-specific behaviour is modelled.
5. No `_zeuge` companion: no theorem quantifies over program syntax and the
   task names no `ZEUGE:` target, so rule 13 does not trigger.
