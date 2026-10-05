# MUSE-REPORT-1339: Opcode ledger, one-byte opcodes C0-FF

## What was done

New file `grammatik/Grammatik/X86/OpcodeLedger1ByteC0.lean` (namespace
`Gabbro.Grammatik.X86.LedgerC0`), plus one import line appended to
`grammatik/Grammatik.lean`. The file is self-contained (does not depend
on other ledger lanes) and follows the task schema exactly: `LStatus`
(`modelliert | zurueckgestellt | verweigert | ungueltig64 | fehlt`),
`LEintrag` (opcode bytes, prefix/reg extension, mnemonic, status,
family/file string, one-line reason).

Content: 134 rows (`tabelleC0` 30, `tabelleD` 44, `tabelleE` 16,
`tabelleF` 44, joined as `tabelleC0FF`); group opcodes expanded by
ModRM.reg extension (C0/C1/D0-D3/F6/F7/FE/FF x8 each). Counts, all
proved by `decide`: 32 modelliert / 22 verweigert / 5 ungueltig64 /
42 fehlt / 33 zurueckgestellt (`lzahl_*`, `lzahl_gesamt`).
Exact-once coverage: `labdeckung_alle` (every byte 192-255 occurs) and
`lkein_duplikat` (no repeated (opcode, ext) pair, via the local
all-pairs boolean `paareVerschieden`).

Checked part: 30 witness theorems `lmod_*` (every modelliert row decodes
through its family: accepted pins reused where they exist, closed
`decide` literals otherwise; `lmod_C4` runs through the capstone chain
via `kapKette_avx2`); 22 chain refusals `lver_*`
(`kapDecode ... = none`, including the silicon SHL-alias rows C1/6,
D3/6 refused by the ShiftCodec digit whitelist and the byte Group 3
rows explicitly refused by `decodeWd`); 5 decode-to-nothing theorems
`lung_*` (CE, D4, D5, D6, EA).

Last `./lean-bau` result line: `Build completed successfully (694 jobs).`
(`== exit 0; 0 error line(s)`). `./lean-probe` on the file: 0 errors.
`#print axioms` for every main theorem: standard only (`propext`,
`Classical.choice`, `Quot.sound`, all inherited from reused accepted
pins); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` of my own.

## Findings (`fehlt`: real instructions no family models)

Frequency notes are estimates from compiler-output knowledge, not
measurements.

High frequency in compiler output:
- D1 /4,/5,/7 (SHL/SHR/SAR Ev,1, REX.W): strength-reduced multiply /
  halve by two, very common. `ShiftCodec` covers only C1-imm and D3-CL.
  Strongest family-level gap.
- C6 MOV Eb,Ib (`movb $imm`): very common.
- C5 VEX2 prefix: no VEX2 row is modeled anywhere; VEX-encoded SSE
  (`vpxor` idiom etc.) is very common in modern -O2 output. Biggest
  structural gap.
- C1 /0,/1 and D3 /0,/1 (ROL/ROR Ev): rotate idioms lower to
  rol/ror; common in crypto/hash code.
- C9 LEAVE: common with frame pointers (-O0, kernels).
- CC INT3: `__builtin_trap`, kernel traps, debugger breakpoints.
- C2 RET imm16: stdcall cleanup (32-bit), some 64-bit code.

OS/kernel use (common there, rare in userspace output):
- F4 HLT (idle loop), FA/FB CLI/STI (interrupt masking), CF IRET
  (note: machine-level `iretSchritt` exists in `HwNestedInterrupts`,
  but no byte decode — a decode gap, not a semantics gap), CD INT ib,
  F1 INT1, FC CLD (boot/libc string setup), FD STD, FF/6 PUSH Ev.

Lower frequency: C0/D0/D2 byte shifts and rotates (8-bit bitfields,
crypto), D1/D3 RCL/RCR excluded (those are `zurueckgestellt`).

`verweigert` rows worth revisiting (deliberate refusals of common
instructions): all of F6 (byte TEST/NOT/NEG/MUL/DIV/IDIV — `testb`
and `negb` are common) refused by `decodeWd` by design (word widths
only); F7 /0,/1 TEST (`test $imm`), /2 NOT, /3 NEG (`neg` is common),
/5 one-operand IMUL (no `WdBefehl` row); C1/6 and D3/6 (silicon
executes the SHL alias, the model refuses it).

Structural note: six `modelliert` families are witnessed at family
level only and are NOT connected to the `kapDecode` chain (carry
FE/FF, indirect FF/2+4, ports E4-E7/EC-EF, width F7, scalar FP F2/F3,
LOCK F0). Only the chain levels (width dispatcher, s32, MXCSR, LOCK,
lockAdr, compact, core, AVX2) have chain-level witnesses.

No C0-FF row was found where Intel and AMD define the opcode
differently, so no `herstellerabhaengig` marking was needed. No AMD
manual is in the clone, so no AMD fact is claimed either way. The
Group 2 /6 (= SHL alias) and Group 3 /1 (= TEST alias) facts are
Intel SDM text (snapshot `.tmp/HARDWARE-REFERENCES/`,
`intel-instruction-reference.txt` line 207955), cited in CUTS.

## What remains open

- Family-level `fehlt`/`verweigert` rows need owner lanes (shift
  extension to D1/C0/D2 widths, VEX2 rows, TEST/NOT/NEG rows,
  control/flag/system rows, x87 if ever wanted).
- Connecting the six family-only decoders to `kapDecode` (or
  documenting their exclusion) belongs to follow-up work.
- The report frequencies above are estimates; a measured corpus
  count (e.g. over emitted binaries) is not part of this lane.

## What I believe is wrong in the task

- The CONTEXT (§27) and MECHANISM (§28) paragraphs describe a
  different lane (connect ONE family to the coherent machine with a
  `HwAdapter`, `HwWf` preservation, two-core forwarding witness).
  The actual ledger task (§§24-25) needs none of that; I followed
  §§24-25 and did not define an adapter or touch the machine.
- §25 is truncated mid-sentence ("Do no...").
- The `ungueltig64` examples name "segment-register push/pop forms"
  (opcodes 06/07/0E/16-1F), which lie outside C0-FF.
- Rule 13 (`_zeuge` for ∀-over-syntax premises) does not apply to
  this file: all theorems are closed equations over concrete bytes,
  so no inhabitation witness was needed.

## Names of new definitions/theorems

`LStatus`, `LEintrag`, `tabelleC0`, `tabelleD`, `tabelleE`,
`tabelleF`, `tabelleC0FF`, `lmod_C1_4`, `lmod_D3_7`, `lmod_F0`,
`lmod_C4`, `lmod_FE0`, `lmod_FF0`, `lmod_FF1mem`, `lmod_F3`,
`lmod_EB`, `lmod_FF2`, `lmod_FF4`, `lmod_C3`, `lmod_C1_5`,
`lmod_C1_7`, `lmod_D3_4`, `lmod_D3_5`, `lmod_C7`, `lmod_E8`,
`lmod_E9`, `lmod_E4`, `lmod_E5`, `lmod_E6`, `lmod_E7`, `lmod_EC`,
`lmod_ED`, `lmod_EE`, `lmod_EF`, `lmod_F2`, `lmod_F7_4`,
`lmod_F7_4_64`, `lmod_F7_6`, `lmod_F7_7`, `lmod_FE1`, `lmod_FF1`,
`lver_C1_6`, `lver_D3_6`, `lver_F6_0` … `lver_F6_7`, `lver_F7_0`,
`lver_F7_1`, `lver_F7_2`, `lver_F7_3`, `lver_F7_5`, `lver_FE_2` …
`lver_FE_7`, `lver_FF_7`, `lung_CE`, `lung_D4`, `lung_D5`,
`lung_D6`, `lung_EA`, `lzahl_modelliert`, `lzahl_verweigert`,
`lzahl_ungueltig64`, `lzahl_fehlt`, `lzahl_zurueckgestellt`,
`lzahl_gesamt`, `labdeckung_alle`, `paareVerschieden`,
`lkein_duplikat`.
