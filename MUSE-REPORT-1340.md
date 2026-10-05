# MUSE-REPORT-1340: Exact review of candidate 1339 (opcode ledger C0-FF)

CANDIDATE: 1339 efaaabc09b666a2d0233d7c953c4716b9b1021d7
VERDICT: ACCEPT

## Substantive verdict (unchanged: accept)

Reviewed author lane 1339, pinned head
`efaaabc09b666a2d0233d7c953c4716b9b1021d7`,
base `574ac3d75180a53907fa28302e3af11cf2d9f2db`, files:
`MUSE-REPORT-1339.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/OpcodeLedger1ByteC0.lean`.
Delivered as files under `.tmp/review/author-1339/` (SNAPSHOT.json,
PATCH.diff, OWNER-TASK.md, BUILD-EVIDENCE.json); the pinned hash was never
read via git, per the review rule.

## What was checked

1. **Forbidden tactics:** no `sorry`/`admit`/`native_decide`/`unsafe` and no
   `axiom` declaration in the candidate Lean file (grepped
   `.tmp/review/author-1339/grammatik/Grammatik/X86/`; the only matches are
   the 69 `#print axioms` lines). No `intro _` / `have _ :=` discards.
   No premise has type `Prop` itself; all theorems are closed equations
   over concrete bytes/lists, except `lmod_EB (rel : BitVec 8)`, whose
   premise is used by the proof (`roundtripC_jump8 rel []`).
2. **Axioms:** per BUILD-EVIDENCE `#print axioms` output, every main theorem
   depends only on `propext`, `Quot.sound` (and `Classical.choice` where the
   reused pins carry it) or on nothing. Standard only.
3. **Existing files:** PATCH.diff touches exactly three files: the new ledger
   file, the author report, and one appended import line
   `import Grammatik.X86.OpcodeLedger1ByteC0` in `grammatik/Grammatik.lean`.
   No existing theorem weakened or deleted.
4. **Lifted, not copied:** all 18 reused pins/roundtrips named by the
   `lmod_*` theorems exist verbatim in this clone at the candidate's base
   (`pin_shift_imm_rax_dekode`, `pin_shift_cl_rcx_dekode`,
   `pin_lock_xadd_decodiert`, `kapKette_avx2`, `pin_decode_incReg8`,
   `pin_decode_incReg64`, `pin_decode_decMem`, `kapW_s32_akzeptiert`,
   `roundtripC_jump8`, `roundtrip_indReg_call`, `roundtrip_indReg_jmp`,
   `roundtrip_ret`, `pin_wdmul_ecx_dekode`, `pin_mulRax_rcx_dekode`,
   `pin_divRax_r8_dekode`, `pin_idivRax_rcx_dekode`,
   `fpRoundtrip_movsdRR`), as do all invoked decoders (`kapDecode`,
   `decodeShift`, `decodeLock`, `decodeCarry`, `s32Decode`, `decodeC`,
   `decodeIndirekt`, `decode`, `decodeIo`, `fpDecode`, `decodeWd`,
   `decodeMulDiv`). The `by decide` witnesses evaluate these accepted
   definitions; nothing is redefined.
5. **Refusals really refuse (spot-checked byte strings):** F6/0
   `[F6,C0,00]` (ModRM reg 0 + imm), F6/1 `[F6,C8,00]` (alias reg 1),
   F7/0 `[F7,C0,imm32]`, FE/2 `[FE,D3]` (reg 2), FF/7 `[FF,FB]` (reg 7),
   C1/6 `[48,C1,F0,01]` (reg 6 + imm). All are well-formed encodings of the
   claimed rows, and per BUILD-EVIDENCE each `lver_*`/`lung_*`
   (`kapDecode ... = none`) closes by `decide`.
6. **Counts verified by hand against the table:** 32 modelliert / 22
   verweigert / 5 ungueltig64 / 42 fehlt / 33 zurueckgestellt, total 134
   (C0: 30 rows; D: 44; E: 16; F: 44). Minor prose slip: the report says
   "30 witness theorems `lmod_*`" but the file contains 34 (F7/4 is witnessed
   twice, via `decodeWd` and `decodeMulDiv`; FF/1 has a register and a memory
   witness). Every modelliert row has at least one witness; every verweigert
   and ungueltig64 row has exactly one refusal theorem. The slip understates
   the work and is not a defect.
7. **Silicon spot checks:** CE (INTO), D4 (AAM), D5 (AAD), D6 (SALC),
   EA (far JMP) as invalid in 64-bit mode: correct. C4 as VEX3 with legacy
   LES invalid, C5 as unmodelled VEX2: correct. C1/6 and D3/6 marked
   `verweigert` with the reason that silicon executes the SHL alias while the
   model refuses it: honest, vendor-neutral (no pinned observed value, no AMD
   provenance claimed, Intel alias fact cited to the SDM snapshot in CUTS).
   C7 `[48,C7,C0,01,00,00,00]` (MOV r/m64,imm32) and F7 `[F7,E1]`
   (MUL ECX): correct encodings.
8. **Witness rule:** rule 13 / the "non-degenerate witness" checklist item
   does not apply: no theorem quantifies over program syntax, so no `_zeuge`
   is required. The author states this correctly. (The OWNER-TASK
   CONTEXT/MECHANISM paragraphs describe a different lane -- a `HwAdapter`
   machine connection with a two-core forwarding witness. The author
   correctly followed the ledger task of sections 24-25 and did not define
   an adapter. The truncated section 25 and the out-of-region `ungueltig64`
   examples noted in the author report are task-text defects, not candidate
   defects.)
9. **CUTS honest, no overclaim:** the CUTS block states family-level-only
   witnesses for six decoder families, `fehlt` rows as literature reading
   rather than proved absence, frequencies as estimates, no vendor-difference
   row claimed, no silicon re-check beyond accepted pins, no W/GX bridge, no
   source/checker/contract/loader/budget claim. The claim matches the proof.
   No hardware-correspondence or W/GX claim is made.

## Findings worth keeping (not repair reasons)

- Strongest reported gaps: D1 /4,/5,/7 (64-bit SHL/SHR/SAR by 1), C6 (movb
  imm), C5 (VEX2), C1/D3 /0,/1 (ROL/ROR), plus the deliberately refused but
  common F6 byte group and F7 TEST/NOT/NEG rows. These are the product the
  lane was asked for and are documented with frequency estimates.
- Coverage theorems prove byte-presence (`labdeckung_alle`), pair-uniqueness
  (`lkein_duplikat`, via local `paareVerschieden` since this toolchain has
  no `List.pairwise`/`List.eraseDup`) and total count (134). Row-level
  completeness rests on the human-readable table itself; the theorems prove
  what their names state and do not overclaim.

## Blocker (apparatus, not candidate)

- This reviewer's `bash` tool calls were twice rejected at the permission
  layer, so `./lean-probe` (on a scratch copy of the candidate file) and
  `./lean-bau` could not be run independently. Shell access was restored
  afterwards: the machine-readable `CANDIDATE:`/`VERDICT:` lines were added
  (substantive verdict unchanged) and this report committed via `./commit.sh`.
  The build verdicts cited
  above are the author's BUILD-EVIDENCE.json (final entries: `lean-probe`
  0 errors; `lean-bau` exit 0, `Build completed successfully (694 jobs).`),
  which is internally consistent with the delivered file (the intermediate
  `eraseDup`/`pairwise`/`maxRecDepth` failures are visibly fixed in the final
  content). The serial merge gate must confirm a green build before
  integration; that confirmation is still outstanding from this lane.
- Last `./lean-bau` result line (author evidence, not an own run):
  `Build completed successfully (694 jobs).`

## Names reviewed (all in `Gabbro.Grammatik.X86.LedgerC0`)

`LStatus`, `LEintrag`, `tabelleC0`, `tabelleD`, `tabelleE`, `tabelleF`,
`tabelleC0FF`, 34 `lmod_*`, 22 `lver_*`, 5 `lung_*`,
`lzahl_modelliert`, `lzahl_verweigert`, `lzahl_ungueltig64`,
`lzahl_fehlt`, `lzahl_zurueckgestellt`, `lzahl_gesamt`,
`labdeckung_alle`, `paareVerschieden`, `lkein_duplikat`.
