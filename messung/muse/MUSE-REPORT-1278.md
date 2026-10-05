# MUSE-REPORT-1278: Exact review of candidate 1277 (BT/BTS/BTR/BTC)

Lane 1278, clone `/home/simon/Dokumente/gabbro-muse/a1278`, branch `muse/1278`.
Review-only lane: I own only this file. Nothing else was touched
(`git diff master..HEAD` in this clone is empty except this report).

CANDIDATE: 1277 7e585b8e460b3c8d699278113a99faf19c71442b
VERDICT: ACCEPT

## What was reviewed

The candidate diff (base `73836654`, pinned HEAD above) contains exactly 3 files:

- NEW `grammatik/Grammatik/X86/IntBitTest.lean` (2161 lines)
- one appended line `import Grammatik.X86.IntBitTest` in `grammatik/Grammatik.lean`
- NEW `MUSE-REPORT-1277.md` (author report, covers `e79c3b66`; the pinned
  HEAD adds only that report file, so the Lean content is identical to the
  green build below)

Access note (honest method limitation): tool permissions confine this lane to
its own clone, so I could not enter the author clone. I reviewed the
coordinator snapshot at `.tmp/review/author-1277/` (PATCH.diff of 2328 lines
with exactly the 3 `diff --git` headers above, the byte snapshot of the new
file, OWNER-TASK.md, MUSE-REPORT-1277.md, BUILD-EVIDENCE.json with per-step
`./lean-probe`/`./lean-bau` transcripts). I read the full 2161-line file,
checked every silicon claim against the in-clone Intel SDM text extract
(`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`), and verified
every reuse name against the live tree.

## Check results (each item of the review brief)

1. **No sorry/axiom/native_decide**: mechanical grep over the new file for
   `\bsorry\b`, `\badmit\b`, `native_decide`, `\bunsafe\b`, `^axiom` finds
   exactly one hit: line 1348, English prose ("admit no successor state").
   No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` anywhere.
2. **`#print axioms` standard**: 57 `#print axioms` lines at end of file;
   the author build transcript shows every main theorem within
   `[propext, Classical.choice, Quot.sound]` or subsets (several `decide`
   pins depend on no axioms at all). Standard goal axioms, nothing else.
3. **Existing files untouched except one import line**: PATCH confirms only
   the single appended import in `Grammatik.lean`. No diagnostic/gift/example
   numbers, no Rust changes.
4. **Every premise used**: no `intro _`, no `have _ :=` in the file. The
   near-definitional selection theorems (`decodeBtHw_prefers_ext`,
   `decodeBtHw_bt/nichts`, `btHwSchritt_ext/bt_ok/bt_verweigert`,
   `adapterBitTest_ok`) are genuine embedding/agreement equations in the
   accepted `HwMulDivWidth` pattern (dispatcher prefers `decodeExt`, adapter
   re-embeds the family step), not conclusions restating premises. No
   contract parameters quantified away (no program-syntax premises at all);
   the flag class `btErlaubt` pins CF/ZF on concrete values and leaves
   OF/SF/AF/PF free.
5. **Evaluator lifted, not copied**: no accepted BT evaluator existed (the
   owner task measures this). The value semantics (`btRoh`, `btSchreibe`,
   `btSchritt`) is defined once in-file and lifted unchanged into the
   `HwAdapter` register plug and the TSO memory path, with exact agreement
   theorems (`adapterBitTest_ok/proj`, `btHwSchritt_bt_ok`). Every reused
   name I checked exists in the tree: `mergeRegNarrow`, `trunc`, `maske`,
   `effAddr`, `schrittRegister`, `ripNach`, `regSet_fremd`, `issueListe`
   (+`issueListe_kein_speicher/haengt_an`), `setKernDaten(+_wf)`,
   `setTso(+_wf)`, `setKernVonFp_*`, `projZustand`, `decodeExt`, `stepExt`,
   `extLen`, `parseLe32_leBytes32`, `codeReg_regCode`,
   `merkmalZugelassen_heisst_beide`, `zeugeFlags`, `kontextReset`,
   `basisHw`, `basisBereit`, `leBytes32`, `parseLe32`, `modrmReg/Mem`,
   `regHigh/Low/Code`, `codeReg`, `byteNat/natByte`,
   `byteNat_natByte_of_lt`, `laengeOk`, `loadByte`, `issueByte`,
   `flushKern`, `tsoAnsicht(+_speicher)`, `decide_eq_true`,
   `testBit_toNat`, `getLsbD_and`, `Nat.testBit_two_pow_of_ne/succ`,
   `Nat.testBit_two_pow_sub_one`. Nothing is redefined.
6. **Planted refusals really refuse**: `sonde_bt_verweigert` (9 rows: LOCK,
   66+REX.W, REX.X, REX.R group row, mod-0, mod-1, bad group digit, bad
   opcode, wrong SIB) and `sonde_bt_abgeschnitten` (7 truncation rows) are
   closed `decide` proofs of `= none`; `decodeBt_lock` proves LOCK refusal
   for every suffix; `btSchritt_mem/memImm_verweigert` and
   `adapterBitTest_verweigert_memReg/memImm/bei_laenge` refuse the wrong
   plug. Round trips hold over any suffix: `roundtripBtReg` (4x3x16x16 =
   3072 kernel-`rfl` cases), mem/imm/memImm round trips with symbolic op.
7. **Witness non-degenerate**: `btWit_zeuge` joins 23 conjuncts — core 0 BTS
   rax (8 -> 10, CF 0) and core 1 BTR rbx (15 -> 14, CF 1) through the
   adapter; memory BTS on both cores through TSO events (4 entries pending
   each, CF 0, shared memory still 0); owner-only forwarding (core 0 reads
   42, core 1 reads 0); drain changes shared memory 0 -> 42 and core 1 then
   reads 42; effective addresses 8194 (offset 20) and 8191 (offset -1);
   decode pin, LOCK refusal instance, set/reset law instances,
   well-formedness. Two cores write; a memory-changing drain is present.
8. **Silicon vs SDM extracts**: opcode rows match the BT/BTC tables
   (0F A3/AB/B3/BB, 0F BA /4../7, ModRM reg = offset source, r/m = base;
   REX.W selects 64-bit, 0x66 selects 16-bit, REX.X=0 with SIB exactly
   0x24, mod-2+disp32 canonical which also keeps rbp out of the
   RIP-relative trap); pinned byte strings re-derive by hand (BTC rax,rcx
   = 48 0F BB C8; BTS edx,5 = 40 0F BA EA 05; BTR [rbx+16],rcx = 48 0F B3
   8B + disp32 16; BT [rsp],rax needs SIB 24). CF = old selected bit, ZF
   unaffected (proved, not just kept), OF/SF/AF/PF free — matches "Flags
   Affected". LOCK refusal is the safe direction of the SDM `#UD If the
   LOCK prefix is used`. Register offsets wrap mod 16/32/64. The memory
   footprint (operand-size bytes at base+disp32+floor(offset/8)) addresses
   the same physical bit as the SDM `EA + size*(off DIV size)` window
   (verified algebraically, incl. negative offsets). Lengths 4..11 sit
   inside 1..15 (`btLaenge_encode`, `btLaenge_ok`).
9. **CUTS honest, claim not larger than proof**: CUTS discloses no hardware
   correspondence (self-consistency only), refused mod-0/mod-1/SIB-index/
   RIP-relative/8-bit forms, no per-access W/GX bridge and no whole-word
   atomicity beyond byte drains, byte-vs-word correspondence on instances
   only, no timing claims, and flags the imm8-memory-offset unsigned
   modelling as open against the SDM extracts (the SDM "high order bits
   ignored" note). The report lists the same. No W/GX or source/ABI/loader
   claim is made anywhere.

No unsupported desired-correctness premises, no weakened guarantees (no
existing theorem touched), no fake closure.

## `./lean-bau` result

Author evidence at candidate content: `== exit 0; 0 error line(s)`,
`Build completed successfully (659 jobs)`, clean `git status`.
My lane run on this clean base clone: `== exit 0; 0 error line(s) in the
COMPLETE output`, last line `Build completed successfully (677 jobs).`
(The job-count delta is master moving on: +`IntCarryForms.lean` from the
1275 merge. I did not and may not build the candidate in this clone —
OWN ONLY this report — so the merge gate must rebuild the candidate on
current master; in particular the `ext_weist_*` no-shadowing pins are
load-bearing against the newer `decodeExt`. ADC/SBB/INC/DEC encodings do
not overlap the BT rows, so no collision is expected, but only the merge
build proves it.)

## Open / follow-ups (non-blocking, for the record)

- memImm large-immediate semantics: model masks nothing (`n/8`, `n%8`);
  SDM says high bits are ignored (low 3/5 bits for 16/32-bit). Disclosed in
  CUTS; worth a small follow-up lane (mask `n` to the width before the
  target computation + a `decide` pin), not a merge blocker since no
  hardware correspondence is claimed.
- 66+REX.W refusal is safe-direction over-approximation (silicon decodes
  it as 64-bit); disclosed canonical-subset behaviour, fine.
- Review method: snapshot-based (see access note above), pinned HEAD
  `7e585b8e460b3c8d699278113a99faf19c71442b`, snapshot flag `clean: true`.

## Task remarks

The review brief's phrase "the family's accepted evaluator" has no
referent (the owner task itself measures that none existed); I read it as
"the family's evaluator as defined in-file", which is lifted unchanged —
criterion met. The brief's "`git diff master..HEAD` in the author clone"
step was performed against the coordinator snapshot for the pinned HEAD
instead, for the access reason stated above; scope (3 files) matches the
snapshot manifest exactly.
