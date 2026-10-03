# MUSE-REPORT-901 — Exact review of author 751: compact AND/OR/XOR with imm8

Lane 901, clone `/home/simon/Dokumente/gabbro-muse/a901`, branch `muse/901`.
Owned file only: this report. No source, no live controls touched.

## CANDIDATE and VERDICT

- CANDIDATE: 751 `27b1a7ba73eb09fccce0c8e6a5124601219939ac`
  (identity and base `23b9a42fb44f2365b636cf8a9c440a2dfd8cae50` from the
  coordinator snapshot `.tmp/review/SNAPSHOT.json`; the author's clone was
  not accessed. The snapshot content tree
  `.tmp/review/author-751/` — task, report, PATCH, build evidence and the
  post-image files — is what was reviewed byte for byte.)
- VERDICT: ACCEPT (bounded, see §5). No repairs required.

## What the candidate is

Three files, confirmed from `PATCH.diff` hunks and the snapshot tree —
nothing else:

1. `grammatik/Grammatik/X86/CompactImm8Logic.lean` (new, 551 lines) —
   connection module over the accepted `IntegerHardwareForms` vocabulary.
2. `grammatik/Grammatik.lean` — exactly one additive line:
   `import Grammatik.X86.CompactImm8Logic`.
3. `MUSE-REPORT-751.md` — the author report.

No new canonical definition: encoder, decoder, step, fetch and byte step
(`encodeIntHwImm`, `decodeIntHwImm`, `stepIntHwImm`, `immWort`,
`imm8Erweitern`, `immPasst8`, `fetchIntHwImm`, `intHwImmByteschritt`) are
all reused from accepted modules. No diagnostic/gift/example/CLI numbers,
no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
files (file list proves the scope; the diff touches only the three files).

## Evidence (reproduced, not trusted)

- `./lean-probe .tmp/review/author-751/grammatik/Grammatik/X86/CompactImm8Logic.lean`
  run in THIS clone (base newer than the author's, so this is also a
  drift check): first line
  `== 0 error(s) in the COMPLETE output; exit 0`.
  The file was checked in place; nothing was copied into `grammatik/`,
  working tree stayed clean (`git status --short` empty afterwards).
- Author build evidence shows the in-lane path honestly: intermediate
  red probes (unknown tactic, unsolved goals, application mismatches)
  converging to `== 0 error(s)` and a final green `./lean-bau`
  (`== exit 0; 0 error line(s)`, `Build completed successfully (483 jobs)`).
  The two mid-lane link-step failures (`FortschrittZeuge.olean`,
  `ScalarFloatHardwareForms.olean` missing while all module jobs passed)
  are apparatus flakiness in files the lane does not own, as reported.
- Axioms reproduced here: every theorem depends only on `[propext]`
  or `[propext, Quot.sound]` — a subset of the standard `gabbro_ziel`
  set. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `have _`,
  no `intro _` (token grep over the snapshot file matches only the
  27 `#print axioms` lines themselves).
- Full `./lean-bau` was NOT re-run in this clone: the review owns no
  source change and the tree is untouched, so a 483-job rebuild would
  measure the base, not the candidate. The single-file probe above is
  the honest check.

## Architecture review (manual-grade, not just Lean-green)

Manual provenance verified line-exact against the local snapshot
(`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
Intel SDM 325462-093US per `REFERENCES.json`):

- Opcode rows: AND `REX.W + 83 /4 ib` at txt 40726; OR `REX.W + 83 /1 ib`
  at txt 71678; XOR `REX.W + 83 /6 ib` at txt 138276. All three read
  `r/m64, imm8 (sign-extended)`.
- Flag identity: "The OF and CF flags are cleared; … AF … undefined" at
  txt 40766–40768 (AND), 71721–71722 (OR), 138319–138321 (XOR) — the
  same sentence in all three places, matching the proved
  `kompakt_{and,or,xor}_flaggen` (CF = OF = false, AF = none).
- Byte forms independently decoded by hand: REX.W = 72, opcode 83 = 131,
  ModRM C8 = mod 3 / reg 001 (/1 OR), E0 = mod 3 / reg 100 (/4 AND),
  F0 = mod 3 / reg 110 (/6 XOR), all rm = 000 (rax). The three REX.W
  pins and their decodes agree with these bytes exactly.
- Width/flag semantics: the flag lemmas are generic over the carried
  width and unfold to exactly the accepted step body
  (`schrittRegister … (intHwFlagsLogik b …) dst (mergeRegNarrow …)`),
  verified character-for-character against `stepIntHwImm`
  (`IntegerHardwareForms.lean` ll. 829–840). AF-undefined is modelled
  as `none`, not invented determinism. All four structural premises
  (`hok`, `hlen`, `hb`, `h`) plus `hstep` are used in each proof.
- Value path coherence (base, accepted, re-checked): encode takes the
  low byte (`imm.toNat % 256`), decode sign-extends (`imm8Erweitern`),
  step sign-extends the int32 (`immWort` = `sext`), and the compact
  form fires exactly under `immPasst8` (signed-byte fit) with the wide
  81 form otherwise — the three `kompakt_*_feuert` iff-lemmas mirror the
  accepted `kompakt_add_feuert` proof shape.
- Memory access order / pre-fault effects: the imm rows are
  register-direct (no memory access); the witness's memory change goes
  through the separate accepted pilot store (`store64 [rbx], rax` =
  `48 89 83 …`, ModRM 0x83 = mod 10 / reg rax / rm rbx, disp32 0,
  length 7 — consistent). TSO/LOCK: nothing to bridge for a
  register-only op; correctly untouched, correctly unclaimed.
- Negative coverage: truncated tails refuse (opcode-only, ModRM-only,
  lone REX); 128/256 refuse compact while 127/-128 take it; outside-i8
  takes the explicit 7-byte form (not silent narrowing). The joint
  theorem ties fetched decode, admission, byte step through the
  accepted dispatcher (`intHwImmByteschritt … = .weiter s1`),
  read-back `0xF1`, start-cell `0`, and the wide form at 256.
- Witness (`CompactImm8Logic_verbindung_zeuge`): both step hypotheses
  instantiated jointly; rax `0xF0 → 0xF1`, data cell `0 → 0xF1` —
  non-degenerate with a real memory-changing reached run. No
  desired-simulation premise, no guarantee weakened, no fake closure:
  the CUTS block explicitly leaves TSO/W/GX, faults beyond refusal,
  LOCK, source correspondence, image coverage, cost, entry/ABI and the
  optimiser chain open, and names memory-operand 83 rows, ADC/SBB and
  b8/b16 rows as refused-by-absence.

## Nits (not verdict-changing, offered as follow-ups)

1. In `CompactImm8Logic_verbindung` the local `have`s `hlen` and `hb`
   (and transitively `hok4`/`hpass` except via `hlen`) are dead after
   derivation — harmless but worth deleting.
2. The header/CUTS phrase "SF/ZF/PF from the width-correct result" is
   inherited from accepted `intHwFlagsLogik`/`logikFlags`, not proved
   by a new equation here; the proved conjuncts are CF/OF/AF only.
   The attribution is correct, the wording could mark the inheritance.
3. `pin_and32_kompakt` pins a bare-REX (`0x40`) 4-byte form — faithful
   to the accepted encoder (`natByte (64 + regHigh dst)`) and round-trip
   proved, but the REX-less 3-byte form assemblers emit is a base-module
   coverage question, not this candidate's defect.

## Claim boundary (bounded acceptance)

Accepted: per-width logic-flag identity (CF/OF/AF) for the REX.W 83
/1 /4 /6 imm8 rows plus one b32 row, pinned compact bytes/decodes,
compact-vs-wide choice with outside-i8 explicitness, truncated-tail
refusals, and the 11-conjunct joint connection with its inhabited
memory-changing witness — all through reused accepted vocabulary.
NOT accepted (not claimed, not proved): silicon correspondence beyond
the cited rows, TSO/W/GX bridge, fault delivery, feature/control
gates, async effects, SIMD/entry/profile forms, optimiser chain.
