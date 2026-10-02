# MUSE-REPORT-597: Selected SSE2 vector bytes to canonical XMM execution

## What was done

New file `grammatik/Grammatik/X86/VectorCodec.lean` (plus one additive
umbrella import in `grammatik/Grammatik.lean`) connects the accepted
packed-integer Vektor subset (PXOR, PADDQ register forms) to actual
canonical SSE2 byte decode and the same ScalarFloat XMM register state.

- **Codes (§0):** `xmmCode`/`codeXmm` (xmm0=0..xmm15=15),
  `codeXmm_xmmCode`, `xmmCode_lt`, `xmmHigh`/`xmmLow`.
- **Forms + encoding (§1):** `VectorOp` (`pxorRR`, `paddqRR`),
  `vectorSecond` (EF=239 / D4=212), `vectorRex` (REX `64+4R+B`),
  `encodeVector` (5 bytes: REX `66` `0F` opcode ModRM reg=dst r/m=src),
  `encodeVector_len`, `vectorLen_ok`.
- **Decoder (§2):** `VectorDec` (op + checked 1..15 length, same shape as
  `NarrowDec`/`MulDivDecodiert` for the lane-575 joint),
  `decodeVectorModrm`/`decodeVectorNach`/`decodeVector` (parse bytes,
  never encode-equality), `roundtrip_pxor`, `roundtrip_paddq`,
  `roundtripVector` (decode inverts encode over any suffix, decoded
  length is the consumed prefix length).
- **Pilot disjointness (§3):** `vector_pilot_verweigert` (pilot `decode`
  refuses every covered row over any suffix: second byte 102 matches no
  pilot REX/push/pop arm), `decodeComboV` + `decodeComboV_kanonisch` /
  `_erweitert` / `_nichts` (pilot-first dispatch, no shadowing),
  planted refusals `vector_nichts_bare0F` (bare `0F` never re-decides a
  pilot conditional jump), `vector_nichts_speicher_modrm` (mod!=3),
  `vector_nichts_kurz` (truncated prefix).
- **Execution (§4):** `vecEintritt` (OS vector state, validator refusal),
  `vecEintritt_merkmal` (agrees with finite `paketInt128` admission where
  silicon support holds), `stepVector` on the SAME `FpZustand`
  (PXOR writes accepted `vecXor .b64`, PADDQ accepted `vecAdd .b64`;
  pilot/FP forms never re-evaluated), step equations `stepVector_pxor` /
  `_paddq`, refusals `stepVector_laenge_verweigert` /
  `stepVector_profil_verweigert`.
- **Frames (§5):** `stepVector_rip`, flags/memory/GPR preservation,
  other-XMM preservation (`_fremd` via `xmmSet_fremd`), per-lane
  correctness `stepVector_pxor_spur` (via accepted `laneGet_xor`) and
  `stepVector_paddq_spur` (via accepted `laneGet_add`), and explicit
  overflow behaviour `stepVector_paddq_modular` (modular at 2^64, no
  inter-lane carry, no float reassociation).
- **Witness (§6):** pinned bytes decode (`vecZeuge_decode`,
  `vecZeuge_laenge`: 5 + 0 = 5), decoded PXOR reaches `vecZeugeT1`
  (`vecZeuge_schritt`), existing MOVSD store carries the xor low half
  (`0xFF ^^^ 0x0F = 0xF0`, `vecZeuge_xor_tief`) to address 0 and changes
  a byte (`vecZeuge_speichere`, `vectorCodec_zeuge` with memory
  `m2.bytes 0 != initial`). No new evaluator for MOVSD: `fpSchritt` is
  reused through `fpSchritt_movsdSpeichere_erfolg`.

## Evidence

- `./lean-probe grammatik/Grammatik/X86/VectorCodec.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (440 jobs).`
- `#print axioms`: every theorem depends only on subsets of
  `[propext, Classical.choice, Quot.sound]` (the heavier two come from
  the accepted `Vektor.lean` lane facts); no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` anywhere in the file.
- No existing file was changed except the additive umbrella import;
  no checker/Spec/goal/optimiser file touched.

## What remains open (see CUTS in the file)

Only PXOR/PADDQ register forms are connected. PADDW/PADDD/PSUBx/
PAND/POR, all memory vector forms, MOVDQA/MOVDQU/PSHUFD and every FP
packed form have no decoder arm and no step (refused by construction).
No vector atomicity, no silicon/fault/TSO/source/budget/progress/image
claim; `simdFreigabe` stays `false`.

## Producer/consumer interfaces (for lane 575 and followers)

- Producer: `decodeVector : List Byte -> Option (VectorDec x List Byte)`,
  `VectorDec` (.op/.laenge), `decodeComboV` (pilot-first,
  `Decodiert (+) VectorDec`), `stepVector : VectorDec -> FpZustand ->
  BereitProfil -> Option FpZustand`, `vectorCodec_zeuge` (joint).
- Consumer fit: `VectorDec` mirrors `NarrowDec`/`MulDivDecodiert`
  (op + stated length + suffix), and `decodeComboV` mirrors
  `decodeCombo`, so the unified lane-575 path can try `decode` first
  and `decodeVector` where it refuses, then dispatch on `.inr` to
  `stepVector` with the same `FpZustand` embedding.
- Useful next tasks: (a) PADDQ decoded-execution witness through the
  same MOVSD joint (mirrors `vectorCodec_zeuge`); (b) lane-575
  integration consuming `decodeComboV`/`stepVector`; (c) MOVDQA/MOVDQU
  load/store rows with the two-chunk `vecRead`/`vecWrite` carriage and
  explicit tearing cuts (needs the per-access TSO bridge table, still
  open). None started here; no filler.

## Notes on the task

- "Implement only ISA rows whose precise semantics have evidence in
  repository selected profile": PXOR/PADDQ register semantics are the
  accepted `vecXor`/`vecAdd` at `.b64` plus the `paketInt128` profile
  tier; encodings are the canonical `66 0F EF/D4 /r` rows. Wider rows
  are reported unsupported in CUTS, not implemented.
- "Admitted typed-register dispatch interface should fit
  ExtendedExecution575": lane 575 was not present in this clone, so the
  fit is by shape (decoded form + length + suffix, pilot-first sum
  dispatch, shared `FpZustand`), documented above for its owner.
