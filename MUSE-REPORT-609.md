# MUSE-REPORT-609: Independent overnight closure review of 597

## Candidate

CANDIDATE: 597 11b6e9da059272d6b85568388dddf13e9e0e634b

VERDICT: ACCEPT

Accepted scope (bounded): `grammatik/Grammatik/X86/VectorCodec.lean` (new, 695
lines) plus one additive umbrella import in `grammatik/Grammatik.lean`, as a
byte-to-shared-state connection for exactly two packed-integer register forms
(PXOR `66 0F EF /r`, PADDQ `66 0F D4 /r`, canonical 5-byte REX form) to the
actual accepted `Vektor.lean` lane functions and the shared `ScalarFloat.lean`
`FpZustand`, with a pilot-first combined dispatch and a byte-backed joint
witness. Not accepted as, and not claimed as: silicon correspondence, lane-575
integration (fit is by shape only), source linkage, or any TSO/fault/budget/
progress/image result.

## What was checked

- Snapshot: `.tmp/review/SNAPSHOT.json` names author 597, the pinned HEAD
  above, base `0044c258`, files `MUSE-REPORT-597.md`,
  `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/VectorCodec.lean`.
  `PATCH.diff` touches exactly these three files; the `Grammatik.lean` hunk
  is a single additive import. No checker, Spec, goal, or friend-reserved
  optimiser file is touched.
- Full read of the candidate `VectorCodec.lean` (all 695 lines) against the
  owner task and against this clone's accepted X86 modules.
- Reuse is real, not redefinition: `vecXor`/`vecAdd`/`laneGet_xor`/
  `laneGet_add`/`laneGet_toNat`/`addB_nat` exist in `Vektor.lean`;
  `XmmReg`/`XmmDatei`/`xmmSet`/`xmmSet_gleich`/`xmmSet_fremd`/`xmmTief`/
  `FpZustand`/`fpSchritt`/`fpSchritt_movsdSpeichere_erfolg`/
  `fpEintritt_reset` exist in `ScalarFloat.lean`; `decode`/`Decodiert`/
  `laengeOk`/`modrmReg`/`natByte`/`byteNat` in `Codec.lean`;
  `HwProfil`/`BereitProfil`/`hat`/`bereit`/`merkmalZugelassen`/
  `PerfMerkmal.paketInt128` in `FeatureProfile.lean`;
  `writeBytesN_hit`/`addrOff_null` in `Speicher.lean`;
  `vecZeugenSpeicher` (zeroed bytes) in `Vektor.lean`. `stepVector` matches
  only the two new forms and writes the accepted lane words; the only
  memory change in the witness goes through the reused `fpSchritt` MOVSD
  store. Pilot/FP forms are never re-evaluated.
- Decoder parses bytes, never encode-equality: REX select, then `66`,
  `0F`, opcode, register-direct ModRM. Round trip (`roundtrip_pxor`,
  `roundtrip_paddq`, `roundtripVector`) is decode-inverts-encode over any
  suffix with the decoded length equal to the consumed prefix length.
  REX coverage is complete: `xmmHigh` is 0 or 1, so `vectorRex` takes only
  values 64/65/68/69, and `decodeVector` handles exactly those four.
- Pilot disjointness is computational, not asserted:
  `vector_pilot_verweigert` (by cases + rfl over every covered row and any
  suffix); `decodeComboV` tries pilot first and the vector arm only where
  the pilot refuses, with the three no-shadowing lemmas proved by rewrite.
  Planted refusals present: bare-`0F` (never re-decides a pilot conditional
  jump), memory ModRM (mod != 3), truncated prefix. Profile and length
  refusals (`stepVector_laenge_verweigert`, `stepVector_profil_verweigert`)
  are proved equations, and `vecEintritt` is correctly labelled a validator
  refusal agreeing with `paketInt128` admission (`vecEintritt_merkmal`).
- Witness is joint and non-degenerate: pinned bytes decode
  (`vecZeuge_decode`, `vecZeuge_laenge`: 5 + 0 = 5), the decoded PXOR
  reaches `vecZeugeT1` (`vecZeuge_schritt`), and the existing MOVSD store
  writes the xor low half `0xF0` to address 0, observably changing a byte
  against zeroed `vecZeugenSpeicher` (`vectorCodec_zeuge`). No `_zeuge`
  companion is required: no theorem quantifies over program syntax and the
  owner task names no `ZEUGE:` target.
- Premise use: every premise of every checked theorem is used in its proof
  (no `intro _`, no `have _ :=` in the file); no premise has type `Prop`
  itself; no conclusion restates a premise; no contract is quantified away;
  nothing unable to change memory is called a semantics. `grep` finds no
  `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` outside prose comments.
- Axioms per `BUILD-EVIDENCE.json` final probe: every printed theorem
  depends only on subsets of `[propext, Classical.choice, Quot.sound]` —
  the standard goal set.
- CUTS are precise and match the file: two register forms only; all wider
  rows (PADDW/PADDD/PSUBx/PAND/POR, memory forms, MOVDQA/MOVDQU/PSHUFD,
  packed FP) reported unsupported, not connected; no vector atomicity (the
  `vecWrite_teilt` tearing result is cited, not contradicted); no silicon,
  fault, TSO, source, budget, progress or image claim; `simdFreigabe`
  stays `false`.
- Build evidence shows genuine iterative development (intermediate red
  probes with `sorryAx` and rewrite failures, each repaired) ending in
  `lean-probe` 0 errors and `lean-bau` green at 440 jobs.

## Limitations of this review

- The exact candidate objects (HEAD `11b6e9da`, base `0044c258`) are absent
  from this clone (`bad object`), so no independent rebuild of the exact
  candidate was possible here; verification is static inspection plus the
  recorded probe/build sequence, not a fresh local build. A full `lean-bau`
  rerun was also deliberately avoided to not contend with live lanes on the
  shared Lean slot.
- The lane-575 consumer fit is by shape (`VectorDec` mirrors
  `NarrowDec`/`MulDivDecodiert`, pilot-first sum dispatch, shared
  `FpZustand`); lane 575 was not present in the author's clone, which the
  author reports honestly rather than claiming an integration.

## Minimal repair locations

None required for ACCEPT. If a follow-up hardens the result, the natural
seams are: `decodeVector` (new REX/escape arms), `stepVector` (new
`VectorOp` arms with their frames), and a PADDQ analogue of
`vectorCodec_zeuge` — all additive, none touching the accepted rows.

## Useful next independent tasks (not started, no filler)

- PADDQ decoded-execution witness through the same MOVSD joint (mirrors
  `vectorCodec_zeuge`).
- Lane-575 integration consuming `decodeComboV`/`stepVector` once 575 is
  accepted.
- MOVDQA/MOVDQU load/store rows with explicit tearing cuts (needs the
  per-access TSO bridge table, still open).

## Last build result

No build run from this review (report-only lane; exact candidate objects
absent locally; live lanes hold the build slots). Evidence relied upon:
`BUILD-EVIDENCE.json` final entries — `lean-probe` 0 errors and `lean-bau`
`Build completed successfully (440 jobs)`.
