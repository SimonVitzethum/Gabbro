# MUSE-REPORT-290: Packed integer lane model for future SIMD

Lane 290, owner files only: `grammatik/Grammatik/X86/Vektor.lean` (new, 651 lines),
one additive umbrella import (`import Grammatik.X86.Vektor` at the end of
`grammatik/Grammatik.lean`), this report. No Rust, no canonical-file edits
beyond the import, no new diagnostic/gift/example/CLI/MARKE numbers.

## What was built

Packed 128-bit integer words (`Vektor := BitVec 128`) with 16/8/4/2 lanes
of 8/16/32/64 bits (`laneCount`), over the SAME canonical helpers:
`Wort`/`Breite`/`addrOff` (Typen), `addB`/`subB`/`xorB`/`trunc`/`maske`
(Wort), `read64`/`write64` and their frame/read-back lemmas (Speicher).
Lanes pack Horner-style (`vecVal`); lane access is `laneNat`/`laneGet`.

Definitions: `Vektor`, `laneCount`, `vecVal`, `laneNat`, `laneGet`, `vecMk`,
`vecAdd`, `vecSub`, `vecXor`, `vecAnd`, `vecOr`, `vLo`, `vHi`, `vecJoin`,
`vecHiAddr`, `OhneUmbruch16`, `vecWrite`, `vecRead`, `vecZeugenSpeicher`,
`vecZeugenVektor`, `vecZeugenM1`, `vecZeugenM2`, `simdFreigabe`.

Theorems (all `#print axioms` within propext/Classical.choice/Quot.sound):
- Packing: `vecVal_succ`, `vecVal_proj` (Horner projection induction),
  `vecVal_lt` (packed value fits), `laneGet_mk`, `laneCount_bits`,
  `laneCount_pos`, `laneMod_pos`, `laneMod_gt_one`, `laneMod_dvd`,
  `laneMod_le`, `laneNat_lt`, `laneNat_lt64`, `laneGet_toNat`.
- Canonical bridge: `mask_and_eq_mod`, `trunc_nat`, `addB_nat`,
  `subB_nat`, `xorB_nat`, `trunc_and_nat`, `trunc_or_nat`. Note: the
  canonical file provides only `xorB`, so and/or bridge through `trunc`
  directly (same mask pattern); a future canonical `andB`/`orB` subsumes it.
- Per-lane correctness, generic over operand values and lane index:
  `laneNat_add/sub/xor/and/or`, `laneGet_add/sub/xor/and/or`, plus
  no-carry/no-borrow `vecAdd_allein`, `vecSub_allein`.
- Memory carriage (two ordered canonical chunks, low half first):
  `vecJoin_split`, `addrOff_nat`, `Disjunkt_symm`, `vecChunks_disjoint`
  (needs explicit `OhneUmbruch16`: 16 bytes no-wrap), `vecWrite_perm`,
  `vecWrite_verweigert_lo/hi`, `vecRead_nach_write`, `vecWrite_rahmen`,
  `vecWrite_teilt` (mixed intermediate: low half new, high half old --
  no vector atomicity is claimed, and lane disjointness is never used to
  infer atomicity or reorder shared operations).
- Witnesses (all `decide`, nonzero/real): `vec_ueberlauf_ohne_uebertrag_b8`
  (lane0 `0xFF+1=0`, lane1 `5+7=12`), `..._b64`, `vec_borg_ohne_uebertrag_b8`
  (`0-1=0xFF`, neighbour `5-2=3`), `vec_xor_spur_b8`, and
  `vecWrite_read_zeuge` (nonzero vector, two chunk writes, low-half
  read-back, full read-back, changed base byte).
- Refusal: `simdFreigabe = false`, `simd_gesperrt`. SIMD optimisation
  admission stays refused until source correspondence, fault order,
  visibility, tearing, FP control status, concurrent observations and
  budget transfer are proved. No FP SIMD modelled. No XMM register file,
  no `Befehl` edits.

## Verification

- `./lean-probe grammatik/Grammatik/X86/Vektor.lean`: 0 errors; every main
  theorem within the standard axiom triple (several depend on no axioms).
- `./lean-bau` (full project): exit 0, 0 error lines, 369 jobs
  (`✔ [368/369] Built Grammatik`, `Build completed successfully (369 jobs)`).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (checked by grep; the
  only matches are the words "admitted" and `#print axioms` lines).
- No theorem has a premise of type `Prop` itself; every premise is used.
  No source-syntax (`Vertrag`/`Stmt`/...) premises occur, and the task
  names no `ZEUGE:` targets, so rule 13 requires no `_zeuge` companions;
  target helpers carry real operand/memory probes (`decide` witnesses plus
  the memory-changing `vecWrite_read_zeuge`).

## Open / cuts (also in the file CUTS block)

Source correspondence, per-lane fault order, visibility/tearing against
the TSO bridge, FP lanes, call-log preservation, budget transfer,
decoder/ABI/image validation, progress interaction: all open, owned by
later lanes. The `vecSub` lane representative (`2^64 - y + x`) matches the
canonical `BitVec.toNat_sub` form by construction.

## Notes on the task

Nothing in the task seemed wrong. Two implementation findings worth keeping:
`{ s with f := <newline> value }` does not parse for structure updates
(single line as in `Speicher.lean` works), and `interval_cases` is
unavailable (no mathlib) -- the outside-footprint fact is proved by
`toNat` injectivity instead. `Nat` `^^^` and `.xor` elaborate to different
heads, so `vecXor` uses `^^^` throughout.
