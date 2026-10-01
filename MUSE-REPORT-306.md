# MUSE-REPORT-306: Independent review of candidate 290

Lane 306, review only. Model: opencode-go/muse-spark-1.3-contributor.
No delegation, no Rust work, no source/Spec/goal edits, no network.
Owned file: this report only. Candidate files inspected at their
committed snapshot copies under `.tmp/review/`; nothing copied into the tree.

## Scope and snapshot

- Reviewed: author 290, pinned HEAD `b10be43bd287629305aa18936b47c72b4a883c44`
  (base `f49581505cda367b97d4f3d89faa1b2f33413497`, clean), per `SNAPSHOT.json`.
- Files in snapshot: `MUSE-REPORT-290.md`, `grammatik/Grammatik.lean`
  (one additive line `import Grammatik.X86.Vektor`), new
  `grammatik/Grammatik/X86/Vektor.lean` (651 lines, confirmed by `wc -l`).
- `PATCH.diff` confirms ownership: only those three paths, no Rust,
  no canonical-file edits beyond the umbrella import, no new
  diagnostic/gift/example/CLI/MARKE numbers.
- Preconditions: `pwd` / toplevel `/home/simon/Dokumente/gabbro-muse/a306`,
  branch `muse/306` — matched. This clone has no `Vektor.lean` in-tree,
  so the review ran against the snapshot copy only.
- Note: `LEAN-ZUERST.md` / `WELLE-A.md` named in the owner task are absent
  from this clone; AGENTS.md (system prompt) and the owner task itself were read.

## Method

- Read the full snapshot `Vektor.lean` (all definitions, statements, proofs),
  the owner task, the author report, `PATCH.diff`, and `BUILD-EVIDENCE.json`.
- Verified canonical bridge targets exist in this clone: `Wort`/`Breite`
  (`Typen.lean`), `maske`/`trunc`/`addB`/`subB`/`xorB` (`Wort.lean`,
  `subB := trunc b (x - y)` etc.), `addrOff`/`read64`/`write64`/`Disjunkt`/
  `lesbar8`/`schreibbar8`/`writeBytes(N)`/`wortByte` and the lemmas
  `write64_erhaelt_berechtigungen`, `write64_verweigert`,
  `lesbar8_nach_schreiben`, `read64_nach_write64`, `write64_rahmen`,
  `read64_rahmen`, `writeBytesN_hit/miss`, `addrOff_null` (`Speicher.lean`).
- Ran `./lean-probe .tmp/review/author-290/grammatik/Grammatik/X86/Vektor.lean`
  (queued wrapper only): first line `== 0 error(s)`, full output ends with
  per-theorem `#print axioms` lines, all within `[propext, Classical.choice,
  Quot.sound]` or subsets (several axiom-free). Matches the claimed evidence.
- Grep checks on the snapshot: no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe` outside comments (`admitted` in prose) and `#print axioms` lines;
  no `intro _` / `have _ :=`; no theorem with a premise of type `Prop` itself;
  `Befehl`/XMM occur only in comments stating they are NOT created/touched.

## Findings per review axis

- Definitions/proofs inspected, not just statements: Horner packing
  (`vecVal`, `vecVal_succ` rfl, `vecVal_lt`, `vecVal_proj`), lane access
  (`laneNat` div/mod projection, `laneGet` zero-extended word, `laneGet_mk`
  with the `< 2^128` bound via `laneCount_bits`), per-lane ops and their
  modular statements, canonical bridge (`mask_and_eq_mod`, `trunc_nat` by
  four width cases, `addB/subB/xorB_nat`, `trunc_and/or_nat`), `laneGet_*`
  correspondence through `BitVec.eq_of_toNat_eq`, `vecAdd/Sub_allein`
  independence, memory carriage (`vLo`/`vHi` split, `vecJoin` reassembly,
  `vecJoin_split`, `vecHiAddr = addrOff a 8`, `OhneUmbruch16`, `addrOff_nat`,
  `vecChunks_disjoint`, ordered two-`write64` store, two-`read64` load,
  permission preservation, both refusal directions, read-after-write with
  frame, outside-footprint frame, mixed-intermediate `vecWrite_teilt`).
- Witnesses real and state-changing: `decide` boundary probes for add
  (b8 lane0 `0xFF+1=0` with lane1 `5+7=12`; b64 wrap with `3+4=7`), sub
  (`0-1=0xFF`, neighbour `5-2=3`), xor (`0xAA^^^0x55=0xFF`, `240^^^240=0`),
  plus `vecWrite_read_zeuge`: existential over nonzero vector
  `0x100F...0201`, two ordered chunk writes at address 0, low-half and full
  read-back, and a proved changed base byte (low byte `0x01` vs zero).
- Boundaries honest: `vecWrite_teilt` states the observably mixed intermediate
  and claims no vector atomicity; lane disjointness is never used to infer
  atomicity or reordering; `simdFreigabe = false` with `simd_gesperrt`;
  CUTS block lists source correspondence, per-lane fault order,
  visibility/tearing vs the TSO bridge, FP lanes, call-log preservation,
  budget transfer, progress, decoder/ABI/image validation as NOT proved.
  A green build is not presented as a hardware/source theorem.
- Genericity: all lane/memory theorems quantify generically over width,
  operand values and lane index; no program/example-specific rule, no
  inferred `ensures`, no weakening. `vecSub`'s `2^64 - y + x` representative
  is justified by `laneMod_dvd` (`2^w ∣ 2^64`) and matches canonical
  `BitVec.toNat_sub` through the same `Nat.mod_mod_of_dvd` step used for
  `subB_nat` — checked, not assumed.
- Premise use: every hypothesis is consumed (spot-checked `vecVal_lt`,
  `vecVal_proj`, `laneGet_mk`, `vecWrite_perm`, `vecRead_nach_write`,
  `vecWrite_rahmen`, `vecWrite_teilt`, `addrOff_nat`, `vecChunks_disjoint`,
  `Disjunkt_symm`); refusal lemmas state refusal in the correct state
  (high-chunk refusal in post-low-write `m1`, not pre-state).
- Report-vs-code cross-check: every claimed definition/theorem name exists
  in the snapshot; counts and the 369-job green `lean-bau` / 0-error
  `lean-probe` claims are consistent with `BUILD-EVIDENCE.json` and my
  independent probe. Intermediate red probes in the evidence log are normal
  development steps ending green; final state is what is judged.
- Rule 13: no premises quantify over program syntax and the owner task names
  no `ZEUGE:` targets, so no `_zeuge` companions are required; operand and
  memory probes are present as the task demands for target helpers.

## Defects

None material. No required changes.

## Verdict

The delivered bounded claim — a packed-128 integer lane data/operation
foundation over the canonical word/memory vocabulary with per-lane modular
correctness, no-carry/no-borrow independence, two-chunk carriage with refusal
/ read-back / frame / explicit tearing exposure, boundary and memory-changing
witnesses, and SIMD admission still refused — is true as stated, with needed
checks green, proof/witness gates holding, and cuts honestly labelled. This
does not certify the whole compiler or any binary validation.

CANDIDATE: 290 b10be43bd287629305aa18936b47c72b4a883c44
VERDICT: ACCEPT
