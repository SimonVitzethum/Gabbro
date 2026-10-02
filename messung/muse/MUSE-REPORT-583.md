# MUSE-REPORT-583: Independent exact-candidate connection review of 565

Lane 583, clone `/home/simon/Dokumente/gabbro-muse/a583`, branch `muse/583` (verified).
Owns only this report. No source file was changed by this lane.

CANDIDATE: 565 2c935821c0b2b3c0bbd418f9edab41ccca9919a0
VERDICT: ACCEPT

## Re-review of the report-only follow-up (supersedes the `b62e3019` review)

New pinned commit `2c935821` ("integration-gate failure analysis, no
module change") touches only `MUSE-REPORT-565.md`: it analyses an
integration-gate exit-134 (`failed to create thread`) as the known
apparatus flake and deliberately makes no module change. The Lean
module in this snapshot is structurally identical to the accepted
`b62e3019` version (same 710 lines, same declaration names and line
numbers, `fpXmmCode`/`fpXmmCode_lt` rename in place, 40 axiom
prints). The previous ACCEPT verdict's basis is therefore unchanged;
this section records the fresh independent verification of the new
pinned snapshot. (Cosmetic: the author report still names `b62e3019`
as "the changed commit" in one sentence; the snapshot of record and
the reviewed files are `2c935821`.)

## Re-review after repair (supersedes the previous REPAIR verdict)

Previous verdict (on `3fbe0b8f`): REPAIR -- the candidate redefined
`xmmCode`/`xmmCode_lt` in `Gabbro.Grammatik.X86`, colliding with merged
`VectorCodec.lean` (lane 597); full `lean-bau` failed at the umbrella.
The author applied exactly the recommended minimal repair (rename to
`fpXmmCode`/`fpXmmCode_lt`, `codeXmmLow_xmmCode` keeps its non-colliding
name) in the new pinned snapshot `b62e3019`. This report re-reviews
that snapshot from scratch; the old verdict is stale and replaced.

## What was reviewed (new snapshot)

Exact candidate 565 (base `8596f83e`, files `MUSE-REPORT-565.md`,
`grammatik/Grammatik.lean` one import line,
`grammatik/Grammatik/X86/ScalarFloatCodec.lean` 710 lines) against its
owner task (lane 565: scalar SSE2 bytes to accepted FP execution, MOVSD
register/load/store + ADDSD register) and against current master
(`26c58bd4`). Method: read the full candidate file, checked every
producer name against current `ScalarFloat`/`Codec`/`Byteschritt`/
`Speicher` sources, hand-verified all four byte shapes against the Intel
SDM opcode map, applied the candidate byte-identically in this clone
(`diff` confirmed identical) and reproduced through the queued wrappers.

## What the candidate gets right (accepted bounded claim)

The connection itself is sound and genuinely productive, not decorative:

- Decoder takes only `List Byte`; `fpByteschritt` takes only the state.
  No caller-supplied `FpDecodiert` ever becomes fetched evidence. The
  `hf : fpFetchDekodiert t = some (d, rest)` premises are fetched facts,
  not forged inputs.
- Byte shapes are correct: F2/0F with opcodes 16/17/88, ModRM mod=11
  reg=destination (10/58) and reg=source for the store (11), mod=10
  disp32 with the pilot SIB rule, lengths 4/8/9. Hand-checked the
  witness bytes `F2 0F 11 80 00 00 00 00` through `fpDecodeRest`.
- All execution facts (`fpByteschritt_addsdRR_rechnet/_klasse/_hoch`,
  `movsdRR_flags/_fp/_gpr`) are derived from the accepted `fpSchritt`
  equations plus existing lemmas; nothing is redefined. Every premise
  is used; no conclusion restates a premise; no `Prop`-typed premises.
- Joint witness `fpCodec_bytes_zeuge` is non-degenerate: actual store
  bytes at RIP 4096, reached `fpByteschritt` stores `+inf` at 8192,
  word reads back, one memory byte observably changed, profile
  admitted, planted refusals beside it in section 4.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. All 40 proved
  items print only standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`, or none). Single-file `./lean-probe` is green
  (reproduced 3x; exit-134 thread flakes on other attempts are the
  known apparatus issue under concurrent load, retried to verdict).
- CUTS block is honest: REX/high registers, memory arithmetic,
  UCOMISD, NaN payloads, hardware correspondence and source bridge
  are marked open. The report's "no SSE byte evidence in repo to pin
  against" statement is accurate. (Minor: the first author report
  said 39 theorems; the file proves 40 items with axiom prints. The
  repair note corrects this; one stale "39" remains in the report
  body -- cosmetic only.)

## Why REPAIR: exact candidate breaks the full build on current master

(Resolved in `b62e3019`; kept here as audit of the previous finding.)
`grammatik/Grammatik/X86/VectorCodec.lean` (lane 597, merged after the
candidate's base) defines `xmmCode` and `xmmCode_lt` in the same
namespace `Gabbro.Grammatik.X86`. The old candidate defined both names
again (textually identical definitions). Full `./lean-bau` with the old
candidate applied failed at the umbrella (reproduced, exit 1):

```
error: Grammatik.lean:44:0: import Grammatik.X86.ScalarFloatCodec
  failed, environment already contains
  'Gabbro.Grammatik.X86.xmmCode.match_1' from Grammatik.X86.VectorCodec
```

The candidate built green only because it was branched before 597 and
single-file probes never elaborate sibling modules. This is an
integration conflict, not a proof defect.

## Concrete minimal repair (for a 565 continuation)

(Was required; author applied it in `b62e3019`; verified below.)
In `ScalarFloatCodec.lean`, rename the two colliding declarations and
their uses, nothing else:

- `def xmmCode` -> `def fpXmmCode` (definition, ~lines 27-31),
- `theorem xmmCode_lt` -> `theorem fpXmmCode_lt` (line 45),
- update uses: `codeXmmLow_xmmCode` statement+proof, the four
  encoders, the four round-trip premises+proofs, and the two
  `#print axioms` lines (~12 touch points, all mechanical).
- No new import needed; no statement logic changes; round-trip
  `< 8` premises keep their exact meaning.

Alternative (not recommended): delete both and `import
Grammatik.X86.VectorCodec` to reuse its identical definitions. This
removes duplication but couples lane 565 to lane 597's module; the
rename keeps the candidate self-contained.

After the rename, the continuation must show full `./lean-bau` green
(457 jobs on current master) plus `#print axioms gabbro_ziel`
unchanged. The repaired module then lands as: decoder/round-trips
(`fpDecode`, `fpRoundtrip_*`), fetch admission
(`fpFetchDekodiert_erfolg`), byte execution (`fpByteschritt_schritt`
family), joint witness (`fpCodec_bytes_zeuge`).

## Producer/consumer interface (stable, for the coordinator)

Producers (unchanged by repair): `fpDecode`, the four `fpRoundtrip_*`,
`fpFetchDekodiert_erfolg`, `fpByteschritt_schritt`,
`fpByteschritt_addsdRR_klasse` (via `fpRechne_klasse`). Consumers:
validator-skeleton admission of the four forms, TSO bridge
per-access footprints, source bridge via `fpRechne_klasse`.
Measurable next integration: wire `fpFetchDekodiert` shapes into
`ValidatorSkeleton` admission, or extend one more form (memory ADDSD
or UCOMISD) through the same fetch/execute/witness chain.

## Last build results (new snapshot `2c935821`, master `26c58bd4`)

- PATCH/file consistency: the `PATCH.diff` module hunk (710 `+` lines)
  is byte-identical to the extracted candidate file; the
  `Grammatik.lean` hunk is the single additive import. Merger note:
  the hunk context anchors the import after `ContractSites` (old base
  layout); current master has grown past that point, so the import
  lands at the new tail at merge -- mechanical, not a defect.
- Name-collision scan over every `grammatik/Grammatik/X86/*.lean`
  module vs the new candidate: NONE.
- Forbidden-tactic scan of the new file: clean (only comment-word
  matches; header and CUTS unchanged, no new claims).
- `./lean-probe grammatik/Grammatik/X86/ScalarFloatCodec.lean` with
  the new candidate applied byte-identically: `0 error(s), exit 0`;
  40/40 axiom lines within the standard set
  (`propext`/`Classical.choice`/`Quot.sound`/none).
- `./lean-bau` with the new candidate applied: `Build completed
  successfully (457 jobs)`, first attempt, no flake this run.
- `#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel`:
  exactly `[propext, Classical.choice, Quot.sound]`.
- The author's flake analysis (exit-134 is apparatus load, pure-Lean
  module spawns no threads, no proof restructuring to chase it) is
  accurate and matches this lane's own measurements across all three
  review rounds. No proof change was needed and none was made.
- Working tree was reverted afterwards; it is clean except this
  report.

## Open / not claimed

No hardware correspondence (stated contract only); no TSO/GX, validator
or source-bridge consumption; REX/high registers and further forms
open per the file CUTS. Nothing in the owner task text was found to
be wrong; the task's byte-connection requirement is met by the
pinned candidate.
