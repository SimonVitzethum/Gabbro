# MUSE-REPORT-580: Independent exact-candidate connection review of 562

## Scope

Review of lane 562 (narrow operations byte decoder and execution connection)
as pinned in `.tmp/review/SNAPSHOT.json` against its task in `lanes/562.md`.
Inspected artefacts: `.tmp/review/author-562/MUSE-REPORT-562.md`,
`.tmp/review/author-562/BUILD-EVIDENCE.json`,
`.tmp/review/author-562/PATCH.diff`,
`.tmp/review/author-562/grammatik/Grammatik/X86/NarrowCodec.lean`
(959 lines). Producer modules resolved in this clone
(`grammatik/Grammatik/X86/`): `NarrowOps.lean`, `Codec.lean`,
`DecodingCoverage.lean`, `Ausfuehrung.lean`. No files outside
`MUSE-REPORT-580.md` were touched by this review.

## What the candidate does

New file `grammatik/Grammatik/X86/NarrowCodec.lean` plus one additive
umbrella import in `grammatik/Grammatik.lean`. Exactly four narrow rows are
covered: `mov32rr` (opcode 89, mod=3, no REX.W), `movzx8`/`movsx8`
(0F B6/BE, mod=3, no REX.W), `store32` (opcode 89, mod=2 + disp32 [+SIB],
no REX.W). Every form carries a canonical REX byte with W=0/X=0
(values 40/41/44/45). Pilot `decode`/`schritt` are untouched; dispatch is
canonical-first via `decodeCombo`, mirroring `decodeErw`. Execution
(`stepNarrow`) reuses the accepted `NarrowOps` evaluators (`moveNarrow`,
`extendNarrow`, `mergeRegNarrow`, `storeNarrow`) on the same `Zustand`.
No hardware correspondence is claimed (canonical-subset self-consistency).

## Checks performed

- **Forbidden tactics:** `grep -E "sorry|admit|native_decide|unsafe|^axiom"`
  over the candidate file returns nothing (exit 1). The 35 `axiom`
  substring hits are all required `#print axioms` lines. Clean.
- **Producer resolution:** all reused names exist with matching roles in
  this clone: `moveNarrow`/`extendNarrow`/`mergeRegNarrow`/`storeNarrow`
  (`NarrowOps.lean`), `storeNarrow_success`/`storeNarrow_frame_b32`,
  `parseLe32_suffix` (`DecodingCoverage.lean`), `decode` (`Codec.lean`),
  `laengeOk`/`ripNach`/`effAddr`/`regSet`/`regSet_gleich`
  (`Ausfuehrung.lean`). `mergeRegNarrow .b32` clears the upper 32 bits by
  construction, so the `movsx8 0x80 -> 0xFFFFFF80` witness is the
  architecturally correct MOVSX r32 form, as the author report states.
  No duplicated IR/executor: `stepNarrow` delegates to the accepted
  evaluator plus a RIP advance; no new memory semantics invented.
- **Round trip:** generic over all registers (`cases dst <;> cases src
  <;> rfl`) and over all `BitVec 32` displacements plus any suffix
  (`roundtrip_store32` by simp over the decoder/encoder definitions).
  Not pinned-only. Genuine.
- **Arbitrary-input coverage:** `decodeNarrow_abdeckung` with per-level
  shape lemmas (`decodeNarrowStore/89/0F/Tail_abdeckung`) proves every
  successful decode of an arbitrary byte list consumes exactly its stated
  length at the exact per-row length, with `laengeOk` validity and
  `decodeNarrow_consumes` as corollary. Decoder-side only, mirroring
  `DecodingCoverage` — openly stated, matches the task's bounded demand.
- **Disjointness:** `narrow_pilot_verweigert` proves the pilot refuses
  every covered encoding over any suffix, by `rfl` per register pair
  (machine-checked, not asserted). `decodeCombo` facts
  (`kanonisch`/`erweitert`/`nichts`) are direct unfolds. No shadowing.
- **Refusals:** empty input, lone/truncated REX, truncated move,
  ADD opcode, 16-bit rows 183/191, REX.W, REX.X, mod=0, wrong SIB,
  short displacement, extension-with-memory-ModRM — all `rfl`-decided.
  Real planted refusals.
- **Execution/frames:** per-form step equations plus width-exact frame
  facts reusing `regSet_gleich`, `storeNarrow_success`,
  `storeNarrow_frame_b32`. Reached witnesses are `decide`-closed:
  memory-changing store (byte 0->4, RIP 4096->4103), zero/sign-extension
  pins, 32-bit clearing pin, length-0 and permission-denied refusals.
- **Axioms:** build evidence prints every main theorem within
  `propext`/`Classical.choice`/`Quot.sound` subsets. Standard goal
  axioms. Clean.
- **Build:** final evidence is `./lean-probe` 0 errors and `./lean-bau`
  `Build completed successfully (428 jobs)`. Intermediate probe
  failures in the evidence log are development iterations, all resolved
  before the commit. One remaining cosmetic linter warning (unused
  simp arg `narrowLen`) is not an error.
- **CUTS/witnesses:** CUTS block present and accurate; `#print axioms`
  for each main theorem present. No INHABITATION `_zeuge` required
  (no premise quantifies over program syntax, no `ZEUGE:` target);
  the `decide`-closed execution pins exceed what the rule demands.
- **Scope discipline:** PATCH touches exactly the three owned paths;
  `Grammatik.lean` diff is the single additive import. No Spec/goal/
  emitter/checker changes, no optimiser files, no vacuity, no guessed
  ISA beyond the stated canonical subset, no closure exaggeration —
  fetch wiring (`Byteschritt` via `decodeCombo`), 16-bit rows, loads,
  ALU forms, source/TSO/ABI claims are all explicitly open.

## Accepted bounded claim

Four covered narrow rows with canonical encoder, bounded independent
decoder, generic round trip, arbitrary-input decoder-side consumption,
pilot disjointness with combined dispatcher, and `stepNarrow` execution
reusing the accepted narrow evaluator with width-exact frames and
reached memory-changing/extension/refusal witnesses. Fetch wiring
through `Byteschritt` is the measured next integration.

## Finding on the task text

Nothing technically wrong. The task's "arbitrary successful decode
consumption" is satisfied decoder-side; encoder-side arbitrary-input
claims are neither asked nor made.

CANDIDATE: 562 10e5b2255691905b2c306220032dc576958bead4
VERDICT: ACCEPT
