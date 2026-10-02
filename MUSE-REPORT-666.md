# MUSE-REPORT-666: Hardware completion — practical integer width and compact encoding rows

## What was done

New module `grammatik/Grammatik/X86/IntegerHardwareForms.lean` (~1550 lines, all green)
plus the additive umbrella import in `grammatik/Grammatik.lean`. It closes the missing
practical scalar integer logical/test rows and compact-immediate rows with
width-parametric shared rules over the accepted canonical producers — no copied
evaluators, no new word/register/state types, no `Befehl` change, no
integer-to-pointer conversion.

- Value/flag/width layer: `IntHwOp` (AND/OR/TEST/NOT/NEG with explicit `Breite`),
  shared `intHwWert` dispatch routing to `andB`/`orB`/`notB`/`negW`; TEST flags
  equal AND flags; AF-none observation abstraction (`inthw_logik_af_none`: AF is
  `none`, never read as false); b64 agreement with `and64`/`or64`; defined NEG AF;
  32-bit zero-upper derived generically from `mergeRegNarrow_b32_fits`, 64-bit full
  word, 8/16-bit partial-merge pins.
- Register codec: AND 0x21, OR 0x09, TEST 0x85, NOT/NEG group F7 /2 /3 (disjoint
  from MulDiv /4/6/7); b64 REX.W, b32 REX W=0; REX.R-over-digit refusal; b8/b16
  encoder empty (OPEN). Per-form round trips, pilot disjointness, pins, planted
  refusals (empty/truncated/wrong-opcode/mod≠3/MulDiv-digit/REX.X/no-REX).
- Register step `stepIntHw`: shared merge discipline, TEST writes no register, NOT
  preserves flags, NEG installs `NegGueltig`-satisfying snapshot, exact-length
  check, memory-freedom theorems (adapter for address lane 664).
- Compact immediates `IntHwImm`: one int32 with architectural sign extension;
  encoder picks imm8 (0x83, 4 bytes) exactly when the value fits else imm32 (0x81,
  7 bytes), proved by `kompakt_add_feuert`; ADD/SUB/CMP b64-only (DEFINED AF via
  `add64`/`sub64` — the required observation production, not an AF-none
  abstraction); AND/OR/XOR b64+b32; ADC/SBB and 32-bit-arithmetic refusals;
  immediate step with CMP no-write and b64 AND==register-snapshot agreement.
- Fetched-byte paths `fetchIntHw`/`fetchIntHwImm` + `intHwByteschritt`/
  `intHwImmByteschritt` from ACTUAL executable memory with length/permission
  admission and `fetch*_erfolg` theorems (mirror of `fetchDekodiert` discipline).
- Branch/validator adapters: `inthw_test_zf`, `inthw_cmp_l`, `inthw_cmp_e` over the
  shared values, plus `wort_beq_decide`.
- Arbitrary-input register length soundness: every successful register decode
  reports length 3 (`decodeIntHw_laenge` via per-layer lemmas), hence passes
  `laengeOk`; decode-to-execute selection theorems per row (producer interface for
  lane 660).
- Joint witness `inthw_zeuge`: decoded AND bytes step 12&10=8 through the reused
  evaluator, fetched-byte stepper agrees from actual memory, pilot store carries
  8 into the data cell with observable byte change, NEG `sMin` overflow, compact
  (4B) vs wide (7B) choice, and planted refusals — jointly instantiated,
  non-degenerate (memory-changing reached run + loud refusals).

## Verification

- `./lean-probe grammatik/Grammatik/X86/IntegerHardwareForms.lean`: 0 errors, no
  `sorryAx` anywhere; axioms are `[propext]`, `[propext, Quot.sound]`, or the
  standard `[propext, Classical.choice, Quot.sound]` triple.
- `./lean-bau`: exit 0, 460 jobs, whole project green. `gabbro_ziel` untouched
  (no file in its cone modified; only an additive import).
- Inhabitation: `inthw_zeuge` is the joint memory-changing witness; per-task
  ZEUGE lines were truncated away, so the X86-lane joint-witness practice
  (`muldiv_codec_zeuge`, `shift_kette_speicher`) is followed and each conjunct
  names the generic theorem it instantiates.

## What remains OPEN (recorded in CUTS, not silently reduced)

- No hardware correspondence: opcodes/digits/REX discipline/flag rules are stated
  canonical-subset choices with self-consistency only. The task's
  `.tmp/HARDWARE-REFERENCES/` bundle is ABSENT from this clone (`.tmp` holds only
  `LANE.md`); no manual heading/page/provenance could be recorded and no new ISA
  detail was invented — all rows reuse accepted producer semantics.
- No b8/b16 codec rows; no 32-bit ADD/SUB/CMP immediates (no narrow arithmetic
  flag snapshot); no ADC/SBB, memory-operand logic, or INC/DEC rows; full
  immediate arbitrary-input length soundness (7/4 consumption) — immediates run
  via explicit-length steps plus runtime fetch admission.
- No source correspondence, no TSO/GX bridge (sequential single-`Speicher` facts;
  register rows provably never touch memory), no ABI/image/entry/relocation, no
  cost or divide-trap transfer. No new assumptions, no checker codes/examples.

## Task feedback

The lane file arrived truncated (rule 13's ZEUGE-line requirements cut off mid-line
at "every..."), so witness obligations were met via the established X86 joint-witness
pattern. The missing hardware-reference bundle should be staged into lane clones or
the task should name fallback provenance explicitly.
