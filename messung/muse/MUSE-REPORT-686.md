# MUSE-REPORT-686: Essential SSE2 integer and memory byte forms

Lane 686, clone `/home/simon/Dokumente/gabbro-muse/a686`, branch `muse/686`.
Owned files only: `grammatik/Grammatik/X86/VectorIntegerHardwareForms.lean`
(new, 2348 lines, 151 theorems, 41 defs/inductives), `grammatik/Grammatik.lean`
(additive umbrella import), this report. No producer file touched.

## What was done

Closed 15 selected SSE2 rows as canonical byte decode plus fetched
execution on the shared XMM state: PADDB/W/D/Q register-register
(`66 0F FC/FD/FE/D4`), PAND/POR/PXOR register-register
(`66 0F DB/EB/EF`), packed PSLLQ/PSRLQ with register count
(`66 0F F3/D3`) and imm8 (`66 0F 73 /6|/2`), MOVDQA/MOVDQU 128-bit
load/store (`66 0F 6F/7F`, `F3 0F 6F/7F`, base+disp32, pilot SIB rule).

- Lane arithmetic: all four PADD widths reuse accepted `vecAdd`
  (`laneGet_add`, no inter-lane carry); logicals reuse
  `vecAnd`/`vecOr`/`vecXor` at `.b64`; shifts use new
  `vecShlQ`/`vecShrQ` with SATURATING counts (`COUNT > 63`
  zeroes; only low 64 count bits checked), never masked-count
  semantics. `vecShlQ_satt_vs_maske` pins count 64 zeroes vs
  masked shift-by-zero.
- Correct legacy admission: `vektorLegacyZugelassen` (silicon
  SSE2 + CR0.EM/TS + CR4.OSFXSR + OS bit, NO XCR0 input) with
  `vektorLegacy_verfeinert` (accepted 674 gate implies it; old
  gate kept as safe stronger, never faulted) and
  `vektorLegacy_strikt` (strictness witness with XCR0 SSE clear).
- Step semantics `stepIntVec` with 15 per-row equations, generic
  flags/RIP/GPR frames, per-row XMM preservation, non-store
  memory preservation, per-lane effects at every width, store
  read-back through `vecRead_nach_write`, shared-row decode AND
  step agreement with accepted `decodeVector`/`stepVector` for
  PXOR/PADDQ.
- Fetched adapter for consumers: `fetchIntVec`,
  `intVecByteschritt`, `intVecValidatorZugelassen`,
  `intVec_fetch_bridge`, and `decodeComboIV` (unified
  dispatcher first, selected rows where it refuses; 7 pinned
  `decodeExt`-refusal proofs, one per opcode group).
- Joint witness `intVec_joint_zeuge`: movdqu load, wrapping
  paddb (lane 0 `0x01+0xFF` wraps, lane 1 independent),
  psllq imm8, movdqa store; byte 18 observably changes,
  byte 32 frame, xmm7 sentinel and flags preserved.
- Fetched pin `intVec_fetch_bridge_pin` through actual code
  bytes; negatives for saturated count, #GP alignment, missing
  read/write permission, feature gate, high registers
  (xmm8/xmm15 positive), VEX/bare-0F/truncation/modRM
  confusion, and overlapping footprints.

Manual provenance: Intel SDM 325462-093US (Sept 2026), local
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`;
exact opcode/flags/saturation/#GP/Type-1/Type-4 citations are in
the file header and CUTS. Recorded honestly: MOVDQA/MOVDQU legacy
entries have no Flags-Affected section (modelled from DEST-only
Operation text, stated as observed absence); PADD flag-freeness
from the description sentence plus accepted producer precedent.

## Integration repair (second commit)

The integration gate failed the first candidate with a name
collision: `Gabbro.Grammatik.X86.witKern0` already exists in the
new-master module `Grammatik.X86.ArchitecturalFlags` (absent in
this clone). Nothing was merged. Repair, owned files only:
renamed my entire generic witness family `wit*` to lane-specific
`iv*` (`ivT0`-`ivT4`, `ivKern0`, `ivXmm0`, `ivX4`, `ivM4a`,
`ivM4`, `ivBereit`, `iv_gate`, `ivLd`, `ivS1`-`ivS4`, `ivHwr`,
`ivNachbar32`, `ivXmm7`, `ivFlags`, `ivCodeT`, `ivTRO`/`ivTWO`,
etc.; 14 disjoint-stem replacements, English words verified
intact). No semantic change: `./lean-probe` 0 errors,
`./lean-bau` green (466 jobs), axioms unchanged. A fresh
independent review is required for the changed commit; no
full source/binary chain acceptance is claimed.

## Checks

- `./lean-probe .../VectorIntegerHardwareForms.lean`: 0 errors;
  `#print axioms` all within `[propext, Classical.choice,
  Quot.sound]` (subset of `gabbro_ziel`).
- `./lean-bau`: green, "Build completed successfully (466 jobs)".
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
  Every premise is used (uncovered premises were removed during
  development, e.g. vacuous lane bounds on saturation lemmas).

## What remains open (not claimed)

See CUTS in the file: YMM upper bits unmodelled; MXCSR/x87/
segments/paging/interrupts/timing absent; no vector atomicity
(two ordered chunk accesses, torn state stands); TSO/GX/source/
budget/progress/call-log open; `simdFreigabe` untouched;
register-register 6F/7F move shape refused as documented gap;
non-selected rows (saturated/fused arithmetic, shuffles,
packed-FP, VEX/EVEX/MMX) refused by absence. No full
hardware-model closure is claimed from this subset.

## Task notes / findings

- Lean 4 struct-update `{ s with ... }` does not tolerate a
  newline after a comma or after `:=` in this toolchain
  (parse error "unexpected identifier; expected '}'"):
  all multi-field updates are single-line.
- Elaboration order: equation applications with leading `_`
  before `(by decide)`/`rfl` arguments can hang `whnf`
  (observed timeout); fully explicit argument lists fix it.
- Bare `0` vs `(0 : BitVec 32)` elaborated differently in two
  positions (pretty-printed `0` vs `0#32`), breaking a
  `simp [hc]` rewrite; `if_neg (by decide)` avoids the chain.
- `cases h : e` substitutes `e` in the goal too: in
  `fetchIntVec_erfolg` the first conjunct becomes `rfl`, not
  the decode hypothesis.
- `rw [h1]` on a `vecWrite`-unfolded goal leaves
  `match some ...`; `simp only [h1, h2]` reduces it.
