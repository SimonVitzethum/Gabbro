# MUSE-REPORT-1127: Multiply/divide and narrow widths connected

## What was done

NEW FILE `grammatik/Grammatik/X86/HwMulDivWidth.lean` (~870 lines, all green),
plus one `import Grammatik.X86.HwMulDivWidth` line appended to
`grammatik/Grammatik.lean`. No other existing file was touched. The accepted
`MulDivWidthHardwareForms` evaluator (`wdSchritt`/`decodeWd`/`wdEncode`) and
the accepted 64-bit `MulDiv` evaluator are lifted, never redefined or copied.

1. **Dispatcher (§1-§2).** `WdHwInstr` (`ext`/`wd`), `decodeMulDivWidth`
   (unified `decodeExt` first, `decodeWd` only where it refuses),
   `wdHwLen`, selection theorems `decodeMulDivWidth_prefers_ext`,
   `decodeMulDivWidth_wd`, `decodeMulDivWidth_nichts`.
   No-shadowing evidence: 10 unified-chain refusals of the new rows
   (`ext_weist_wd*_zurueck`: 32-bit Group-3, both immediates, both
   preparations at both widths) and 3 overlap pins showing the REX.W
   Group-3/0FAF rows stay with the unified `muldiv` arm
   (`pin_ext_wdmul64`, `pin_ext_wdidiv64`, `pin_ext_wdimul2`).
   Dispatcher pins: pilot ret unchanged (`pin_wdHw_pilot_ret`), six new
   rows take the width arm (`pin_wdHw_wdmul32`, `pin_wdHw_wddiv32`,
   `pin_wdHw_wdimul3k`, `pin_wdHw_wdimul3w64`, `pin_wdHw_wdvor98w64`,
   `pin_wdHw_wdvor99`), two overlap rows keep the unified arm
   (`pin_wdHw_ext_mul64`, `pin_wdHw_ext_imul2`). Planted refusals
   through the dispatcher: LOCK, F6 8-bit, 0x66 override
   (`wdHw_nichts_lock/f6/op16` with unified-side refusal lemmas).
2. **Unified step (§3).** `wdHwSchritt` (Ext via `stepExt`, width via
   `wdSchritt` on `kern`) with four selection theorems; divide trap is
   `halt`.
3. **Lift, never redefine (§4).** `wd_mul64_ist_mulRax`,
   `wd_div64_ist_divRax`, `wd_idiv64_ist_idivRax`, `wd_imul2_64_ist_imul2`
   (all by `rfl`), plus narrow-width agreement `wdSchreiben_narrow32/64`
   against `mergeRegNarrow` (by `rfl`).
4. **Memory discipline (§5).** `wdSchritt_speicher`: every successful
   width step leaves canonical memory alone (traps/refusals carry no
   state).
5. **Machine adapter (§6).** `adapterMulDivWidth : HwAdapter WdDecodiert`
   with `adapterMulDivWidth_wf` (HwWf preserved), `_ok` + `_proj`
   (exact agreement, successor registers over shared memory),
   `_verweigert_bei_laenge`, `_verweigert_bei_halt` (trap admits no
   successor, following the `adapterFault670` discipline).
6. **Machine outcome (§7).** `wdHwRegSchritt` reusing the accepted
   `HwRegAusgang` unchanged, with weiter/halt/verweigert selection,
   `halt_ist_kein_weiter` (no register claim on the fault arm) and
   `weiter_wf`.
7. **Joint witness (§8).** Two cores over one shared memory (core 0
   `divWd w32 17/5` -> EAX=3 EDX=2; core 1 `mul w32 17*5` -> EAX=85
   EDX=0), TSO issue with owner-only forwarding (owner 42, foreign 0),
   drain changing actual shared memory 0 -> 42 observed from both
   cores, well-formedness of both machines, zero-divisor halt and
   bad-length refusal beside the run. `wdHw_zeuge` joins all 13
   conjuncts. Non-degenerate: the drain changes actual shared memory.

## Verification

- `./lean-probe` after every addition: final `== 0 error(s)`.
- Full `./lean-bau`: `Build completed successfully (601 jobs).`
- `#print axioms` for 12 main theorems: all `[propext, Quot.sound]`
  (witness wf `[propext]` only) — standard, no new axioms.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (one English
  "admit" in a comment, matching 27 accepted files); no `Prop`-typed
  premises; every premise used.

## Open / not claimed (see CUTS)

No hardware correspondence (self-consistency only; silicon
assumptions inherited from the family file and named); no 8/16-bit
mul/div, no `/5` IMUL, no memory-addressed forms, no LOCK path; no
source/IR/ABI/loader/entry/budget link; no per-access W/GX bridge;
no timing/power. Overlapping 64-bit rows are covered twice by
construction but executed once (dispatcher takes unified first).

## Note on the task

The task asked for a witness with "at least two cores where the
family touches memory". The family is register-only by construction
(`wdSchritt_speicher` proves it never touches memory), so the witness
runs family register steps on two cores and exercises memory through
the TSO issue/forward/drain path instead; the joint theorem pins both
halves together. This is reported as an interpretation, not a
deviation: a memory-touching family step would contradict §5.
