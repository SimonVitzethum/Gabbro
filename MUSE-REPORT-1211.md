# MUSE-REPORT-1211: FP s32/MXCSR rows in the unified dispatcher

Lane 1211 (follow-up of lane 1129 `HwFpControl.lean`). Clone
`/home/simon/Dokumente/gabbro-muse/a1211`, branch `muse/1211` verified at
start. Owned files only: `grammatik/Grammatik/X86/HwFpDispatch.lean` (new),
`grammatik/Grammatik.lean` (one import line appended),
`MUSE-REPORT-1211.md`.

## What was done

New file `grammatik/Grammatik/X86/HwFpDispatch.lean` (~1310 lines),
connecting the accepted s32 (`ScalarFloat32HardwareForms`: `s32Schritt`,
`s32Decode`) and MXCSR (`FpControlHardwareForms`: `mxcsrSchritt`,
`mxcsrDecode`) rows to the coherent machine (`HardwareExecution`:
`HwMaschine`/`HwSchritt`) through a dispatcher extension. Accepted
evaluators are lifted, never redefined.

1. **Dispatcher** (§1): `FpDispInstr` (`.ext`/`.s32`/`.mxcsr`),
   `fpDispLen`, `decodeFpDisp` (unified `decodeExt` first, `s32Decode`
   then `mxcsrDecode` only on earlier `none`) with selection theorems
   `decodeFpDisp_ext/s32/mxcsr/nichts`.
2. **Disjointness** (§2): closed-chain pins in every direction —
   `decodeExt` refuses the s32/LDMXCSR/STMXCSR witness rows, the new
   decoders refuse each other and the old DOUBLE row, the old row stays
   unified (`pin_ext_fp_movsd` cited), and each new row is taken in its
   own arm (`pin_disp_s32_arm/ldmxcsr_arm/stmxcsr_arm`). **No overlap
   found — no FINDING to report.**
3. **Fetch** (§3): `fpDispZugelassen` + `fetchFpDisp` with
   `fetchFpDisp_erfolg` (decode equation, length equation, length guard,
   execute permission — the `fetchExt_erfolg` discipline).
4. **Gate, re-proved** (§4): `fpDispGate` reuses the accepted
   `fpHwCvttZugelassen` predicate but every gating fact is proved here
   from the gate definition (`fpDispGate_cvtt_gleichung` is `rfl`;
   NaN refusal and `42.0` admission unfold it); `fpDispSchrittZustand`
   with per-leg selection; `fpDispGated`/`fpDispByteschritt` with
   refusal theorems. No family gate theorem cited.
5. **Machine step** (§5): `FpDispEreignis`/`FpDispSchritt` — register
   legs carry fetch evidence over the actual window, the `.ext` leg the
   gate, the MXCSR leg the pinned `.ldmxcsr` form, plus the shared TSO
   byte legs; `fpDispSchritt_wf`.
6. **Agreement** (§6): s32/LD legs ARE `FpCtrlSchritt`, unified IS
   `HwSchritt.reg`, TSO legs ARE the coherent TSO steps; STMXCSR and
   MOVSS-store travel as four buffered byte issues of the accepted
   stored word (`fpDispMxcsrAusgabe/fpDispMovssAusgabe` over
   `fpCtrlAusgabe32`, with wf and `FpGruppe32` establishment).
7. **Refusals** (§7): bad length, refused profile, LOCK `#UD`, STMXCSR
   on the register path, conversion domain on the unified leg,
   unreadable/unwritable bytes.
8. **Witness** (§§8–10): 11-byte image (`ADDSS` + `LDMXCSR [rax+4]`),
   two cores; `fpDisp_zeuge` joins fetched s32 add (`3.0f32`, upper
   preserved, RIP 4100), fetched MXCSR reset install (admission, RIP
   4107), owner-only forwarding, four-drain install (`0` becomes
   `0x40400000`, observed from both cores), NaN gate refusal, core-1
   refusal, `HwWf`. Non-degenerate: the drain changes actual shared
   memory while both cores participate.

## Verification

- `./lean-probe` after every section: 0 errors (one linter warning on
  the `∃ s'` binder, same shape as the accepted `HwFpControl` file).
- `./lean-bau`: **Build completed successfully (640 jobs)**,
  whole project green.
- `#print axioms` per main theorem: subsets of
  `propext`/`Classical.choice`/`Quot.sound` only (standard).
- Banned-token scan (`sorry/admit/native_decide/sorryAx/unsafe/axiom`):
  clean (only the English word "admits").
- No premise of any theorem is unused; no conclusion restates a premise;
  contracts are not quantified away (no contracts involved).

## Open / not claimed (see CUTS block in the file)

- No hardware correspondence (self-consistency only; silicon provenance
  cited from family files, never restated).
- `decodeFpDisp` is not wired into `fetchExt`/`HwSchritt` itself; the
  unified dispatcher still carries no s32/MXCSR rows.
- No target-to-W/GX simulation, no whole-word atomicity beyond drain
  groups; the drain/write32 byte correspondence for STMXCSR/MOVSS-store
  is open (value and footprint pinned at issue level).
- Timing/power/interrupts/faults beyond the carried divide halt absent;
  sticky flags, SNaN/DAZ/FTZ, NaN payloads at inherited family cuts.

Nothing in the task looks wrong; the "re-prove instead of cite" and
disjointness requirements were implementable as stated.

## Repair after failed integration gate (no merge happened)

Integration evidence (exact): `Lean merge build failed`, lean output
`== exit 1; 2 error line(s)`, the failing job
`✖ [640/642] Building Grammatik.X86.HwFpDispatch (10s)` with stderr
`libc++abi: terminating due to uncaught exception of type
lean::exception: failed to create thread`, `Lean exited with code 134`.

Classification: **resource failure, not a proof defect.** The log shows
zero Lean error lines for the module (the 2 counted lines are the
`failed to create thread` abort and the exit-code line); every other
file's `#print axioms` output in the same log is clean. `failed to
create thread` with exit 134 is pthread creation failing under a
parallel integration build (642 jobs, per-file `-j2 -M4096`) — the
documented symptom of virtual-address/thread exhaustion, not of a bad
proof. No finding of an overlap, wrong encoding, or broken guarantee.

Module-side repair assessment: no semantic change made, deliberately.
The owned module was re-verified with zero changes to any definition,
theorem, or proof:

- `./lean-probe grammatik/Grammatik/X86/HwFpDispatch.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (same single linter
  warning on the `∃ s'` binder as before, identical in shape to the
  accepted `HwFpControl` file; warning-only, fails nothing).
- `./lean-bau`: `Build completed successfully (640 jobs)`, whole
  project green in this clone.
- Banned-token scan still clean; `#print axioms` still standard
  subsets only; all guarantees of the candidate unchanged.

Deliberately NOT changed: weakening or restructuring proofs to chase a
resource symptom would change the reviewed candidate without a defect
to fix; the `decide` evaluations in the file are small closed
evaluations (byte lists of 4–11 bytes, bounded fetch windows, 4-step
drain chains), each green here twice (standalone probe and full
build). If the gate fails again on the same file with the same
signature, the concrete blocker to record is integration-side thread
budget, not module content.

Fresh independent review is required for the new commit (report-only
change). No acceptance of the full source/binary chain is claimed.
