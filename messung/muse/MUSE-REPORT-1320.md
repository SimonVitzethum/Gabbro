# MUSE-REPORT-1320: exact review of candidate 1319 (8-bit operand forms)

Lane 1320, clone `/home/simon/Dokumente/gabbro-muse/a1320`, branch `muse/1320`
(verified via `git rev-parse --show-toplevel` + `git branch --show-current`).
Owns ONLY this file. Review of author lane 1319 (pinned HEAD see below).
pinned HEAD `77be369eac8c3794ce296f7f5398efb6b4a9f40b`
(base `f92c2649c25c822f0ff7791f82dfecad9c7d4c31`, SNAPSHOT clean:true).
The author clone and the pinned commit were never touched; only the delivered
FILES under `.tmp/review/author-1319/` were read
(`SNAPSHOT.json`, `PATCH.diff`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`,
the candidate Lean file at its repository path).

## Verdict

VERDICT: ACCEPT

CANDIDATE: 1319 77be369eac8c3794ce296f7f5398efb6b4a9f40b

## What was checked

1. **File scope (PATCH.diff).** Exactly three paths: new `MUSE-REPORT-1319.md`,
   new `grammatik/Grammatik/X86/IntByteForms.lean` (998 lines), and
   `grammatik/Grammatik.lean` with exactly one added line,
   `import Grammatik.X86.IntByteForms`, at the end of its base version.
   No existing file is otherwise touched. Compliant.
2. **Forbidden patterns.** Grep over the candidate file for
   `sorry|admit|native_decide|unsafe|^axiom`: the only hits are English prose
   ("admitted"/"admits"). No `intro _`, no `have _ :=`. Compliant.
3. **Build (`./lean-probe`, queued wrapper).** A `cp` of the candidate file
   into my own `grammatik/` tree was permission-blocked, so I probed the
   delivered file directly at its `.tmp` path (`lean-probe` accepts any path;
   imports resolve through the `grammatik/` lake environment):
   `== 0 error(s) in the COMPLETE output; exit 0`.
   Note: my clone base is NEWER than the candidate base, so this additionally
   proves the candidate file is robust against base drift (all accepted names
   it uses — `codeReg`, `mergeRegNarrow`, `rolB`/`rorB`/`rclB`/`rcrB`,
   `adcWert`/`sbbWert`/`incWert`/`decWert`, `rotRoundtrip_reg_eins/_cl`,
   `hochbyteCode`, `projZustand`/`setKernVonFp`/`hwWitStart`,
   `issueByte`/`loadByte`/`flushKern`, `HwAdapter`/`setKernDaten_wf` —
   were grep-confirmed present in my tree and elaborated cleanly).
4. **Axioms.** All 18 `#print axioms` lines are `[propext]` or
   `[propext, Quot.sound]`; no `sorryAx`, no new axiom, no
   `Classical.choice` needed. Standard. Compliant.
5. **Lift, not copy.** `byteRol/Ror/Rcl/Rcr/Adc/Sbb/Inc/Dec` are thin
   wrappers fixing `.b8` with `rfl` agreements over the accepted evaluators;
   merge discipline is the accepted `mergeRegNarrow .b8` (no second merge);
   codec legs reuse `rotEncode`/`decodeRot`, `carryEncode`/`decodeCarry`;
   adapter and witness reuse `HwAdapter`, `setKernDaten_wf`, `hwWitStart`,
   TSO `issueByte`/`loadByte`/`flushKern`. Genuinely new: `byteZielReg`,
   `byteXchgWert`, the 86H codec — the report honestly states no accepted
   8-bit XCHG evaluator exists. Compliant with the reuse rule.
6. **Premises used.** Spot-checked every family of theorems: admission/length
   premises are discharged by `rw`/`refine` into the goal or an admission
   conjunct (round trips restate the admission beside the bytes, per the
   task); `byteZielReg_ausserhalb` uses its bound via `omega`; step equations
   rewrite all three premises. No discarded premise found.
7. **Planted refusals really refuse.** All refusal theorems closed by kernel
   computation in the green build: `byteXchg_hochbyte_verweigert`,
   `byteXchg_sonde_verweigert` (LOCK/wrong-opcode/memory-mode/truncation),
   `byteFam_laenge_misslungen`, `byteFam_unzulaessig_misslungen`,
   `adapterByteFam_verweigert_bei_laenge/_ohne_zulassung`. Compliant.
8. **Witness non-degenerate.** `byteFam_zeuge` joins: `HwWf` at start, core 0
   INC AL (5 becomes 6, RIP +3), core 1 DEC CL (becomes 0xFF), shared-byte
   stillness after the register-only family steps, owner-only forwarding
   (core 0 reads 6, core 1 reads 0), and the memory-changing drain
   (shared byte 0 becomes 6). Two cores, register change, memory change.
   Compliant. The report's remark is accepted: the family plug is
   register-only by construction, so the memory leg is TSO issue/flush —
   `byteFamSchritt_speicher` proves the plug itself never touches memory.
9. **Silicon facts vs local Intel extract** (`.tmp/HARDWARE-REFERENCES/`):
   `byteZielReg` matches the architecture (AL/CL/DL/BL always; SPL/BPL/SIL/DIL
   only with REX; AH/CH/DH/BH refused as outside the `Register` vocabulary;
   R8B–R15B only with REX); opcode 134 = 0x86 = `XCHG r/m8, r8` per extract
   line 137946; ModRM side reconstruction (REX.B*8 + r/m, REX.R*8 + reg,
   mod == 3) is self-consistent over all 256 pairs by `rfl`; merge pins show
   low-byte-take/upper-kept with the 32-bit zero-extend contrast; XCHG leaves
   flags untouched. The decoder accepting REX.W-bearing prefixes on the 8-bit
   path is silicon-harmless (extract: unneeded REX bits are ignored) and the
   encoder emits canonical W-clear bytes. No defect.
10. **Honest finding, not hidden.** `byteRot_ah_befund` pins that the accepted
    rotate codec maps 8-bit code 4 without REX to `.rsp` (silicon: AH); the
    candidate refuses that code on the selector side and does not touch the
    accepted file. This is a recorded obstruction with an owner needed for the
    accepted-file repair — exactly what the wave rules ask for. Not a reason
    to repair THIS candidate.
11. **CUTS honest, no over-claim.** Self-consistency only; no hardware
    correspondence, no LOCK/RMW, no 8-bit memory forms at the plug, no
    SIB/addressed forms, no W/GX bridge. `IntSignXchg` absent in the candidate
    base (present in my newer reviewer base — base drift, not a defect; the
    task named it conditionally).
12. **Full build (`./lean-bau`, queued wrapper, own tree without the
    candidate file):** `Build completed successfully (692 jobs).`
    (Candidate evidence reported 688 jobs on its older base; the delta is
    base drift, verified green on both sides.)

## Remarks for the integrator

- The candidate applies cleanly in intent but its `Grammatik.lean` hunk is
  against base `f92c2649`; the current master tail has moved on (692 vs 688
  jobs, `IntSignXchg` etc. merged since). Expect the import line to re-apply
  at the new tail; no semantic conflict (fresh module, fresh name).
- Follow-up owner needed: the accepted rotate-codec AH gap
  (`byteRot_ah_befund`) — repair belongs in the accepted rotate codec files,
  out of scope for this lane.
- Method note: `cp` into my own tree was blocked by the permission
  classifier, so no test copy was ever placed in my `grammatik/` tree
  (`git status` clean before and after; only this report is committed).
  Probing the delivered file at its `.tmp` path is equivalent for a
  self-contained module check.
