# MUSE-REPORT-1294: Exact review of candidate 1293 (capstone multi-family run)

## Candidate

- Author lane 1293, pinned HEAD `63892bc7e994904469ff3402d6d5f3d7c8288fca`
  (base `63e2ec3543deec0c4cce21e9431dfffba157ebd6` per `.tmp/review/SNAPSHOT.json`).
- Changed files: `MUSE-REPORT-1293.md` (new), `grammatik/Grammatik.lean`
  (+1 import line), `grammatik/Grammatik/X86/HwKapsteinRun.lean` (new, 785 lines).

## What was checked

1. **Forbidden tokens**: grepped the candidate tree for `sorry` / `sorryAx` /
   `admit` / `axiom` declarations / `native_decide` / `unsafe`. The Lean file
   is clean; the words occur only in task/report prose and in the historical
   `BUILD-EVIDENCE.json` (an intermediate `sorryAx` during development, gone
   from the final state). No `intro _` / `have _ :=` discards.
2. **Axioms (independently re-probed)**: `./lean-probe` on the candidate file
   (in place; imports resolve against this clone's accepted modules):
   `== 0 error(s) in the COMPLETE output; exit 0`.
   `run_haupt`: `[propext, Classical.choice, Quot.sound]` (exactly the goal
   standard); `runStart_wf`: `[propext]`; `runDrain0_run`,
   `runKap_anhang`, `runKap_wf`: `[propext, Quot.sound]`.
3. **Existing files**: `PATCH.diff` shows exactly one added import line
   (`import Grammatik.X86.HwKapsteinRun`) in `grammatik/Grammatik.lean`;
   nothing else touched.
4. **Premise use**: every theorem consumes all its premises
   (`runStart_zugelassen` uses `f`; `runFp_eq` uses `hfp`; `runVec_eq` uses
   `hgate`; `runKap_anhang` / `runKap_wf` / `runDrain0_run` /
   `liste_gleich_replicate` use all of theirs).
5. **Lifted, not copied**: all reused names verified present in this clone's
   accepted modules — `kap_wf`, `kap_lock/fwd/basis/stapel/fp/vec/drain_embedded`
   (`HwKapstein.lean`), `hwLockSchritt`, `hwLockWitStart_zugelassen`,
   `pinXadd` (`LockedInstructionExecution.lean` / `HwLockRmw.lean`),
   `s32Schritt_addssRR`, `stepIntVec_paddb`, `fwdAdapter`, `stapelAdapter`,
   `drainAdapter`, `hwWf_aus_zugelassen`. The candidate defines only
   run-specific machines (`runStart`, `runNachLock/Store/Push/Ruf/Fp/Vec`,
   `runDrain0`, `runNachFlush0/1`), closed `decide` pins, and the `RunKap`
   chain infrastructure (`RunKap`, `runKap_anhang`, `runKap_wf`,
   `runKap_einzel`, `liste_gleich_replicate`, `runDrain0_run`, `run_haupt`).
   No model duplication.
6. **Refusals**: no new refusal theorem in the run file; the refusal story is
   inherited from the accepted capstone (`kap_verweigert`, present in this
   clone's `HwKapstein.lean`). Correct layering for a composition run; the
   MECHANISM paragraph's per-family refusal demand is the stale-copy part the
   author flagged, and re-proving refusals here would duplicate the capstone.
7. **Witness non-degeneracy**: `run_haupt` exhibits a reached 38-step
   two-core run (11 tagged prefix steps + 24 core-0 drains + core-1 drain +
   2 end observations = 38): LOCK XADD moves word 10 to 15 (`decide`),
   rax takes 10, RIP 4096 to 4105; owner-only forwarding plus foreign
   canonical observation; push/pop/call/pop/ret at slot 8200; scalar
   `addss` (`s32reg`); packed `paddb` (`vecReg`); exact final memory
   (word 15 at 8192, `runStoreWort` at 8208, `runRufWort` at 8200,
   byte 99 at 8216; both buffers empty). Core 1 genuinely participates
   (pending byte, drain, both-core observations). HARD RULE 13 needs no
   `_zeuge` companion: no premise quantifies over program syntax.
8. **Silicon** (against `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
   XADD r/m64,r64 = REX.W + 0F C1 /r, MR encoding, LOCK allowed, #UD only
   for non-memory destination. `pinXadd` = F0 48 0F C1 85 00 00 00 00 is
   LOCK / REX.W / XADD / ModRM 0x85 (mod=10, reg=rax source, r/m=rbp+disp32)
/ disp32=0: `LOCK XADD [rbp+0], rax`, 9 bytes, no SIB. Length, RIP advance,
   and exchange-add semantics (mem 15, rax 10) all agree. No silicon finding.
9. **CUTS honesty**: the CUTS block (and report) state exactly what is open —
   per-step fetched decoding only for LOCK (FP/vector cite accepted byte pins
   and run as direct family events; full dispatcher union is open in the
   capstone CUTS), no hardware correspondence, no W/GX bridge, no
   source/checker/contract/entry/ABI/loader/budget/liveness claim, and the
   task MECHANISM-vs-TASK mismatch. No claim larger than the proof.

## Last build result

- `./lean-probe <candidate file>`: `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (677 jobs).`
- This clone's tree is untouched (candidate was probed in place, nothing
  copied); only this report is committed.

## What remains open (not a defect of this candidate)

Full per-step fetched decoding through one dispatcher; the W/GX bridge; all
items the candidate CUTS already names.

## Verdict

CANDIDATE: 1293 63892bc7e994904469ff3402d6d5f3d7c8288fca

VERDICT: ACCEPT

The reviewed run composes the 21 accepted family adapters into one reached, non-degenerate,
two-core `HwVollSchritt` chain with `HwWf` preservation and exact final
memory, reusing every accepted definition unchanged, with standard axioms and
honest CUTS. No unsupported desired-correctness premises, no weakened
guarantees, no fake closure.
