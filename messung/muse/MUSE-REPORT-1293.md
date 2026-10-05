# MUSE-REPORT-1293: Capstone run — a reached multi-family program run on two cores from bytes

## What was done

New file `grammatik/Grammatik/X86/HwKapsteinRun.lean` (~790 lines) plus one
`import Grammatik.X86.HwKapsteinRun` line appended to
`grammatik/Grammatik.lean`. No other existing file touched. Every accepted
definition is reused unchanged (lifted, never redefined); no `sorry`,
`admit`, `axiom`, `native_decide`, `unsafe` (only the words inside the
CUTS/report prose).

**Start machine** (`runStart`): `pinXadd` bytes (LOCK XADD [rbp], rax)
mapped executable at 4096..4128, word 10 at 8192, data window
8192..8224 holding the lock word (8192), the stack slot (8200, from
16-aligned rsp 8208) and the foreign byte (8216) disjointly; core 0
(rax 5) and core 1 (rax 7) run from 4096 with zeroed XMM; core 1 holds
one pending byte 99 at 8216; profiles `basisHw`/`basisBereit` (full
silicon, admission reused from `hwLockWitStart_zugelassen`).

**Main theorem `run_haupt`**: a reached 38-step `RunKap` chain
(`HwVollSchritt` with the family tag of every step) on two cores:
LOCK XADD (fetched decode, word 10 to 15, rax takes 10, RIP past 9
bytes), plain store, owner-only forwarding observation plus foreign
canonical observation, push, pop, call, pop, ret, scalar `addss`
(`s32reg`), packed `paddb` (`vecReg`), twenty-four core-0 drains, the
core-1 drain, and both-core end observations. Concludes `HwWf` of the
final machine (via `kap_wf` per link), empty buffers on both cores, and
the exact final memory: locked word 15 at 8192, stored word
123456789 at 8208, younger call word 4222 at the slot 8200, foreign
byte 99 at 8216.

**Supporting definitions/theorems** (exact names):
- machines: `runDataRW`, `runReg0`, `runReg1`, `runKern`, `runBuf`,
  `runStart`, `runNachLock`, `runStoreAdr`, `runStoreWort`,
  `runNachStore`, `runPushWort`, `runNachPush`, `runRufWort`,
  `runNachRuf`, `runFpD`, `runFpT`, `runNachFp`, `runVecD`, `runVecT`,
  `runNachVec`, `runDrain0`, `runNachFlush0`, `runNachFlush1`.
- closed pins (all `decide`): `runStart_zugelassen`, `runStart_wf`,
  `runCode_bytes`, `run_lock_wort/rax/rip/fremd_buf/eigen_sicht/
  fremd_sicht`, `run_step_lock`, `run_slot_bleibt`, `run_ruf_gate`,
  `runFp_eq`, `run_fp_eintritt`, `runVec_eq`, `run_vec_gate`,
  `run_vec_puffer_pin`, `run_puffer_zensus` (8-way buffer census),
  `run_speicher_ende` (4-way final memory), `run_fwd_beobachte_pin`,
  `run_basis_fremd_pin`, `run_pop_pin`, `run_ruf_liest_pin`,
  `run_ende_beobachte_pin`.
- run infrastructure: `RunKap` (nil/cons), `runKap_anhang`,
  `runKap_wf`, `runKap_einzel`, `liste_gleich_replicate`,
  `runDrain0_run`, `run_haupt`.
- CUTS block plus `#print axioms` for `runStart_wf`, `run_haupt`,
  `runDrain0_run`, `runKap_anhang`, `runKap_wf`.

**Axioms** (`./lean-probe` first line `== 0 error(s)`):
`run_haupt`: `[propext, Classical.choice, Quot.sound]` (exactly the
goal standard); all others depend on subsets (`[propext]` or
`[propext, Quot.sound]`).

## Last build result

`./lean-bau`: `Build completed successfully (677 jobs)`.
`./lean-probe grammatik/Grammatik/X86/HwKapsteinRun.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.

## What remains open (see CUTS)

- Fetched decoding per step: only the LOCK step runs through fetched
  bytes in this run (`pin_lock_xadd_decodiert` names the same row;
  `zeug_xadd_fetch_ok` is the accepted fetched shape). The FP/vector
  rows cite their families' accepted byte pins and execute here as
  direct family events at named addresses. Full per-step fetched
  decoding through one dispatcher stays open (decoder disjointness
  beyond width-vs-unified is already open in the capstone CUTS).
- No hardware correspondence beyond self-consistency; no W/GX bridge;
  no source/checker/contract/entry/ABI/loader/budget/liveness claim.

## What I believe is wrong in the task

1. The MECHANISM paragraph describes connecting ONE family with a new
   `HwAdapter` (a stale copy of an earlier single-family lane prompt);
   the TASK paragraph asks for the capstone run. This lane builds the
   run, reusing all 21 adapters unchanged, and records the mismatch in
   CUTS (same convention as lane 1149's report).
2. "Executed ... by fetched decoding" for every step is not
   dischargeable at this level: the families decode through different
   accepted fetchers and dispatcher disjointness is open in 1149. The
   run fetches LOCK from bytes and pins the rest to the families'
   accepted byte rows; claiming more would be dishonest.
3. Toolchain note for the next lane: in this repo (Lean v4.33.1),
   multi-field structure-instance updates (`{ e with a := .., b := ..
   }`) only parsed single-line; the multi-line form fails with
   `unexpected identifier; expected '}'`. All such updates in this
   file are single-line (mirroring `hvecWitT1`).
