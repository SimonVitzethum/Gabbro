# MUSE-REPORT-422: Lean proof reserve ReleaseAcquire

## Task
Lane 422 (continuous direct-compiler pool): new reusable module
`grammatik/Grammatik/X86/ReleaseAcquire.lean` plus one additive X86 import
at the end of the umbrella. Generic source/target acquire-release
obligation over the ACTUAL accepted definitions: source view primitives
(`Ordnung`/`beitrag`/`nachricht`, `Speichermodell.Sicht`) and target TSO
operations (`issueByte`/`loadByte`/`flushKern`/`zaunBereit`, `X86.TSO`).
No global foreign flushing, no source payload safety, no second IR, no
mini-machine. Friend paths untouched. Checker, Spec, goal, Rust, emitter,
Typen/execution/codec untouched.

## What was done
Created `grammatik/Grammatik/X86/ReleaseAcquire.lean` (291 lines,
`skeleton first, then one theorem per probe` per HARD RULE 10). Content:

**Source side (actual `Sicht.lean` definitions):**
- `freigabe_beitrag_deckt_sicht`: acquire read inherits the WHOLE message
  view (`m.sicht y <= beitrag .freigabe x m y`).
- `freigabe_nachricht_traegt_sicht` / `freigabe_nachricht_eigen`: release
  write publishes the writer view off-location / its timestamp at-location.
- `entspannt_beitrag_fremd_leer`: relaxed contributes 0 off-location
  (negative half of acquire).
- `freigabe_liest_uebertraegt`: joined reader view covers writer view.

**Target side (actual `TSO.lean` definitions, all LOCAL to own buffer):**
- `leer_liest_kanonisch`: empty own buffer implies canonical-memory load.
- `zaun_erwerb_liest_kanonisch`: fence-ready acquire reads canonical.
- `freigabe_braucht_flush`: release store invisible off-core until flushed
  (uses issue step, core separation, foreign miss, permission: all four).
- `freigabe_flush_sichtbar`: issue-then-flush installs the byte (positive).
- `fifo_zweite_flush`: two releases drain in order (local MP half).
- `ReleaseSchreiben` (def, plain issue, no fence) with
  `release_braucht_keinen_zaun`: own load forwards with no fence step.

**Non-claim:** `SeqCstTotal` empty inductive + `kein_seqcst_total`
(`seq_cst`-as-release/acquire is over-approximation, no total order).

**Joint witnesses (all premises held together, memory-changing):**
- `freigabe_braucht_flush_zeuge`: core 0 issues `sbX := 1` (`sb_schritt1`
  reused), core 1 loads stale 0, flush changes the byte.
- `freigabe_sichtbar_zeuge`: fence-ready start loads canonical,
  issue+drain installs `sbEins`, bytes differ.
- `freigabe_entspannt_zeuge`: concrete `Nachricht Nat Int` with view 2 at
  location 1; acquire inherits 2, relaxed contributes 0.

No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. No Prop-typed premise.
Every theorem premise is used. `#print axioms`: `[propext]` or none
(standard subset; full per-theorem list in the probe log below).

## Verification evidence
- `./lean-probe grammatik/Grammatik/X86/ReleaseAcquire.lean`:
  `0 error(s), exit 0`, six consecutive green runs during construction,
  final run after CUTS/axioms with all 15 axiom lines printed.
- `./lean-bau` (full project): module `ReleaseAcquire` BUILDS (all its
  axiom lines emitted, jobs reach 392/393), but the final umbrella step
  `Building Grammatik` crashes deterministically with
  `libc++abi: terminating ... failed to create thread`, exit 134.
- CONTROL EXPERIMENT (proves the red is NOT mine): reverted the one-line
  umbrella import (pristine `Grammatik.lean`, only pre-existing modules)
  and re-ran `./lean-bau`: identical crash at `[391/392] Building
  Grammatik`, same thread exception. The pristine tree is red in this
  environment. Single-file probes also crash flakily the same way
  (observed on accepted `Zugriffe.lean`); retries go green.
- Root cause assessment: machine resource exhaustion (prior OOM
  interruption this session; swap was full 8/8 GB; 516 live processes, 15
  opencode workers). The crash happens AFTER elaboration (4+s into the
  umbrella step; probe teardown), never as a Lean type error.
- `gabbro_ziel` axiom check: not run (blocked by the same environmental
  umbrella crash; no goal file touched).

## Status / open
Per HARD RULE 8 (never commit a red build) the tracked umbrella edit was
REVERTED (`git checkout -- grammatik/Grammatik.lean`); this commit contains
ONLY the report. The finished module remains UNCOMMITTED in this clone at
`grammatik/Grammatik/X86/ReleaseAcquire.lean` (291 lines, probe-green).
To land it when the machine is healthy: re-add the single line
`import Grammatik.X86.ReleaseAcquire` after `import Grammatik.X86.AccessList`
at the end of `grammatik/Grammatik.lean`, run `./lean-bau` to green, commit
both. No rework of the module itself is needed; no finding against the task
(the target statement stands as scoped in CUTS).

## Task feedback
Nothing in the task text is believed wrong. One observation for the
coordinator: `./lean-probe` was updated mid-session to crash-aware counting
(`exit $RC` reported, RC!=0 with no error lines counts 1); the teardown
`failed to create thread` crash is now correctly distinguished from real
Lean errors. The remaining gap is machine capacity, not lane output.

CUTS: see file §CUTS (no lowering, no foreign drain, no multi-byte
atomicity, no seq_cst total order, no payload safety, no
progress/timing/cost, no interrupt/device/code claim).
