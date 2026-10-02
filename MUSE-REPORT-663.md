# MUSE-REPORT-663: Exact review of author 662 (LOCK atomic and fence final-byte execution)

## Candidate

CANDIDATE: 662 56e70f849a52295e9b60d12cb91cb73045e9838c

VERDICT: ACCEPT

Bounded acceptance: the three claimed 64-bit rows (LOCK XADD, LOCK CMPXCHG
over mod=2 base+disp32, MFENCE) with canonical byte decode, fetched
execution, the proved `LockedOps` adapter with the failure-path mismatch
resolved, joint memory-changing witnesses and nine planted refusals, all
inside the file's exact CUTS. No full-family, W/GX-bridge, timing or
progress claim is accepted (none is made).

## What was inspected
- Exact pinned snapshot `.tmp/review/author-662/` (SNAPSHOT.json: author
  662, base 1d087115, 3 files, clean): `PATCH.diff` (1249 lines),
  `MUSE-REPORT-662.md`, `OWNER-TASK.md`, full 1144-line module
  `grammatik/Grammatik/X86/LockedInstructionExecution.lean`.
- Official local manuals `.tmp/HARDWARE-REFERENCES/` (Intel SDM
  325462-093US, Sep 2026, sha-pinned in REFERENCES.json; AMD absent, and
  no AMD claim is made).

## Evidence (all reproduced by the reviewer with queued wrappers)
- `./lean-probe .tmp/review/author-662/grammatik/Grammatik/X86/LockedInstructionExecution.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`. The candidate
  elaborates unchanged against current master modules (no base drift in
  any referenced interface).
- `#print axioms` output (full, from the probe): every main theorem
  depends only on a subset of `[propext, Classical.choice, Quot.sound]`
  (standard `gabbro_ziel` set). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` (one grep hit is English prose "admit no
  fetch" in a comment). No Prop-typed premises; every premise is used.
- PATCH touches only the owned files: new module + one additive
  `import Grammatik.X86.LockedInstructionExecution` in
  `grammatik/Grammatik.lean` + report. No source/checker/Spec/goal/
  emitter/optimiser file touched.

## Architecture checks (manual text verified, not just Lean green)
- Byte forms: LOCK=0xF0, REX.W canonical subset (0x48/49/4C/4D, X=0),
  0F C1 (XADD) / 0F B1 (CMPXCHG), mod=2 ModRM + disp32 with SIB exactly
  when base needs it (0x24); MFENCE as 0F AE with reg field 6, any r/m.
- #UD exactly where the manual states it: LOCK on register destination
  (parsed `lockAufRegister`, len 5), LOCK on MFENCE (`lockAufZaun`,
  len 4), fence without SSE2 (`sse2Fehlt` via control-state gate, never
  decode). MFENCE reg==6 requirement is correct disambiguation (E8=LFENCE,
  F8=SFENCE are other instructions).
- Failure path: CMPXCHG failure writes the word back, needing
  `schreibbar8` (manual: "write cycle without regard to the result of
  the comparison", "never a locked read without a locked write";
  verified at txt lines 46998-47000). The accepted `casSchritt` stutter
  mismatch is resolved by proof (`lockVoll_cmpxchg_fehlschlag_adapter`:
  same observable bytes + `false`, write permission additionally
  pinned), not assumed away; `zeug_schreibfehler_bei_fehlschlag` pins
  `speicherFehler` on a readable-but-unwritable word.
- XADD: old word into source register, sum installed, `add64` flags;
  CMPXCHG: RAX implicit accumulator, `sub64` flags, ZF set/cleared,
  pinned by fetched witnesses (10->15/rax=10; 10->7/ZF; fail keeps
  10/rax=10/ZF-cleared).
- TSO: locked steps require the empty own buffer and operate on
  canonical memory via `read64`/`write64` (real permission checks);
  MFENCE gates on admitted SSE2 (silicon AND MXCSR/OS readiness) plus
  the empty own buffer and moves only RIP; foreign buffers untouched
  (pinned). No drain, linearisation, timing or retry-bound claim.
- Dispatcher: `decodeLockExt` tries accepted `decodeExt` first (no
  shadowing by construction); three closed rows proved refused by it.
  Generic arbitrary-input disjointness is correctly left OPEN in CUTS.
- Witnesses are non-degenerate: joint `_zeuge` run fetched code from
  executable bytes with memory/register change (XADD 10->15); nine
  planted refusals cover register-LOCK, fence-LOCK, truncation,
  execute-denied, buffer, misalignment, SSE2-off, read fault and the
  failure-path write fault. Refusals are admission/`speicherFehler`,
  never reclassified as #UD.

## Notes (not repairs)
- The `lockFetch` length-consistency conjunct is implied by decode
  construction; `laengeOk` and `ausfuehrbarN` do the real admission
  work. Harmless.
- REX-prefixed MFENCE and unlocked XADD/CMPXCHG are refused rather than
  modelled; both refusals are conservative and explicitly listed in
  CUTS. No guarantee is weakened.
- Whole-project `lean-bau` green (460 jobs, per author report) was not
  re-run here: this review owns only MUSE-REPORT-663.md and touches no
  source. File-level green plus axioms plus interface-signature checks
  above carry the verdict.

## Open (unchanged, per file CUTS)
64-bit rows only; mod=2 base+disp32 only; alignment as profile contract;
no W/GX refinement; no SMC-overlap guard; device/MMIO/NT/speculation
open; generic dispatcher disjointness beyond the three pins open;
split-lock/HLE/#AC open.
