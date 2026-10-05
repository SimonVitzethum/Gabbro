# MUSE-REPORT-1210: exact review of candidate 1209 (HwLockFetch)

CANDIDATE: 1209 424bd9b9017aa2c507510da67e14e9a87c2fdd11

VERDICT: ACCEPT

## Scope and method

Report-only independent exact review. The author clone was not accessed
(isolation rule: nothing outside this directory). The review used the
coordinator-supplied exact snapshot in this clone:
`.tmp/review/author-1209/` (`PATCH.diff`, 760 lines;
`grammatik/Grammatik/X86/HwLockFetch.lean`, 657 lines;
`MUSE-REPORT-1209.md`; `BUILD-EVIDENCE.json`; `OWNER-TASK.md`)
with pin `SNAPSHOT.json`: head
`424bd9b9017aa2c507510da67e14e9a87c2fdd11`, base `988d75ef`,
files exactly `MUSE-REPORT-1209.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/HwLockFetch.lean`, clean tree.
The full candidate source was read via the snapshot diff. This clone's
own tree was not modified except for this report.

## Checks performed

- Forbidden tokens: no `sorry`, no `admit` tactic (remaining grep hits
  are English prose "admit/admitted"), no `axiom` declaration,
  no `native_decide`, no `sorryAx`, no `unsafe`, no `split_ifs`,
  no `norm_num`/`ring_nf`. No `Prop`-typed premises, no `intro _`
  or `have _ :=` discards.
- `#print axioms`: one block per main theorem (13 lines); build
  evidence shows `propext` (+ `Quot.sound` where case analysis is
  used). Standard set.
- File scope: `grammatik/Grammatik.lean` diff is exactly one added
  import line (`import Grammatik.X86.HwLockFetch`); everything else
  is the one new file plus the author report. No existing theorem
  touched, weakened, or duplicated.
- Lifting, not copying: `hwLockFetch m c := lockFetch
  (lockMaschineVonHw m c)` reuses the 662 fetch verbatim
  (`hwLockFetch_aus_projektion` is `rfl`); `hwLockFetchSchritt`
  admits only through the 1119 parsed plug `hwLockSchritt`;
  discipline via accepted `decodeLockExt_aelter`; refusal and run
  pins rewrite to accepted 1119 witness lemmas
  (`hwLockWit_nach1_wort/rax/...`, `hwLock_puffer_bleibt_verweigert`,
  `hwLock_mfence_ohne_sse2_verweigert`,
  `hwLockSchritt_verweigert_bei`,
  `hwLock_unaligned_bleibt_verweigert`). No second fetch model,
  no second decoder, no caller-supplied decoded value on the trust
  path (`adapterLockFetch : HwAdapter Unit`).
- Premise use: spot-checked every theorem; each hypothesis (`h`,
  `hff`, `hs`, `hwf`, `hf`, the `Unit` token via the step
  hypothesis) is consumed by its proof. The general exact-agreement
  equation `hwLockFetchSchritt_ohne_split` (fetched step = parsed
  plug step off-split) plus the run equality `hwLockFetchWit_nach1`
  (fetched step = `hwLockWitNach1`) with transfer of word, rax,
  foreign buffer, and both TSO views satisfy the
  exact-agreement requirement.
- Planted refusals really refuse: split word at 8188 refuses the
  fetched step while the parsed plug would admit it (strictness
  pin); aligned 8192 never splits; 32-bit (no REX.W), 16-bit
  (0x66), and mod=0 shapes have no fetched decode (`by decide`)
  and refuse the step; register-#UD, pending own store, missing
  SSE2, unreadable word, and misaligned base refuse on the fetched
  path. The 662-accepted 10-byte SIB shape (base rsp) dispatches
  and moves the word 10 to 15, with no-shadowing decided, not
  assumed.
- Witness non-degeneracy: `hwLockFetch_zeuge` joins fetch pin,
  core-0 word 10 to 15 with rax 10, owner-only forwarding
  (owner sees 99, foreign core sees 0), post-drain core-1 word 15
  to 22 with rax 15, `HwWf`, the SIB run, and all eight refusal
  pins. Two cores, memory-changing steps on both, foreign buffered
  store visible to owner only. Non-degenerate.
- Silicon: no new encoding/fault/ordering claim beyond the accepted
  662 rows (cited Intel SDM 325462-093US Vol. 2A/2B/2D rows in
  CUTS). The two extras are stated NAMED ASSUMPTIONS: 64-byte
  lines (`cacheLinie`) and split-crossing as admission refusal
  (no bus transaction, no #AC state, no timing). Narrower widths
  are refused at the decoder because 662 rows only the 64-bit
  word forms; the SIB form 662 accepts is run. The author honestly
  records not re-verifying the SDM Vol. 3A split-lock text in this
  lane; the assumption is stated, not cited. Acceptable per task
  ("stated refusal or a named assumption").
- CUTS honest: no hardware correspondence beyond 662
  self-consistency, no W/GX refinement, no timing/progress, no
  source/checker/goal change. No claim exceeds the proof.

## Builds

- Candidate evidence (`BUILD-EVIDENCE.json`): `./lean-probe
  grammatik/Grammatik/X86/HwLockFetch.lean` == 0 error(s);
  `./lean-bau` "Build completed successfully (640 jobs)" at the
  pinned commit.
- Reviewer baseline in this clone (candidate not applied here;
  own-only constraint): `./lean-bau` ->
  `Build completed successfully (641 jobs).` (one more module than
  the candidate base from later merges; base tree green, exit 0,
  0 error lines).

## Remarks on the task

Nothing in the task statement was found to be wrong. The task's
"narrower widths ... that LockedInstructionExecution accepts" is
vacuous for widths (662 rows only 64-bit word forms), and the
candidate correctly refuses them with closed `decide` pins while
running the accepted SIB addressing mode.

## Open items

None for this candidate. Integration (merge gate) remains the
coordinator's business, including the mechanical sorry-scan and
the exact-candidate check at merge time.
