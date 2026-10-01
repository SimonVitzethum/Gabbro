# MUSE-REPORT-476: Independent exact-candidate review of 428

## Scope
Reviewed exact pinned candidate files in `.tmp/review/SNAPSHOT.json` (author 428,
HEAD `0cd16791040e459118ec50cd72c5a47ab7a0e20b`, base `0b3132b7...`, clean):
`MUSE-REPORT-428.md`, `grammatik/Grammatik.lean` (+1 additive import),
`grammatik/Grammatik/X86/ParallelMoves.lean` (new, 314 lines).
Checked PATCH, code, report claims, and BUILD-EVIDENCE.json against the actual
accepted canonical model (`Ausfuehrung.lean`) in this clone. No other clone read.
Reproduced the module through the queued wrapper in this clone by temporarily
staging the supplied file, then removed it; tree is clean before this report commit.

## Reproduction (this clone, branch muse/476)
- `cp` supplied `ParallelMoves.lean` into `grammatik/Grammatik/X86/`, then
  `./lean-probe grammatik/Grammatik/X86/ParallelMoves.lean`:
  `== 0 error(s) ... exit 0`, all 18 `#print axioms` lines emitted.
- Axiom sets match the report exactly: `moveInstr_laenge` and
  `swapMitScratch_entfaltet` depend on no axioms; every other theorem prints
  `[propext, Quot.sound]`, a subset of the goal standard. No `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe`, no `sorryAx`, no `Prop`-typed premise
  (grepped, 0 hits each).
- `decide` witnesses (`tausch_zeuge`, both negative cases) evaluated green here
  on the first attempt; the exit-134 `failed to create thread` episodes in
  BUILD-EVIDENCE are load-dependent apparatus noise, honestly documented, with
  the fix (derive `lauf_einzeln` from `lauf_kopf`, one large split only) present
  in the final file. No hidden red: final `./lean-bau` in evidence is exit 0,
  393 jobs, plus a `gabbro_ziel` probe at exactly
  `[propext, Classical.choice, Quot.sound]`.
- Restored afterwards: `grammatik/Grammatik/X86/ParallelMoves.lean` removed,
  `git status --short` clean apart from this report.

## Semantic checks (against canonical definitions, not just green output)
- Real execution, no duplicated evaluator: `moveInstr`/`expandMoves`/
  `swapMitScratch` are pure syntax maps to canonical `Decodiert`
  (`movReg64`, lengths 3/4 matching the witness shapes); every step/frame lemma
  goes through canonical `schritt`/`lauf` and reuses accepted helpers verified
  present in `Ausfuehrung.lean`: `schritt_movReg64` (+`_speicher`/`_flags`),
  `regSet_gleich`/`regSet_fremd`, `schrittRegister`, `ripNach`, `laengeOk`,
  `lauf`, `zeugeReg`/`zeugeSpeicher`/`zeugeFlags`. No second move semantics.
- Alias premises are load-bearing and correctly wired (checked by hand):
  `swap_tausch` uses `hbt` (b across save, dst=t), `Ne.symm hat` (t across
  overwrite, dst=a), `hab` (a across restore, dst=b); `swap_scratch_belegt`
  uses `symm hat`/`symm hbt`; `swap_rahmen` routes `hqt`/`hqa`/`hqb` to the
  matching destinations. No free scratch: `t` is always named, required distinct,
  and proved clobbered (`swap_scratch_belegt`: ends holding old `a`).
- Non-vacuity: `tausch_zeuge` is a JOINT reached run over one program/state:
  prefix `movImm rcx 42` + `store64 rsp rcx` changes byte at 8192 `0x00`->`42`
  (both conjuncts decided), suffix is exactly the `rax`/`rbx`-through-`r10`
  swap triple ending `(rax,rbx)=(9,7)`, `r10=7`, from distinct payloads 7 vs 9.
  So the swap theorems' `lauf ... = some` premise is jointly satisfiable;
  results are not vacuous. Every theorem's premises are used in its proof
  (read each proof; no `intro _`/`have _ :=`).
- Negative cases are genuine decided counterexamples: scratch-free
  `[rax<-rbx, rbx<-rax]` ends `(9,9)`; aliased scratch
  `swapMitScratch rax rbx rax` ends `(9,9)`; both `≠ (9,7)` conjuncts decide.
  `a=b` / `b=t` aliases have no separate counterexample, but each premise is
  used in the proofs, so the bounded claim (all three distinct required) stands.
- `lauf_kopf`/`lauf_einzeln`: generic reached-run decomposition over canonical
  `lauf` (no machine match duplicated beyond unfolding `lauf` itself); grep in
  this clone confirms no prior `lauf_kopf`/`lauf_einzeln` in `Grammatik/X86`,
  so no duplication of proved facts. Light-derivation structure
  (`lauf_einzeln` from `lauf_kopf`) matches the apparatus fix.
- Trust boundaries preserved: CUTS disclaims n-cycle scheduling, allocator/
  liveness, narrow/immediate/memory/flag-affecting forms, decoder/encoder, TSO
  bridge (explicit: no per-access atomicity), concurrency, source
  correspondence, contracts, cost/timing/progress/whole-image claims. Report
  claims only the delivered bounded 2-cycle facts. Consumer link (register
  allocation parallel-copy resolution) is stated as use, not proved integration.
  Ownership respected: exactly the 3 owned files, umbrella diff is one appended
  import line. Theorem count 18 matches the file.

## Defects / repair direction
None. No material defect found; nothing to repair. Two non-blocking notes for
the merger/owner: (1) report remark 4 on rule-13 scope (machine-level module,
no source-syntax premises) is correct; (2) the `lean::exception` crashes are
apparatus load behaviour, evidence for them is complete in BUILD-EVIDENCE.

## Verdict
ACCEPT the precisely delivered bounded claim: canonical `movReg64` edge
expansion with memory/flag frames, `lauf` head/singleton decomposition,
2-cycle swap through an explicit distinct scratch (exchange + scratch-clobber +
frame + memory/flag preservation), one joint memory-changing reached witness,
and two decided alias counterexamples. No full-compiler closure claimed or granted.

CANDIDATE: 428 0cd16791040e459118ec50cd72c5a47ab7a0e20b
VERDICT: ACCEPT
