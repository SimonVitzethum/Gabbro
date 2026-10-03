# MUSE-REPORT-981: Exact review of author 831 (contract-at-call closing)

Clone: `/home/simon/Dokumente/gabbro-muse/a981`, branch `muse/981`.
Owns only this file. No source or live controls touched.

## CANDIDATE / VERDICT

CANDIDATE: 831 1f7bddf78e97b30086efd3cbaaa889d16650976c
VERDICT: ACCEPT

(Base `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4`, equals this clone's HEAD;
files: `MUSE-REPORT-831.md`, `grammatik/Grammatik.lean` (+1 import),
`grammatik/Grammatik/X86/ComposeContractCall.lean` (new, 431 lines).
Acceptance is bounded; bounds in "Scope of acceptance" below.)

## What was checked

Review materials were the pinned snapshot in `.tmp/review/author-831/`
(`SNAPSHOT.json`, `OWNER-TASK.md`, `PATCH.diff`, `MUSE-REPORT-831.md`,
`BUILD-EVIDENCE.json`) plus the live base tree in this clone.
Shell execution was denied in this session, so no wrapper could be re-run;
verification is static (every reused name/signature re-checked against the
base tree) plus the author's recorded build evidence.

1. Producer reuse, by name, nothing re-proved: `callSite_vorOk`
   (`ContractSites.lean:50`), `rufAt_ok_gibt_ens` (`:85`),
   `inlinePflicht_aus_rufAt` (`:133`, a `def`, correctly used as the
   `Nonempty` witness). All three applications in
   `ComposeContractCall_verbindung` re-checked argument-by-argument against
   these signatures, including the `σ := σ.lese Λa args.orte` instantiation
   that aligns the producer's `hread` shape, and the `rw [← hread]`
   conversion of the entry half. Correct.
2. Witness well-formedness: the 17-way destructure of
   `vertragStandort_lauf_zeuge` matches its statement exactly
   (M, reach, slot-0, schreibt, 9 ghost binders, log equation, slot-5,
   entry contract, order leg); the `rueck eSetze` membership proof has the
   right two-level `mem_cons_of_mem` shape for the 3-element log prefix;
   `write_read_zeuge` (`Speicher.lean:681`) matches the final conjunct
   verbatim; `RufErreichbarG.start`, `schreibTor_ok`, `zeugenMoves_ok`,
   `zeugenStub_trap`, computable `valZeigerOk` (so `by decide` is legitimate)
   all exist. Non-degeneracy is real: table `konto` written
   (`schreibt = true`), start slot `0` vs entry slot `5` on one reached run,
   target-side `write64`/`read64` change. The planted refusal's
   `simp at hmem` closes a `rueck ∈ [eintritt …]` singleton by constructor
   mismatch. Correct.
3. Rule 3 (every premise used): traced in both theorems; all premises occur
   in the proofs. Rule 4: no `forall rho`/`forall v` quantification-away
   (contracts at actual values throughout); no `Prop`-typed premises;
   no `intro _`/`have _ :=`; no new interpreter/executor (one `Prop`
   predicate + theorems). The conclusion is a genuinely new six-way
   conjunction, not a premise renamed: entry, return and inline-discharge
   halves are each derived through a producer lemma from an outcome
   equation. The ghost, gate-Bool and reachability conjuncts are carried as
   premises, which the report and file header state openly; the refusal
   theorem proves the ghost conjunct load-bearing (uses exactly the absence
   fact plus the alleged closing). Not fake closure.
4. Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the
   candidate file (grep hits are only English "admitted"); English only;
   CUTS block + `#print axioms` for all four theorems present; import
   appended at end of `Grammatik.lean`; no diagnostic/gift/example/CLI
   numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits,
   no friend-reserved optimiser files.
5. Hardware dimension: the module adds no byte forms, decoder rows,
   REX/width/flag semantics, TSO steps or interrupt gates, so there is
   nothing to check against the Intel SDM beyond what the reused accepted
   modules already cover; gate bytes are admitted as Bools and never
   claimed to execute the source call. No invented determinism, no desired
   simulation premise, no guarantee weakened.
6. Build evidence: recorded `./lean-probe` 0 errors on the final file,
   `./lean-bau` green (509 jobs), standard axioms
   `[propext, Classical.choice, Quot.sound]` for all four theorems.

## Scope of acceptance (bounded)

Per-access refinement into W/GX, decoder coupling, `valX86_sound`,
shared IR (lane 287, no substitute invented), split holdings (Λa shared),
indirect/value-carrying call sites, cost/budget transfer, and callee-side
obligation (c) beyond `InlinePflicht` stay OPEN per the file CUTS, each
with its owning lane named. The two-fuel split (`fe`/`fr`) and
return-event-only ghost half are disclosed scoping decisions, not defects.
The task's "identical contracts without ghost events refuse" direction is
proved exactly as stated.

## Honest gaps (not defects in the candidate)

- The `gabbro_ziel`-axioms claim in BUILD-EVIDENCE has no displayed
  output (the grep pipeline errored; the redirected file was never shown).
  Risk is negligible (purely additive change cannot move existing axioms)
  but I did not independently verify it.
- Shell execution was briefly denied mid-session, so `./lean-probe` /
  `./lean-bau` could not be re-run by this reviewer: green-build reliance
  is on the author's recorded evidence plus the exact static
  re-verification above. No wrapper run was needed for this commit itself:
  it adds only this report file, no source, so the build is unaffected.
