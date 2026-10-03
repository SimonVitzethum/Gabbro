# MUSE-REPORT-982: Exact review of author 832 (contract-at-return closing)

CANDIDATE: 832 286d28f2711e4f955cfcb1e9f45e70ec446a9ee9
VERDICT: ACCEPT (bounded: admitted-interface conjunction, not source-to-byte validation)

## Scope inspected

- Pinned snapshot: base `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4`, head `286d28f2`,
  files `MUSE-REPORT-832.md`, `grammatik/Grammatik.lean` (one import line),
  `grammatik/Grammatik/X86/ComposeContractReturn.lean` (294 lines).
- Exact sources read: `.tmp/review/SNAPSHOT.json`, `.tmp/review/author-832/OWNER-TASK.md`,
  `MUSE-REPORT-832.md`, `PATCH.diff`, full `ComposeContractReturn.lean` snapshot copy,
  `BUILD-EVIDENCE.json`, plus local reference modules `grammatik/Grammatik/X86/ContractSites.lean`,
  `EntryState.lean`, `ValidatorSkeleton.lean`, `CostSummary.lean`, `Bild.lean`,
  `grammatik/Grammatik/VertragOrtB.lean`, `ZielOrtEinfadenZeuge.lean`.
- Official local hardware references (`intel-instruction-reference.*`) are present but add no
  new byte/semantics burden here: the candidate defines no decoder, execution step, register,
  flag, memory-ordering, or gate semantics of its own.

## What the candidate does

- New Bool `rueckSchlussOk` conjoins the source return leg at actual values
  (`EnsAmRueck P f sread sret rho v`, i.e. `wahr? (eval ... (ergEnv ... v rho))`)
  with three accepted target admission Bools (`eintrittOk`, `valX86`, `kostenSummeOk`).
- TARGET `ComposeContractReturn_verbindung` is generic over arbitrary
  `D/P/f/sread/sret/rho/v/p/bild/bias/art/z/s` with four legs in and the closed Bool out.
  All four premises are used (`hEns` via `hE`, the three Bools via `simp`).
- Four projections recover each leg from a closed step; four generic refusal lemmas show one
  failing leg poisons the close; four planted concrete refusals cover each leg
  (refuting result `miniV0`, XMM-touching entry without save, mutated opcode byte,
  unbounded `retryBound` summary); `rueckSchluss_ohne_qensures` shows place holds while
  `QEnsuresB` is false on the same contract (no inferred ensures admitted).
- Joint witness `ComposeContractReturn_verbindung_zeuge` instantiates all premises together:
  real `setze` return via reused `rufAt_ok_gibt_ens_zeuge` (body outcome, `sinv` equation,
  `.ok` outcome, `schreibt () = true`, slot `0 -> 5`), reached machine run via reused
  `vertragStandort_lauf_zeuge`, closed step derived, plus byte-level `write64`/`read64`
  memory change via reused `eintritt_zeuge`. Non-degenerate on both sides.

## Checks

- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the final file; no
  `intro _` / `have _ :=` discard; contracts use actual `rho`/`v` at their place, never
  `forall rho` / `forall v`; no new interpreter/executor duplicated; every referenced
  producer name resolves in the base tree (`EnsAmRueck`, `QEnsuresB`, `miniContrP/fTrue/
  miniWelt/miniRho/miniV/miniV0`, `mini_ens_am_ort`, `mini_qensures_falsch`, `eintrittOk`,
  `zeugenEintrittHosted/zeugenEintrittXmmOhneSave/zeugenXmm_verweigert`, `valX86/valZeuge/
  valZeuge_akzeptiert/valZeuge_mutiert_verweigert`, `kostenSummeOk/blattSummary/
  blattSummary_ok`, `eD/eP/eSetze`, `rufAt_ok_gibt_ens_zeuge`,
  `vertragStandort_lauf_zeuge`, `eintritt_zeuge`, `zeugenBild`).
- Axioms/build: BUILD-EVIDENCE shows one intermediate `unsolved goals` + `sorryAx` probe,
  then final `./lean-probe ... == 0 error(s)` on every later run and full `./lean-bau`
  `Build completed successfully (509 jobs)`, `== exit 0; 0 error line(s)`. Final
  `#print axioms` for all main theorems is standard (`propext, Classical.choice,
  Quot.sound`; `decide` lemmas `propext` only). One remaining linter warning about
  unused existential binder names at line 222 is cosmetic; the witnesses are consumed by
  the final `exact`.
- Architecture: nothing new to fault at byte/REX/width/flag/operand/TSO/gate level because
  nothing new is defined there. Undefined hardware state is not invented; defined effects
  are not zeroed. The file honestly labels itself "a conjunction of checks only; execution
  evidence comes from the joint witness".
- No fake closure: the theorem does NOT link source function `f` to target image contents
  (no lowering/relocation/byte-decoding relation) and does NOT derive stops, footprints,
  lock floors, indirect calls, or TSO refinement. CUTS states exactly this (TSO + full
  source-to-final-byte closure OPEN with decoder/bridge owners; `InlinePflicht hp/hr` with
  ContractSites; indirect calls uncovered; budget leg is the admitted Bool, never a stop
  claim; guard/decode sweeps with owning lanes). Claim boundary is precise.
- Scope: only the new X86 file + one import line + report. No diagnostic/gift/example/CLI
  numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files. English throughout.

## Bounded acceptance

ACCEPT as a bounded composition step: generic admitted-interface conjunction with
projections, per-leg refusals, planted negative cases, no-inference separation, and a
joint non-degenerate reached/memory-changing witness. It must NOT be cited as
source-to-final-byte validation, per-access x86-TSO refinement, caller-side discharge,
or a stop/budget guarantee; those remain OPEN per its own CUTS.

## Reproduction note

Review-only lane: owns only this report, no source or live-control changes. Verification
is by independent inspection of the pinned PATCH plus base-tree interface resolution and
the author's queued-wrapper evidence (`lean-probe` 0 errors, `lean-bau` 509 jobs green,
standard axioms). Direct wrapper re-execution was not available from this lane's tool
permissions; no red signal was found in the complete-output evidence. If the integrator
wants a mechanical re-run, `./lean-probe grammatik/Grammatik/X86/ComposeContractReturn.lean`
and `./lean-bau` on the pinned commit are the two commands to repeat at merge.
