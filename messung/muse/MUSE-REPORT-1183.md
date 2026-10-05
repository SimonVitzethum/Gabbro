# MUSE-REPORT-1183: Feature gating enforced per step, not by wrapper

## Task

Follow-up of lane 1135 (`HwFeatureGates`, merged): the scalar-FP
`BereitProfil` leg, the CPUID-observation leg and the silicon-absent
refusal were enforced by a wrapper (`HwTorSchritt`), not by the steps.
Build a step-level statement that reads `BereitProfil`/CPUID answers
(lifting, never editing, the accepted steps) and prove wrapper and
step-level versions agree; report as a FINDING every accepted step
that ignores the profile.

## What was done

NEW FILE `grammatik/Grammatik/X86/HwFeatureStep.lean` (683 lines),
plus one `import Grammatik.X86.HwFeatureStep` line appended to
`grammatik/Grammatik.lean`. No existing file was edited otherwise;
no accepted definition was copied or modified.

- §1 `stepExtTor`: the accepted unified step `stepExt` gated per step
  by the whole `hwTorOffen` conjunction (profile, state,
  observation); refusal otherwise. Gate equations
  (`stepExtTor_offen`, `stepExtTor_zu`) and inversions
  (`stepTor_weiter_offen`, `stepTor_weiter_schritt`).
- §2 wrapper agreement: step-level success admits through
  `adapterFeatureTor` (`stepTor_adapter_weiter`), refusal/trap admits
  nothing (`stepTor_adapter_verweigert`, `stepTor_adapter_halt`), and
  the `HwTorSchritt` admitted/refused legs coincide with the
  step-level success/closed gate (`hwStepTor_ok_iff`,
  `hwStepTor_ud_iff`).
- §3 exact agreement with the accepted evaluators, both directions:
  accepted FP/vector success under an open gate IS step-level
  (`stepTor_fp_lift`, `stepTor_vec_lift`), and step-level FP/vector
  success IS the accepted success (`stepTor_fp_aus_fpSchritt`,
  `stepTor_vec_aus_stepVector`).
- §4 profile-ignorance FINDINGS, one theorem per family:
  F1a–F1f (six families carry no feature bit: gate always open,
  wrapper/step gates add nothing) with six
  `stepTor_*_ohne_beobachtung` corollaries;
  F2a–F2g (seven of eight accepted `stepExt` arms never read
  `BereitProfil`; only the packed-integer arm does, proved by the
  `stepTor_vec_beachtet_bereit` counterexample);
  F3 (`stepTor_fp_beobachtet_haengt_ab`: the step-level FP gate reads
  observed CPUID/XCR0 answers, which no accepted step reads);
  F4 (`hwStepTor_ohne_silizium_zu`: absent silicon closes the
  step-level gate under full readiness).
- §5 `hwStepTor_wf` (well-formedness through the step level, via the
  wrapper agreement), concrete step-level equations (witness vector
  step, half-gated cores 0/1), planted step-level refusals per closed
  leg (OS state, FTZ word, absent observed bit, absent silicon), the
  closing `hwStepTor_verbindung` (step-level admission, exact
  `HwSchritt.reg` embedding, well-formedness, gate/step fault
  silence, TSO owner-only forwarding and drain with 0 becoming 42)
  and the joint 18-conjunct witness `hwStepTor_verbindung_zeuge`.
- CUTS block and `#print axioms` for 27 names; all axioms are
  `[propext, Quot.sound]` (one decide-only lemma `[propext]`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwFeatureStep.lean`:
  `== 0 error(s) in the COMPLETE output` after every addition.
- `./lean-bau`: `Build completed successfully (618 jobs).`
- `rg` for `sorry|admit|native_decide|unsafe|^axiom` in the new file:
  no hits (only benign `admits` substrings in doc comments).
- One mid-task mistake was caught and repaired honestly: I drafted a
  three-branch `cases` for the CMOVcc independence proof before
  reading `ControlCodec.lean`; `cmovSchrittBytes` is `Option`-valued,
  so the proof is two-branch like SETcc. No `sorry` was ever written
  into the file (the draft with placeholders was corrected in the
  next edit after reading the true signature).
- Two Lean idiom repairs, both without weakening: `cases h : e`
  substitutes the goal (true branch closed by `rfl`), and casing
  `HwTorSchritt` with identical from/to state indices fails
  unification, so `hwStepTor_ud_iff` forward goes through the
  accepted `hwTorSchritt_ud_klasse` lemma.

## What remains open / what is wrong in the task

- Nothing in the task statement turned out to be wrong. The premise
  "the accepted FP step ignores `BereitProfil`" is confirmed
  (F2g: `fpSchritt` takes no profile argument).
- Clarification worth keeping: the observation-leg finding is
  two-sided. Accepted steps ignore CPUID answers by TYPE (`stepExt`
  takes no `CpuOut`/XCR0 argument); the six non-FP/vector families
  additionally ignore them by VALUE at step level (gate always open,
  `*_ohne_beobachtung`); FP/vector read them only through the gate
  (`stepExtTor`), never through evaluation.
- Not claimed (see CUTS): memory-touching family forms must use the
  §3/§6 issue events, never the register plug; no source/checker/
  emitter correspondence; no per-access target-to-W/GX simulation;
  no hardware correspondence beyond self-consistency over the
  accepted producers' definitions.
