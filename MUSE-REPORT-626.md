# MUSE-REPORT-626: FloatEntryState entry control-state admission bridge

## Task

Lane 626 (direct-source closure): connect actual ScalarFloat
`FpZustand`/MXCSR-valid profile, EntryState/FeatureProfile and decoded
floating operations. Model the bounded target entry control-state
admission/establishment contract on existing state: MXCSR word validity
and preservation across actual admitted FP steps; refuse FTZ/DAZ,
non-nearest rounding and unsupported exception/control encodings. No
extra x87/OS runtime semantics. Record establishment from entry bytes
OPEN where the accepted vocabulary cannot execute control-word
load/store. Produce a memory-changing admitted execution plus source
surrounding table-write witness. Hosted and freestanding entry as
generic profiles.

## What was done

New module `grammatik/Grammatik/X86/FloatEntryState.lean` (556 lines)
plus one additive import line in `grammatik/Grammatik.lean`. No existing
file was otherwise touched; no new executor, decoder, IR, or
source/checker/emitter change.

New definitions (3):

- `eintrittFp (z : EintrittZustand) : FPKontext` — the entry's FP
  context is the entry state's own MXCSR word as data. Software
  establishment is ordinary movement of this word; no OS/hardware
  switch semantics is claimed.
- `zeugenEintrittFpHosted`, `zeugenEintrittFpMetall : EintrittZustand`
  — hosted (IF set) and freestanding (IF clear, no guard owed) entry
  control states sharing one discipline: XMM touched, save validated,
  reset word `0x1F80`. Generic profiles; no libc/Linux content.

New theorems (30):

- §0: `eintrittFp_profil` — entry-word-as-context meets `fpEintritt`
  exactly when `mxcsrGueltig` holds (`rfl`).
- §1 word validity: `mxcsrGueltig_zerlegt` (admission implies each leg:
  RNE, FTZ off, DAZ off, all masks set); `mxcsrReset_rne`;
  `mxcsr_runde_hoch_verweigert` (RC=10 `0x5F80`),
  `mxcsr_runde_schnitt_verweigert` (RC=11 `0x7F80`),
  `mxcsr_falle_verweigert` (trap-on-exception `0x1F00`),
  `mxcsr_maske_null_verweigert` (`0x1D80`). RC=01, FTZ, DAZ and one
  mask row already existed and are reused, not duplicated.
- §2 bridge: `eintritt_mxcsr_gibt_fpEintritt` (disciplined entry word
  admits FP execution), `eintrittOk_gibt_fpEintritt` (the full entry
  predicate's control-state leg is the FP admission),
  `eintritt_gibt_bereit` (disciplined word readies `.sseDoppel`),
  `sse_zugelassen_gibt_fpEintritt` (feature admission implies the FP
  step admission).
- §3 preservation: `fpSchritt_erhaelt_fp` (all fifteen `fpSchritt`
  forms keep `t.fp`, proved arm-by-arm through the accepted step
  equations, including memory-refusal arms);
  `fpSchritt_erhaelt_fpEintritt`; `zugelassener_schritt_bleibt`;
  `fpSchritt_zugelassen_heisst` (every reached step ran under checked
  length `1..15` and a valid profile — read off the step, not
  assumed); `kein_fpSchritt_installiert` (no admitted step installs a
  control word).
- §4 entry refusals/accepts: `mxcsrOk_verweigert_ungueltig` (generic)
  plus `mxcsrOk_verweigert_ftz/daz/runde_unten/runde_hoch/
  runde_schnitt/falle`; `zeugenEintrittFpHosted_ok`,
  `zeugenEintrittFpMetall_ok`, `zeugenEintrittFpHosted_fp`,
  `zeugenEintrittFpMetall_fp`, `zeugenEintrittFp_bereit` (accepts);
  `ftz_dreiWege_verweigert` (FTZ refused at entry, feature and FP
  admission jointly, reusing `sse_verweigert_ohne_profil`).
- §5: `zeugenEintrittFpHosted_kontext` (the hosted entry establishes
  exactly the witness FP context, `rfl`); `floatEintritt_zeuge` —
  JOINT witness: admitted hosted entry, two reached admitted FP steps
  (`divsd` `1.0/+0.0 = +∞`, `movsd` store, read-back, observable byte
  change, reusing `fpZeuge_schritt1/2`, `fpZeuge_liest`,
  `fpZeuge_speicher_aendert`) beside a reached source run from
  `vertragStandort_lauf_zeuge` (table-writing call, `0` at start,
  `5` at the entry contract's actual place, `ReqAmEintritt` held) plus
  `write_read_zeuge`. No lowering between the sides is claimed.

## Checks

- `./lean-probe grammatik/Grammatik/X86/FloatEntryState.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (447 jobs).`
- Axioms: every theorem depends only on `propext` (most),
  `propext + Quot.sound` (the five §3 step theorems, inherited from
  the reused ScalarFloat equations), or the full standard triple
  `propext, Classical.choice, Quot.sound` (`floatEintritt_zeuge`,
  inherited from the source fixture). `eintrittFp` and
  `zeugenEintrittFpHosted_kontext` depend on no axioms. No `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`.
- Every premise of every new theorem is used by its proof (checked by
  hand while writing; e.g. the redundant save premise was dropped from
  `eintrittOk_gibt_fpEintritt` because `mxcsrOk` already contains it).
- Rule 13: no new theorem takes a premise universally quantifying over
  source syntax; contracts appear only at actual values. The joint
  non-degenerate witness is `floatEintritt_zeuge`.

## What remains open (also recorded in the file's CUTS)

- No FP decoder: `FpBefehl` arrives constructed; LDMXCSR/STMXCSR have
  no accepted byte form. Checked here: admission, preservation,
  no-installation. Establishment of the word from entry bytes is OPEN.
- x87/FPCR, further rounding modes beyond refusal, contraction,
  fast-math: out of scope. Sticky flags unmodelled; NaN conclusions
  class-level only (inherited gaps).
- Image/stack/guard/IF legs of full `eintrittOk` stay with
  EntryState/EntryExecution; only the control-state leg and its
  transfer are owned here.
- No lowering between the witness sides; full
  source-to-final-loaded-bytes remains OPEN.
- No concurrency (sequential `Speicher` only), no cost/timing/budget
  transfer.

## Remarks on the task

- Nothing in the task turned out to be wrong. One clarification worth
  recording: "decoded floating operations" are `FpDecodiert` values
  (checked length plus constructed form), not decoded bytes — byte
  decoding of FP forms does not exist in the accepted vocabulary, so
  the module connects constructed decoded forms, and says so in CUTS
  instead of pretending otherwise.
- Proof-engineering note: `mxcsrOk_verweigert_ungueltig` needs `simp`,
  not `rw`, to close the concrete Bool goal after substitution; the two
  `| true => rfl` branches in `fpSchritt_zugelassen_heisst` are required
  because `cases h : e` rewrites goal occurrences of `e`.
