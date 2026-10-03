# MUSE-REPORT-1108: Binary32 fetched steps with a lifting API for the FP consumer

Lane 1108. Clone verified: `/home/simon/Dokumente/gabbro-muse/a1108`, branch
`muse/1108`. OWN ONLY respected: the only files touched are
`grammatik/Grammatik/X86/ScalarFloat32FetchedSteps.lean` (new, 672 lines) and
this report. Shared author gates kept: `./lean-probe` after every step,
`./lean-bau` green before finish, no `sorry`/`admit`/`axiom`/`native_decide`/
`unsafe`, no Prop-typed premise, every premise used, standard axioms only,
English only, no touch of `Spec.lean`, goal theorem, emitter, checker, friend
files, or any other lane's module. The unaccepted 724 module
(`ConcurrentFloatingExecution`, which does not exist in this tree) is never
imported.

## What was done

NEW module `grammatik/Grammatik/X86/ScalarFloat32FetchedSteps.lean`, importing
only the two accepted producers `Grammatik.X86.ScalarFloat32HardwareForms`
(lane 702) and `Grammatik.X86.FpControlHardwareForms` (lane 682). No new
machine, decoder row, evaluator, or IEEE arithmetic anywhere: every fact runs
an accepted equation (`s32Schritt_*`, `s32Byteschritt_weiter`,
`s32Rechne_routen`, `s32Zeuge_*`, `ldmxcsrArchOk_*`) and projects observables
out of it.

- §1 Fetched control (724-style): `S32FetchedKontrolle` (silicon `S32Hw` +
  OS `osXmm` + 682 `MxcsrProfil`), admission `s32FetchedZugelassen` (accepted
  `s32Zugelassen` AND 682 `ldmxcsrArchOk` on the raw word -- the strictest of
  both worlds, fail-closed), reset admitted, per-conjunct refusals,
  projection to both gates.
- §2 Fetched step agreement per S32Op row: `s32OpForm` maps each op to its
  fetched register form; `s32Fetched_rahmen_arith` is the shared frame
  (value + upper-96 + raw MXCSR + RIP); target `s32Fetched_schritt`
  dispatches all four rows through the accepted kernel routing.
- §3 Narrowing: `s32Narrowing_2hoch24plus1` evaluates the kernel once
  (`cvtSD2SS` of exact f64 `2^24+1` = f32 `2^24`, RNE ties-to-even, by
  `decide` with 702's `set_option`s); target `s32Fetched_narrowing`
  concludes the narrowed value IS the accepted stalled f32 value
  (`s32_stallt_bei_2hoch24`, reused) while f64 advances
  (`s32_f64_steigt_weiter`, reused) -- the 702 pattern reused, not re-proved.
- §4 Lifting interface for consumer 724 (never imported): `s32LiftForm`,
  `s32LiftWert`, `s32LiftSchritt` (admission, then fetched bytes, then the
  lifted-form check, then the accepted step -- each signature's contract in
  the §4 doc block, so a 724 shape mismatch is a loud type error), with
  `s32LiftForm_stimmt`, `s32LiftWert_routen`, `s32LiftSchritt_stimmt` and
  target `s32Fetched_lift_schnittstelle` (every signature has a proved
  provider).
- §5 Joint witness: `s32Fetched_gelenk_zeuge` instantiates every premise of
  all three targets together -- admitted control, the accepted 702 fetched
  ADDSS-plus-MOVSS-store run (real RAM change: byte `0x2002` flips
  `0x00` to `0x40`, `3.0f` reads back) and the new fetched CVTSD2SS run
  (`F2 0F 5A C0` at `0x3000`, `s32FetchedEngT/T1`, fetch proved by
  `decide`, step via the accepted row equation).
- §6 One `_zeuge` companion per target: `s32Fetched_schritt_zeuge`,
  `s32Fetched_narrowing_zeuge`, `s32Fetched_lift_schnittstelle_zeuge`.
- §7 Planted probes (all refused): `s32Sonde_engung_ohne_laenge`
  (narrowing claimed with zero decode length), `s32Sonde_klebrig_verweigert`
  (sticky-flag accumulation -- control passes through raw),
  `s32Sonde_obere_xmm_verweigert` + `s32Sonde_obere_xmm_konkret`
  (XMM-upper clobber -- general preservation plus a nonzero-upper
  `decide` instance).
- CUTS block (§7 end) lists exactly what stays OPEN; `#print axioms` for
  16 main theorems, all `propext`/`Quot.sound` or fewer (subset of the
  `gabbro_ziel` triple; `Classical.choice` never needed).

## Exact new names

Definitions: `s32FetchedSchicht`, `S32FetchedKontrolle`,
`s32FetchedZugelassen`, `s32OpForm`, `s32LiftForm`, `s32LiftWert`,
`s32LiftSchritt`, `s32FetchedEngBytes`, `s32FetchedEngMem`,
`s32FetchedEngXmm`, `s32FetchedEngKern`, `s32FetchedEngT`,
`s32FetchedEngT1`.
Theorems: `s32FetchedSchicht_ist_f32`, `s32FetchedZugelassen_reset`,
`s32FetchedZugelassen_profil`, `s32FetchedZugelassen_ohne_silizium`,
`s32FetchedZugelassen_ohne_os`, `s32FetchedZugelassen_ohne_profil`,
`s32FetchedZugelassen_arch_verweigert`, `s32Fetched_rahmen_arith`,
`s32Fetched_schritt`, `s32Narrowing_2hoch24plus1`, `s32Fetched_narrowing`,
`s32LiftForm_stimmt`, `s32LiftWert_routen`, `s32LiftSchritt_stimmt`,
`s32Fetched_lift_schnittstelle`, `s32FetchedEng_tief`, `s32FetchedEng_fp`,
`s32FetchedEng_fetch`, `s32FetchedEng_schritt`, `s32FetchedEng_tief32`,
`s32Fetched_gelenk_zeuge`, `s32Fetched_schritt_zeuge`,
`s32Fetched_narrowing_zeuge`, `s32Fetched_lift_schnittstelle_zeuge`,
`s32Sonde_engung_ohne_laenge`, `s32Sonde_klebrig_verweigert`,
`s32Sonde_obere_xmm_verweigert`, `s32Sonde_obere_xmm_konkret`.

## Check results

- `./lean-probe grammatik/Grammatik/X86/ScalarFloat32FetchedSteps.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (also prints the 16
  `#print axioms` lines, all standard).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (513 jobs).`
- `rg` for `sorry|admit(tactic)|axiom|native_decide|unsafe|intro _`:
  clean (only English words "admits"/"admitted" in comments).

## What remains open

Everything in the file's CUTS block; in particular: sticky-flag
accumulation, NaN payloads, SNaN/QNaN, DAZ/FTZ, denormal narrowing
inputs, fetched RM/integer-conversion/compare/move rows (RR arithmetic
only here), TSO tearing and the GX bridge, faults beyond explicit
refusal, timing/budget, silicon correspondence, and consumer-724 /
`decodeExt` integration (their owners' work).

## What I believe is wrong or needs a decision

1. The task's `ZEUGE` phrase "table-writing ... program" is Gabbro-source
   level; at the X86 level there are no source tables in scope. I followed
   the accepted X86 precedent (`Cvtsi2sdW64_verbindung_zeuge`): a reached
   fetched run with a real memory change plus register changes, never an
   empty run. If the merge gate mechanically requires a source-table
   witness for these theorems, that gate cannot be satisfied by any
   hardware-only module and should be scoped to source-syntax premises.
2. The umbrella `Grammatik.lean` import is deliberately NOT added: the
   lane owns only its module and report (and the sandbox denies that
   edit). The integration owner adds
   `import Grammatik.X86.ScalarFloat32FetchedSteps` at the end of
   `grammatik/Grammatik.lean`; the file is self-contained and probes
   green standalone.
3. Note for the 724 consumer: 682's `ldmxcsrArchOk` admits FTZ
   (`0x9F80`) under the modern profile while the shared `s32Eintritt`
   refuses it. My admission conjoins both, so FTZ stays refused here.
   That is the conservative reading; if 724 wants FTZ execution rather
   than refusal, that is a profile-owner decision, not something this
   lane weakens unilaterally.
