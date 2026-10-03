# MUSE-REPORT-1109: Exact review of candidate 1108 (Binary32 fetched steps + lifting API)

Lane 1109, report-only independent review. Clone verified: `/home/simon/Dokumente/gabbro-muse/a1109`,
branch `muse/1109` (via `.git/HEAD`). OWN ONLY respected: this report is the only file written;
no source, private, root, or network changes.

CANDIDATE: 1108 b58ec1acb4e73aad93c5e3671b569860b2903a4d

## Candidate identity (exact)

- Author 1108, pinned HEAD `b58ec1acb4e73aad93c5e3671b569860b2903a4d`, base `9fb1d5e9`,
  per `.tmp/review/SNAPSHOT.json` (`clean: true`).
- Files (exactly 2, matching lane-1108 OWN ONLY): `MUSE-REPORT-1108.md` and
  `grammatik/Grammatik/X86/ScalarFloat32FetchedSteps.lean` (672 lines).
- Reviewed the exact snapshot at `.tmp/review/author-1108/` (module file, `MUSE-REPORT-1108.md`,
  `OWNER-TASK.md`, `PATCH.diff`, `BUILD-EVIDENCE.json`). No other tree state was used as evidence.

## Check results (each against the task checklist)

1. **Kernel routing reuse, no duplicated float interpreter — PASS.** The module defines zero new
   float kernels, evaluators, decoder rows, or machines (grep for `def` of `fadd32/fsub32/fmul32/
   fdiv32/cvtSD2SS/bites32/bites64/muster32/muster64/rundeExakt/s32Rechne/s32Schritt/
   s32Byteschritt/s32FetchDekodiert`: no matches). Every fact runs an accepted equation:
   `s32Schritt_addssRR/subssRR/mulssRR/divssRR/cvtsd2ssRR`, `s32Byteschritt_weiter`,
   `s32Rechne_routen`, `s32Zeuge_*`, `ldmxcsrArchOk_*`. The two `decide` evaluations
   (`s32Narrowing_2hoch24plus1`, `s32FetchedEng_fetch`, `s32Sonde_obere_xmm_konkret`) execute the
   accepted kernel/decoder; they are not a new interpreter.
2. **Narrowing witness really separates f32/f64 — PASS.** `s32Narrowing_2hoch24plus1` evaluates the
   accepted kernel once (`cvtSD2SS` of exact f64 `2^24+1` = f32 `2^24`). `s32Fetched_narrowing`
   concludes the narrowed value IS the stalled f32 value (`s32_stallt_bei_2hoch24.symm`, reused)
   AND the f64 lane advances (`s32_f64_steigt_weiter`, reused: `muster64 (fadd64 …) ≠ …`). The 702
   counterexample pattern is referenced, never re-proved.
3. **XMM-upper / MXCSR preservation theorems — PASS.** `s32Fetched_rahmen_arith` proves the full
   frame (low value + upper-96 preservation + raw MXCSR passthrough `t1.fp = t.fp` + RIP advance);
   `s32Fetched_schritt` carries it per S32Op row. `s32Sonde_klebrig_verweigert` pins raw MXCSR
   passthrough (no sticky accumulation exists); `s32Sonde_obere_xmm_verweigert` plus the concrete
   nonzero `decide` instance `s32Sonde_obere_xmm_konkret` pin upper-lane preservation.
4. **Lifting interface provided AND used, no dead interface — PASS.** Named defs `s32LiftForm`,
   `s32LiftWert`, `s32LiftSchritt` each have a proved provider (`s32LiftForm_stimmt`,
   `s32LiftWert_routen`, `s32LiftSchritt_stimmt`), all three are conjoined in the target
   `s32Fetched_lift_schnittstelle`, and all three are exercised in
   `s32Fetched_lift_schnittstelle_zeuge` (form agreement, kernel value `s32_eins_plus_zwei`,
   lifted step continuing on the arithmetic run). §4 documents each signature's contract.
5. **No 724 import — PASS.** Exactly two imports, both accepted producers:
   `Grammatik.X86.ScalarFloat32HardwareForms`, `Grammatik.X86.FpControlHardwareForms`.
   `ConcurrentFloatingExecution`/724 appears only in prose as the not-imported consumer.
6. **Joint _zeuge + three probes — PASS.** `s32Fetched_gelenk_zeuge` instantiates all three targets'
   premises jointly: admitted control, the accepted 702 fetched ADDSS-plus-MOVSS-store run with
   real RAM change (`read32 … = some 0x40400000`, byte `0x2002` differs), and the new fetched
   CVTSD2SS run with the f32-vs-f64 distinction. One companion per target
   (`s32Fetched_schritt_zeuge`, `s32Fetched_narrowing_zeuge`,
   `s32Fetched_lift_schnittstelle_zeuge`). Planted probes match the owner task 1:1: narrowing
   without length (`s32Sonde_engung_ohne_laenge`), sticky accumulation
   (`s32Sonde_klebrig_verweigert`), XMM-upper clobber (`s32Sonde_obere_xmm_verweigert` +
   concrete instance). Every premise of every reviewed theorem is used by its proof (checked by
   reading each proof: no `intro _`, no unused hypothesis).
7. **CUTS honesty — PASS.** The CUTS block claims only the reused-vocabulary results and lists as
   OPEN: sticky accumulation, NaN payloads, SNaN/QNaN, DAZ/FTZ, denormal narrowing inputs,
   memory-source/integer-conversion/compare/move rows, TSO tearing and the GX bridge, faults
   beyond refusal, timing/budget, silicon correspondence, 724/`decodeExt` integration, and the
   umbrella import. No fake closure; the report's §"What remains open" matches the file.
8. **One-line import — DEFERRED BY DESIGN, documented.** The umbrella `Grammatik.lean` import is
   absent because lane-1108 OWN ONLY forbids that edit; CUTS and the author report name the
   integration owner as the adder. This is integration residue, not a candidate defect.
- **Hygiene — PASS on evidence.** No `sorry`/`admit(tactic)`/`axiom`/`native_decide`/`unsafe`
  (grep hits are only English "admitted" in comments); no Prop-typed premise; English prose with
  project-convention German identifiers; `#print axioms` for all 16 main theorems, all standard
  (`propext`/`Quot.sound` or fewer, subset of the `gabbro_ziel` triple) per BUILD-EVIDENCE.
  Final `./lean-probe`: `== 0 error(s) … exit 0`; final `./lean-bau`: `== exit 0 … Build completed
  successfully (513 jobs)` (BUILD-EVIDENCE.json; one intermediate 1-error probe during development
  is shown and then fixed — honest incremental evidence).

## Decision

VERDICT: ACCEPT

Candidate 1108 at `b58ec1acb4e73aad93c5e3671b569860b2903a4d` is accepted as reviewed: all three
targets (`s32Fetched_schritt`, `s32Fetched_narrowing`, `s32Fetched_lift_schnittstelle`) are proved
over reused accepted vocabulary with the joint witness, per-target witnesses, and the three
required refused probes; no unsupported premise, no weakened guarantee, no fake closure.

## New definitions/theorems by lane 1109

None — report-only review lane. No Lean file was added or edited.

## Last `./lean-bau` result line

Not re-run in this clone: the candidate module lives only in the author-1108 snapshot, and this
lane owns only the report (adding the module here to rebuild it would violate OWN ONLY). The
candidate's build evidence is taken from `.tmp/review/author-1108/BUILD-EVIDENCE.json`:
`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully
(513 jobs).` My own commit touches only this report, so no Lean build state changes.

## What remains open

Per the candidate CUTS (sticky flags, NaN discipline, DAZ/FTZ, further fetched rows, TSO/GX,
faults, timing, silicon, consumer-724 integration) plus the one-line umbrella import for the
integration owner at merge time.

## Notes on the task (non-blocking)

1. The `ZEUGE` "table-writing program" phrasing is Gabbro-source level; at the X86 level there are
   no source tables in scope. The candidate follows the accepted X86 precedent (reached fetched
   runs with a real memory change plus register changes, never an empty run) and says so openly
   in report item 1. If the merge gate mechanically requires a source-table witness, it should be
   scoped to source-syntax premises; no hardware-only module could satisfy it otherwise.
2. `#print axioms` is absent for five witness helpers (`s32FetchedEng_tief/fp/fetch/schritt/
   tief32`) and the `decide`-only `s32Sonde_obere_xmm_konkret` (axiom-free by construction).
   Observation only — the requirement targets main theorems, all 16 of which print standard axioms.
