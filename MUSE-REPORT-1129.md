# MUSE-REPORT-1129: Scalar FP32/FP64 and MXCSR on the coherent machine

Clone `/home/simon/Dokumente/gabbro-muse/a1129`, branch `muse/1129`
(verified before starting; 9 commits on top of master, owned files
only: `grammatik/Grammatik/X86/HwFpControl.lean` (new, 1317 lines)
plus one `import Grammatik.X86.HwFpControl` line in
`grammatik/Grammatik.lean`).

## What was done

Lifted the three accepted scalar families onto `HwMaschine`
(`HardwareExecution.lean`) per core, reusing their evaluators
unchanged (never copied, never redefined): binary32 `s32Schritt`
(`ScalarFloat32HardwareForms`), binary64 `fpSchritt` reached through
the REX decoder `fpHwDecode` (`ScalarFloatHardwareForms`), and
`mxcsrSchritt` under the modern example profile with open control
gates (`FpControlHardwareForms`). Mechanism is the second option the
task allows: an extended step relation `FpCtrlSchritt` with an exact
embedding theorem (no `HwAdapter` was added; `adapterFp668` already
covers the `FpDecodiert` register path and my f64 leg is proved to
*be* `HwSchritt.reg` through it).

1. **Step relation + wf (§§1–2).** `FpCtrlEreignis` (one register
   event per family leg plus the shared TSO byte events and explicit
   refusal); `FpCtrlSchritt` with the `HwSchritt.reg`
   memory-unchanged gate on every register leg. `fpCtrlSchritt_wf`:
   every step preserves `HwWf` (profiles untouched). Re-embedding
   projections `setKernVonFp_xmm/fp/rip` (mirroring the accepted
   `setKernVonFp_register`).
2. **Exact agreement (§3).** `fpCtrlF64_reg_ist_hwReg`: the f64 leg
   IS `HwSchritt.reg` on `.fp d` via the accepted `stepExt_fp`.
   `fpCtrlS32_addssRR_rechnet`: the s32 leg computes the accepted
   model sum. `fpCtrlMxcsrLd_installiert`: the MXCSR leg installs
   exactly the accepted four-byte word. TSO legs are the coherent
   TSO steps (`fpCtrlLade_ist_hw`, `fpCtrlGibAus_ist_hw`,
   `fpCtrlSpüle_ist_hw`).
3. **TSO word bridges (§4).** `fpCtrlAusgabe32`: a 32-bit FP store
   is four `issueByte` steps over the new `fpEintraege32`, never the
   canonical `write32` (buffer/memory/permission frames, wf;
   64-bit stores reuse `hwWortAusgabe`). New `issueListe`
   permission preservation (the foreign-buffer twin already existed
   and is reused, see below). Per-byte youngest-match facts and
   four-byte owner forwarding `fpCtrlWeiterleitung32`; entry-free
   observation reads canonical memory (`fpCtrlLade_beobachtet`).
4. **Control state (§5).** `s32Eintritt_ist_fpEintritt` (same gate);
   `s32Schritt_erhaelt_fp`: all seventeen s32 forms keep the word
   (full case analysis, the family only states per-form frames);
   RNE preserved on states and on the machine for both legs;
   reset word establishes RNE/admission through the coherent MXCSR
   load (`fpCtrlMxcsrReset_stellt_her`); the FTZ arch-vs-source
   split (`fpCtrlFtz_spalt`: loads architecturally, stays
   source-inadmissible).
5. **IEEE pins + refusals + group (§§6–7).** NaN both widths,
   signed zero both widths, no-contraction split (all cited from the
   accepted kernel). Refusals: bad length, refused profile,
   LOCK-prefixed MXCSR (`#UD`, hence no machine step), unreadable
   load, unwritable issue. New `FpGruppe32`/`FpFremdFrei32` over
   `fpFuss32` with tearing/overlap refusals and establishment
   through `fpCtrlAusgabe32`.
6. **Joint witness (§§8–11, `fpCtrl_zeuge`).** Two-core reached run:
   fetched REX `DIVSD` (`1.0/+0.0 = +inf`), register `ADDSS`
   (`1.0f32+2.0f32 = 3.0f32`, upper96 = 1 preserved), RNE preserved
   on both legs, buffered 32-bit store forwarded to the owner only
   (`0x40` vs `0x00`), four-drain install (`0` becomes
   `0x40400000`, observed from both cores), MXCSR reset install
   (admission), core-1 fetch refusal, NaN classification, wf.
   Non-degenerate: the drain changes actual shared memory while
   both cores participate (issue on core 0, loads on core 1).

## Verification (last results)

- `./lean-probe grammatik/Grammatik/X86/HwFpControl.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (one remaining
  linter warning: unused binder `s'` in an existential statement,
  harmless).
- `./lean-bau`: `Build completed successfully (601 jobs)` —
  whole project green with the new import.
- `python3 instrumente/pruefe-kein-sorry.py --rev muse/1129
  --diff master`: `0 violations` (608 files, 1 recorded allowlist
  axiom elsewhere).
- `#print axioms` for every main theorem: only `propext`,
  `Quot.sound` (subsets; no `sorryAx`, no new axiom).
- Rule 13: no theorem quantifies over source syntax (`Vertrag`,
  `Stmt`, `Endblock`, `ErgExpr`, `Expr`, `Args`); X86
  `S32Decodiert`/`FpDecodiert`/`MxcsrDec` binders follow the
  predecessor precedent (e.g. `hwPilot_weiter` over `Decodiert`).
  `fpCtrl_zeuge` jointly instantiates the run, non-degenerate
  (memory-changing drain, two participating cores).

## Finding during integration (repaired)

`lean-bau` failed once: my helper `issueListe_anderer_kern`
duplicated the accepted `ConcurrentIntegerExecution` twin
(same conclusion, different argument order). Per reuse-don't-
duplicate I deleted mine, imported
`Grammatik.X86.ConcurrentIntegerExecution`, and call the accepted
lemma. No other name in the file collides (checked every new
`def`/`theorem`/`inductive` against the tree).

## What remains open (also the file CUTS)

- No hardware correspondence: canonical subsets with
  self-consistency only; SDM-093 extracts are provenance.
- `decodeExt`/`fetchExt` carry no s32/MXCSR rows: those legs plug
  in via `FpCtrlSchritt`, not the unified dispatcher; the REX leg
  reaches bytes only through the family fetchers, and
  `fpHwCvttZugelassen` gating is cited, not re-proved, at the
  machine.
- No per-access target-to-W/GX simulation; no word atomicity
  beyond byte-drain groups; no timing/power/interrupts/faults
  beyond the carried divide halt; sticky/SNaN/DAZ/FTZ/NaN-payload
  cuts inherited from the families.

## Notes on the task (nothing believed wrong)

- The task's `*FetchedSteps` remark matches the tree: the REX
  fetcher used here is `fpHwFetchDekodiert`/`fpHwByteschritt`
  (family-level, previously unwired); s32/MXCSR fetch admission is
  proved at family level and entered the machine through the
  `FpCtrlSchritt` constructors plus the family byte steps in the
  witness.
- MXCSR leg runs under `mxcsrProfilModern`/`mxcsrSteuerungOffen`
  as explicit checked profile data (family CUTS: real silicon
  values come from the target); this is named in the file header
  and CUTS, not hidden.

## Response to independent review 1130 (reviewability REPAIR)

Review 1130 raised no content finding: its verdict REPAIR is
solely that the pinned candidate commit `6032515d` was not
reachable from the reviewer clone (`muse/1130`), so the checklist
could not run. Status from the author side, re-verified just now:

- HEAD here is exactly `6032515d21b2cd9730bc5baeaa1a197a1e392abb`
  on `muse/1129`, tree clean; `git diff master..HEAD` is exactly
  the three owned files (report + 1 import line + new module).
- `./lean-probe` on the candidate file: 0 errors, axioms
  `propext`/`Quot.sound` only. `./lean-bau` was green at this
  exact Lean tree (601 jobs); no Lean file changed since.
- The candidate itself is unchanged: there is no content fix to
  apply because no content defect was reported.

I cannot unblock the review myself: lane HARD RULES forbid
`git push`, network, and touching anything outside this clone,
so fetching my branch into the reviewer clone is not mine to do.
The unblock path is the established coordinator-side mechanism
(same one `muse-merge.sh` uses): fetch the local branch from
this clone, same machine, no network, no push — e.g. from the
coordinator, `git fetch /home/simon/Dokumente/gabbro-muse/a1129
muse/1129` into the reviewer clone — then re-run review 1130
against the pinned commit. Awaiting that re-review; no partial
work is pending on the author side.
