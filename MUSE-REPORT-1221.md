# MUSE-REPORT-1221

Lane 1221: Linking — rel8 selection convergence and fall-through coverage.
Branch `muse/1221` in clone `/home/simon/Dokumente/gabbro-muse/a1221`.

## Task

Follow-up of lane 1193 (`PipelineLinkMulti.lean`). Open were rel8-selection
convergence, fall-through coverage beyond re-decoded windows, and
instructions outside jump/call/conditional sites. Deliverable: NEW FILE
`grammatik/Grammatik/X86/PipelineLinkRel8.lean` (+ one import line in
`grammatik/Grammatik.lean`), owned exclusively. Prove branch relaxation with
relocation converges (monotone widening, termination) and that the linked
bytes decode to exactly the relaxed program including fall-through windows;
overlapping sites stay refused.

## What was done

New file `grammatik/Grammatik/X86/PipelineLinkRel8.lean` (~985 lines),
reusing accepted definitions unchanged (no second decoder/loader/executor/
ISA model/IR): `MultiFeld`, `multiBytes`, `multiPatch`, `multiPatchAlle`,
`opStelle`, `opWeite`, `opsDisjunktB`, `opsDisjunktB_gilt`,
`multiPatchAlle_rahmen`/`_laenge`/`_kopf_stelle`, `disjunktStellen`,
`rel8Passt`, `rel8Byte`, `disp8Signed`, `rel8Byte_rundgang`,
`multi_rel8_liest`, `rel32Bytes`, `rel32Passt`, `fenster_sprung`,
`feld_agreement_sprung`, `ruf_schritt_zeuge`. One import line appended to
`grammatik/Grammatik.lean`. No other file touched.

Sections and exact theorem names:

1. Relaxation vocabulary: `RelaxStueck` (`fest`/`kurz`/`weit`),
   `stueckWeite` (fall-through length / 2 / 5),
   `stueckWeite_kurz_le_weit`.
2. Layout monotonicity: `stueckLE`, `progLE`, `weite_mono`,
   `adressenAux`, `adressen`, `adressenAux_laenge`, `adressenLE`,
   `adressenAux_mono` (widening never moves a laid-out address down).
3. Step: `dispAn`, `relaxSchrittAux`, `relaxSchritt`,
   `relaxSchrittAux_laenge`, `schrittWaechstAux`,
   `relaxSchritt_waechst` (steps only widen),
   `schrittFixpunkt_passtAux`, `relaxSchritt_fixpunkt_passt`
   (where the step rests, every short site fits signed-8).
4. Termination: `anzahlKurz`, `progLE_refl`, `stueckLE_trans`,
   `progLE_trans`, `progLE_anzahl`, `progLE_gleich`,
   `schrittOhneKurzAux`, `relaxSchrittOhneKurz`,
   `schrittAendertZahl`, `relaxSchrittAendertZahl`, `relaxMitFuel`,
   `relaxKonvAux`, `relaxKonvergiert` (fuelled iteration with the
   short-site count as fuel rests at a widened program where every
   short site fits).
5. Link closing: `relaxAlle_stelle` (every operand's bytes are exact
   after a disjoint multi-operand closing — head case through
   `multiPatchAlle_kopf_stelle` with decided separation, tail case
   through the IH, no diagonal needed),
   `relaxVerknuepft_korrekt` (fall-through frame + length + exact
   sites + short read-back), `relaxLang_dekodiert` (widened jump
   sites re-decode through `fenster_sprung` + `feld_agreement_sprung`).
6. Planted refusals (poison probes, all `decide`-closed):
   `relaxUeberlapp_verweigert`, `relaxUeberlauf_verweigert`,
   `relaxAussen32_verweigert`, `relaxAussen8_verweigert`,
   `relaxKeinSprung_verweigert` (`ret` at a claimed jump site decodes
   to `ret`), `relaxKurz_nicht_dekodiert` (rel8 has no decoder row).
7. Joint witness `relaxLink_zeuge`: two-site program
   `[fest 1, kurz, fest 3, kurz]` (targets 8192/4096 at base 4096)
   widens once to `[fest 1, weit, fest 3, kurz]` and rests
   (`decide`), order fact by constructors, fixed-point fit through
   `relaxSchritt_fixpunkt_passt`, two-operand closing
   `[(1, rel32 16), (5, rel8 16)]` through
   `relaxVerknuepft_korrekt` (frame, length, byte read-back),
   reached memory-changing run through the reused
   `ruf_schritt_zeuge`, plus the overlap/overrun refusals.

File ends with the `CUTS:` comment block and `#print axioms` for
every main theorem.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineLinkRel8.lean`:
  `== 0 error(s) ... exit 0`.
- `./lean-probe grammatik/Grammatik.lean` (index with the new import):
  `== 0 error(s) ... exit 0`.
- `#print axioms`: every theorem depends only on subsets of
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe` anywhere in the file (grepped).
- Every premise of every theorem is used by its proof (checked while
  writing; wrappers compose used legs).
- `./lean-bau` (full 640-module build) did NOT complete green in-turn:
  repeated attempts failed at the final `Grammatik` index step with a
  different missing artifact each time
  (`ISASelect.olean`, `HwFeatureGates.olean`, the toolchain's
  `Lean/Meta/Tactic/Grind/Propagate.ir`), plus one `failed to create
  thread` resource error. My own module compiled to
  `PipelineLinkRel8.olean` successfully inside those runs, and no
  error line in any run points at `PipelineLinkRel8.lean`. These are
  apparatus flakes in this clone's incremental build cache (missing
  artifacts for modules this lane never touched, varying per run),
  not Lean errors in the new code. Both touched files are
  probe-green. The merge gate re-runs the full build and must confirm.

## What remains open

- Full `./lean-bau` green and merge — left to the merge gate (see
  above for the apparatus flakes observed).
- Per CUTS in the file: source correspondence, `valX86_sound`,
  hardware/silicon correspondence, TSO/GX bridge, concurrency,
  budget/work transfer (other lanes); conditional-site relaxation,
  call-site re-decode beyond `feld_agreement_ruf`, abs64 sites beyond
  `multi_abs64_liest`, checked image (W^X, executed mapping via
  `mBild`), loader/entry/OS modelling.

## Remarks on the task

- Nothing in the task statement appears wrong. One scoping note: the
  task asks that "the linked bytes decode to exactly the relaxed
  program"; short (rel8) sites have no decoder row (established in
  lane 1193, re-pinned here as `relaxKurz_nicht_dekodiert`), so short
  coverage is proved as byte read-back (`disp8Signed`), and `decode`
  agreement is proved for widened jump sites. This is stated, not
  hidden, in CUTS.
- The `_zeuge` uses a post-lowering program (pieces/bytes), not a
  source-level table-writing function: units arrive already lowered
  (lane scope since `PipelineLink`). The memory-changing reached run
  is included via the reused `ruf_schritt_zeuge`.
