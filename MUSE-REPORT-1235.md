# MUSE-REPORT-1235: Profiles — multi-step control flow and relocation re-decode

Lane 1235, branch `muse/1235`, clone `/home/simon/Dokumente/gabbro-muse/a1235`.
Follow-up of lane 1173 (`PipelineProfiles.lean`).

## What was done

NEW FILE `grammatik/Grammatik/X86/PipelineProfilesReloc.lean` (≈620 lines),
plus one `import Grammatik.X86.PipelineProfilesReloc` line appended to
`grammatik/Grammatik.lean`. No other file touched. No existing theorem
deleted or weakened. `OptimizationRules.lean` / `OptimizationWitnesses.lean`
untouched. No second loader, decoder, executor, ISA, IR or source
interpreter; no new axioms; no `sorry` / `admit` / `axiom` /
`native_decide` / `unsafe`.

Checked admission `relocOk` (profile AND one applied rel32 operand at the
relocated call/jump site), for both OS profiles (`ZielProfil.gehostet`,
`.frei`):

- Split/projection: `relocOk_teile`, `relocOk_profil`, `relocOk_patch`,
  `relocOk_patch_link` (rel32 case equals the two-unit `linkPatch`).
- Operand frame legs (reuse, not re-proved): `relocOk_patch_bereich`,
  `relocOk_patch_stelle`, `relocOk_patch_rahmen` (no byte outside the
  operand changes), `relocOk_patch_laenge`.
- Two relocation closings over arbitrary admitted inputs, each carrying
  the full 12-conjunct `pipeline_profil_verbindung` (joint entry
  admission, both hooks, unchanged status, executable RIP through the
  CHECKED loaded mapping, entry stack window, image/gate/layout/binding/
  trap-suffix/float-word halves) plus re-decoded displacement, fit,
  coverage and exact window:
  `relocOk_sprung_verbindung` (jump, via `verknuepft_rel32_schliesst`),
  `relocOk_ruf_verbindung` (call, via `multi_ruf_schliesst`).
- Multi-step control flow: concrete 3-instruction straight-line program
  `relocProg` with `relocProg_gerade`; `relocOk_mehrschritt` (fetched
  run = canonical run, via `lauf_zu_laufBytes`); entry-plus-program
  composition `relocOk_eintritt_plus_programm` (via `laufBytes_add`).
- Support coverage: `relocOk_stuetz_abdeckung` (fetch succeeds → existing
  step runs, image validated) and `relocOk_stuetz_verweigert` (no fetch
  → no transition, image still validated). Every reachable support byte
  is covered or refused; nothing outside the validated image is fetched.
- Refusals, each with the admission = false: `reloc_verweigert_ohne_patch`,
  `reloc_verweigert_ohne_anfang`, `reloc_verweigert_status`,
  `reloc_verweigert_ohne_bild`.
- Poison probes: `reloc_probe_ueberlauf` (overrun patches nothing),
  `reloc_probe_aussen` (out-of-range displacement patches nothing),
  `reloc_probe_ueberlapp` (overlapping sites not decided disjoint),
  `reloc_probe_ohne_anfang`, `reloc_probe_ohne_patch`,
  `reloc_probe_status`.
- Acceptance: `reloc_gehostet_ok`, `reloc_frei_ok` (minimal image, both
  hooks, unchanged zero status, applied `+16` operand).
- Joint witness `pipeline_profil_reloc_verbindung_zeuge`: both profiles
  admitted jointly, patched window re-decoded to `jump32 +16`, real
  memory-changing write/read (`schreibLese_zeuge`), a table some function
  writes (`zeugenU_schreibt`), a reached memory-changing run through
  actual bytes (`ruf_schritt_zeuge`), the multi-step program, and planted
  refusals (missing handoff, out-of-range patch, overlap, forged opcode).

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineProfilesReloc.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (last run): `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (641 jobs).`
- `#print axioms` for all 30 names: only `propext`, `Classical.choice`,
  `Quot.sound` (subsets thereof; probes mostly `propext` or none).
  No premise has type `Prop` itself; every premise is used by its proof.

## Where the result is weaker than the task asks (stated plainly)

1. The task asks for "a correctness theorem in the style of
   `pipeline_correct_entry` (source `execBlock` result related to the
   byte-level run on the loaded image)". This file does NOT take an
   `execBlock` premise and does NOT relate a source program to bytes:
   units arrive already lowered, exactly the scoping of
   `PipelineLink.lean` ("linking only concatenates, resolves, patches
   and re-checks"). The source-correspondence leg waits on the shared IR
   (lane 287, pending); no substitute is invented. Recorded in CUTS.
2. Likewise there is no `pipeline_refuses_entry`-style theorem relating a
   failed source check to a stub run — only admission refusals
   (`reloc_verweigert_*`) with poison probes. Same reason as (1).
3. No multi-operand closing is re-proved: several operands per closing
   stay with `PipelineLinkMulti.mehrere_korrekt` (cited, with the
   `opsDisjunktB` overlap gate as this file's probe). abs64/rel8 data
   read-back stays with `multi_abs64_liest` / `multi_rel8_liest`, cited,
   not wrapped.
4. Rule 13 note: no theorem added here quantifies over program syntax
   (`Vertrag`, `Stmt`, `Endblock`, `ErgExpr`, `Expr`, `Args`) and the task
   names no `ZEUGE:` target, so inhabitation does not strictly trigger;
   the joint `_zeuge` is still provided on a non-degenerate program
   (written table + memory-changing step + reached memory-changing run).

## Apparatus note (not a content issue)

The first three `./lean-bau` runs failed spuriously while this lane's
module (runs 1–2) and then the root `Grammatik` target (run 3) reported
`failed to read file` for olean files that exist on disk (repo cache
oleans, then a toolchain `Std/.../Udiv.olean`). Nothing was changed
between runs; the fourth run built all 641 jobs green. This matches
resource contention under parallel lane load, not a proof defect: the
failing target moved each run and the file under test never changed.
No gate was weakened and no proof was retried to placate the builder.

## Open (not claimed)

Source correspondence, hardware correspondence, TSO/W/GX bridge,
budget/cost transfer, kernel behaviour beyond the named assumptions —
per CUTS. `verweigert` is absence of transition, never a termination
claim. Commits: 9d4ea828 (skeleton), 5710c683 (split+frame),
e34d1da0 (closings), 11f257ca (multi-step/coverage/refusals),
e4b04c28 (acceptance/witness/CUTS).
