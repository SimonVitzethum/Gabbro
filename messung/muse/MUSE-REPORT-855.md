# MUSE-REPORT-855: Composition closing — loader-bias closing

Lane 855, clone `/home/simon/Dokumente/gabbro-muse/a855`, branch `muse/855`.
Owned files only: `grammatik/Grammatik/X86/ComposeLoaderBias.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

Closed file offsets, virtual addresses, load bias and relocation operands to
the final image and executed mapping checks in one checked closing step.
Producer/consumer interface (all reused by name, nothing re-proved, no second
loader/decoder/executor/ISA/interpreter):

- Producers: `Bild.wohlgeformt/geladen/abteilFinden/ladenByte/dateiByte/effBias`,
  `LoadedExecution.wohlgeformt_wx/wohlgeformt_ausr`,
  `Relokation.rel32Passt/dispSigned`, `RelocatedExecution.PatchSite/siteStart/
  siteNext/patchSiteOk/patchSite_ziel/bildSite_ruf_dekode/fenster5/relocBytes/
  patchSiteOk_disp_aussen/aussen_verweigert/innen_verweigert`,
  `ValidatorSkeleton.transferOk`.
- The one checked closing step: `loaderBiasOk p bild bias site :=
  wohlgeformt p bild && patchSiteOk site && transferOk bild bias site.ziel`.
- Consumer: layout validator / image-coverage proof discharges one
  file-offset/virtual-address/bias/operand site by
  `ComposeLoaderBias_verbindung`, refuses by `loaderBias_disp_aussen` /
  `loaderBias_loch_verweigert`.

New definitions/theorems (all in `Grammatik/X86/ComposeLoaderBias.lean`,
namespace `Gabbro.Grammatik.X86`):

- `loaderBiasOk` with projections `loaderBiasOk_wohlgeformt`,
  `loaderBiasOk_site`, `loaderBiasOk_transfer` (axioms: `[propext]` each).
- `ComposeLoaderBias_verbindung` — generic over arbitrary admitted inputs
  (16 premises: closing-step admission, member section, effective bias,
  site formation, displacement bridge, next-RIP equation, fit, range bounds,
  stable lookup, file-backed extent, 5 exact file bytes). Concludes mapping,
  W^X, aligned biased base, virtual-address formation, loaded-window decode
  to `call32`, executed word target and Nat target (9 conjuncts).
  Axioms: `[propext, Classical.choice, Quot.sound]` (inherited from accepted
  producer lemmas).
- `loaderBias_disp_aussen`, `loaderBias_loch_verweigert` (axioms: `[propext]`).
- Witness image: `lbCode/lbZielSec/lbStapel/lbDatei/lbBild` (code `call +4091`
  at 0x1000 + listed executable target at 0x2000 + writable stack at 0x3000;
  non-degenerate: code plus writable data), `lbSite` (call +4091 to 0x2000),
  `lbD`, acceptance facts `lb_wohlgeformt/lb_patch/lb_transfer/lb_ok/lb_mem/
  lb_bias/lb_site/lb_find/lb_backed/lb_b0..lb_b4/lb_disp/lb_gleich/lb_fit/
  lb_next/lb_ziel` (all `decide` or the accepted-pattern proofs).
- `lbReg/lbZustand`, `lb_call_speichert` — reached memory-changing run
  through `byteschritt` on loaded image memory: return-address byte 5 into
  the stack slot (zero before), rip lands on listed target 0x2000
  (all `decide`, same shape as accepted `bildStore_schritt_speichert`).
- `lb_loch`, `lb_disp_verweigert` — planted refusals at the composed step.
- `ComposeLoaderBias_verbindung_zeuge` — joint witness: all 16 premises
  instantiated jointly on the witness image, all 9 connection conclusions,
  the memory-changing run, and 4 planted refusals.
  Axioms: `[propext, Classical.choice, Quot.sound]`.

Checks:

- `./lean-probe grammatik/Grammatik/X86/ComposeLoaderBias.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau`: `Build completed successfully (511 jobs).`
  (`[509/511] Built Grammatik.X86.ComposeLoaderBias`,
  `[510/511] Built Grammatik`.)
- No `sorry/admit/axiom/native_decide/unsafe` in the new file (only the
  words inside comments and `#print axioms` lines). Every premise of every
  new theorem is used by its proof. No diagnostic/gift/example/CLI numbers,
  no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files touched. `git status` shows only the two
  owned Lean paths (plus this report).

## What remains open (explicit CUTS in the file, owner named)

- No source correspondence, no hardware correspondence, no whole-binary
  theorem, no TSO/GX bridge (stays with lanes 567/573-574), no
  data-field/abs64/rel8 site classes (extension codec lanes), no patched-site
  re-decoding beyond the one call site (rel32 lane 561 owns `patchSiteOk`),
  no termination claim.

## Findings / remarks on the task

- Nothing in the task statement proved wrong. One process note: an explicit
  `write64`-unfolding execution proof in the style of `ruf_schritt_zeuge`
  failed to elaborate in this file (parse-level errors around the
  multi-line structure update), while the identical shape compiles in
  `RelocatedExecution.lean`. I replaced it with the `decide`-based
  outcome-projection shape of the accepted `bildStore_schritt_speichert`
  (`ausgangByte`/`ausgangRip`), which is green and shows the same reached
  memory-changing run. No guarantee was weakened to get green.
- `gabbro_ziel` axioms: I changed no file under `Zielsatz/` or any existing
  Lean file except the one import line in `Grammatik.lean`; the full
  511-job `lean-bau` elaborates the goal proofs without error. I did not run
  a separate `#print axioms gabbro_ziel` probe (a previous attempt to run it
  was blocked by the permission classifier), so that exact line is not
  re-verified by this lane — the merge gate's axiom check remains the
  authority.
