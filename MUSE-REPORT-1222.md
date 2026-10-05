# MUSE-REPORT-1222

Lane 1222: independent exact review of candidate 1221 (linking: rel8
selection convergence and fall-through coverage).
Branch `muse/1222` in clone `/home/simon/Dokumente/gabbro-muse/a1222`.

## Candidate

- Candidate under review: author lane 1221, pinned HEAD
  `6c92cf7406a9ca5f0fb41949d8ffc13d7676c3ac`
  (per `.tmp/review/SNAPSHOT.json`; base `988d75ef`, `clean: true`).
- Files in candidate: `MUSE-REPORT-1221.md`,
  `grammatik/Grammatik.lean` (exactly one appended line
  `import Grammatik.X86.PipelineLinkRel8`),
  `grammatik/Grammatik/X86/PipelineLinkRel8.lean` (new, 985 lines).
  Verified from `.tmp/review/author-1221/PATCH.diff`.
- Review was read-only against the in-clone snapshot
  (`.tmp/review/author-1221/`) plus `BUILD-EVIDENCE.json`; nothing
  outside this clone was touched.

## Checks performed

- Banned forms: grepped the candidate file for
  `sorry|admit|axiom|native_decide|unsafe` — zero code hits
  (only `#print axioms` lines and one doc comment mentioning the
  command). No `intro _`, no `have _ :=`, no contract parameter
  quantification.
- Axioms: per the author's final `./lean-probe` output recorded in
  `BUILD-EVIDENCE.json`, every theorem depends only on subsets of
  `[propext, Classical.choice, Quot.sound]` (standard; `Classical.choice`
  enters only through the reused `ruf_schritt_zeuge` in the joint
  witness).
- Scope: existing files untouched except the single import line; no
  edits to `OptimizationRules.lean`/`OptimizationWitnesses.lean`; no
  second decoder/loader/executor/ISA model/IR. Every reused name was
  confirmed present in this clone's tree: `multiPatchAlle`,
  `opsDisjunktB`, `multiPatchAlle_kopf_stelle`/`_rahmen`/`_laenge`,
  `disjunktStellen`, `rel8Passt`, `rel8Byte`, `disp8Signed`,
  `rel8Byte_rundgang`, `rel32Bytes`, `rel32Passt`, `fenster_sprung`,
  `feld_agreement_sprung`, `rel8Passt_grenzen`, `ruf_schritt_zeuge`.
- Premise use (spot-checked all main theorems): `weite_mono`,
  `adressenAux_mono`, `schrittWaechstAux`,
  `schrittFixpunkt_passtAux`, `progLE_trans`, `progLE_anzahl`,
  `schrittAendertZahl`, `relaxKonvAux`, `relaxAlle_stelle`,
  `relaxVerknuepft_korrekt`, `relaxLang_dekodiert` each consume every
  premise; no conclusion restates a premise.
- Planted refusals: six `decide`-closed theorems (overlap, overrun,
  rel8/rel32 range, `ret` non-site, short-form no-decode-row). They
  refuse by computation, not by added axiom.
- Witness `relaxLink_zeuge`: non-degenerate — two-site program
  `[fest 1, kurz, fest 3, kurz]` widens once
  (`[fest 1, weit, fest 3, kurz]`, `decide`), fixed-point fit via
  `relaxSchritt_fixpunkt_passt`, two-operand disjoint closing with
  byte read-back, plus a reached memory-changing run through the
  reused `ruf_schritt_zeuge` (`m.bytes ... != ...`). I rechecked the
  witness arithmetic by hand: first short site at 4097, width 2,
  disp = 8192 − 4099 = 4093 (widens, correct); after widening the
  remaining short site at 4105, disp = 4096 − 4107 = −11 (fits,
  correct). No concurrency claim, so the two-core criterion is N/A.
- Silicon facts: opcode bytes 233 = 0xE9 (near jump), 235 = 0xEB
  (short jump), 195 = 0xC3 (ret); widths 2 vs 5; signed-8/32 ranges
  through the accepted `rel8Passt`/`rel32Passt`. All match the
  architecture; nothing new is asserted about silicon beyond reusing
  the accepted rows.
- CUTS: honest. Proved scope (monotone layout, step widening,
  fixed-point fit, fuelled convergence, relaxed link closing,
  refusals, joint witness) is separated from OPEN scope (source
  correspondence, `valX86_sound`, hardware/silicon correspondence,
  TSO/GX bridge, concurrency, budget/work, conditional/call/abs64
  extensions, checked image). No hardware-correspondence or W/GX
  claim is made. The scoping note (short-site coverage as byte
  read-back since rel8 has no decoder row) is stated, not hidden.

## Build

- `./lean-bau` in this clone (HEAD `45f6238d`): green,
  `Build completed successfully (641 jobs).`
- The candidate module itself: `./lean-probe` 0 errors at the pinned
  HEAD per `BUILD-EVIDENCE.json` (final probe run lists all
  `#print axioms` with standard subsets). Full `./lean-bau` in the
  author clone did not complete green, but every recorded failure is
  apparatus, not code: missing `.olean` artifacts for untouched
  modules (`ISASelect`, `HwFeatureGates`, toolchain `.ir` file, varying
  per run) and one `failed to create thread` resource error; no error
  line in any run points at `PipelineLinkRel8.lean`. I could not
  re-probe the candidate file inside my own clone (file-copy/scratch
  operations outside the owned report are not permitted to me here);
  the merge gate re-runs the full build and must confirm.
- My clone base (`45f6238d`) is newer than the candidate base
  (`988d75ef`); no conflicts are introduced by this report-only lane
  (it owns no source file).

## Verdict

CANDIDATE: 1221 6c92cf7406a9ca5f0fb41949d8ffc13d7676c3ac
VERDICT: ACCEPT

Candidate 1221 at `6c92cf74` is accepted as reviewed: exact scope
match, standard axioms, lifted (not copied) producer legs, refusing
poison probes, non-degenerate witness, honest CUTS, no weakened
guarantee and no claim larger than the proof.

## Open / notes for the merger

- Merge-gate must confirm full `./lean-bau` green with the candidate
  applied (author-side flakes were cache/resource issues, but only a
  clean integrated build closes this).
- Nothing in the owner task or the candidate appears wrong. One
  observation, not an objection: convergence fuel equals the
  short-site count, so the bound is per-program rather than uniform;
  this matches the task (`relaxKonvergiert` as stated) and is
  correctly reflected in CUTS.
