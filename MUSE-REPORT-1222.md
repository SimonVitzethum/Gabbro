# MUSE-REPORT-1222

Lane 1222: independent exact review of candidate 1221 (linking: rel8
selection convergence and fall-through coverage).
Branch `muse/1222` in clone `/home/simon/Dokumente/gabbro-muse/a1222`.

## Candidate

- Candidate under review: author lane 1221, pinned HEAD
  `bbba63d860bd3ccda92d602483ce3f233a6f353f`
  (per `.tmp/review/SNAPSHOT.json`; base `988d75ef`, `clean: true`).
  Re-review after the author's repair turn; the previous pinned HEAD
  `6c92cf74` is superseded and no longer approved here.
- Files in candidate: `MUSE-REPORT-1221.md`,
  `grammatik/Grammatik.lean` (exactly one appended line
  `import Grammatik.X86.PipelineLinkRel8`),
  `grammatik/Grammatik/X86/PipelineLinkRel8.lean` (new, 985 lines).
  Verified from `.tmp/review/author-1221/PATCH.diff`.
- Review was read-only against the in-clone snapshot
  (`.tmp/review/author-1221/`) plus `BUILD-EVIDENCE.json`; nothing
  outside this clone was touched.

## Repair-turn re-review (new pinned HEAD `bbba63d8`)

The integration gate failed the previous HEAD at
`[640/642] Building Grammatik.X86.PipelineLinkRel8` with
`failed to read file '.../Grammatik/KostenG.olean'` at the import
line — no type error, no error in any theorem. The author's repair
turn changed NO Lean code: `MUSE-REPORT-1221.md` grew 121 to 159
lines (new gate-diagnosis section); the module keeps all 42
declarations at identical line numbers (verified: same
`^theorem|^def|^inductive` inventory at lines
36–803 as in the previous review, so no insertion, deletion or moved
proof). `grammatik/Grammatik.lean` keeps the single appended import
line. I re-ran every check against the NEW snapshot:

- Banned forms: zero code hits again (only `#print axioms` lines).
  No `intro _`, no discarded premises.
- Axioms: the repair-turn `./lean-probe` re-run in `BUILD-EVIDENCE.json`
  lists all theorems on subsets of
  `[propext, Classical.choice, Quot.sound]` — unchanged, standard.
- All previous findings stand unchanged: exact scope (one new file +
  one import line), lifted-not-copied producer legs (all reused names
  still resolve in this clone's tree), six `decide`-closed refusals,
  non-degenerate `relaxLink_zeuge` (witness arithmetic rechecked:
  disp 4093 widens, disp −11 fits), correct silicon bytes
  (233/235/195 = 0xE9/0xEB/0xC3), honest CUTS with no
  hardware-correspondence or W/GX claim.
- Gate-failure assessment: the new evidence strengthens the
  apparatus-flake diagnosis rather than weakening the candidate.
  `KostenG.olean` demonstrably EXISTS in the author clone (`ls`
  succeeded in the same evidence run), yet the integration gate
  reported it unreadable; the author's local retry then failed on a
  different victim inside the installed toolchain directory
  (`Std/Data/DTreeMap/Raw/Basic.olean.private`), which lane code
  cannot influence in any way. The failure precedes typechecking
  (import/index line), the author's own `.olean` builds fine, and no
  error line in any run points at `PipelineLinkRel8.lean`. This is a
  build-cache/toolchain-read flake in the integration checkout, not
  a code defect; there was nothing for the author to repair in the
  module, and they repaired nothing there. Unblock by retrying the
  gate on a quiet machine or rebuilding the missing artifact in the
  integration checkout.

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

- `./lean-bau` in this clone, re-run for this re-review: green,
  `Build completed successfully (641 jobs).`
- The candidate module itself: `./lean-probe` 0 errors at the NEW
  pinned HEAD per the repair-turn entry in `BUILD-EVIDENCE.json`
  (probe re-run with full `#print axioms` output, standard
  subsets). Full `./lean-bau` in the
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

CANDIDATE: 1221 bbba63d860bd3ccda92d602483ce3f233a6f353f
VERDICT: ACCEPT

Candidate 1221 at `bbba63d8` is accepted as reviewed: exact scope
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
