# MUSE-REPORT-424: FeatureProfile (finite admitted performance-feature profile)

Lane 424, continuous Lean proof reserve. Branch `muse/424` in clone
`/home/simon/Dokumente/gabbro-muse/a424`. Owned files:
`grammatik/Grammatik/X86/FeatureProfile.lean` (NEW),
`grammatik/Grammatik.lean` (one additive import line),
`MUSE-REPORT-424.md` (this file).

SUPERSEDES the earlier blocked report (commit 0f08abcf): after the
diagnostic resource repair (16 GiB virtual ceiling, lean kept at
-j2 -M4096 with the serial build lease) every queued check is green and
the source is COMMITTED in this revision.

## 1. What was done

Created `grammatik/Grammatik/X86/FeatureProfile.lean` (241 lines): a small
generic FINITE admitted performance-feature profile with proved fail-closed
selection/refusal over the existing canonical width/FP/vector interfaces
(`Typen`/`Speicher`, `Gleitprofil`, `Vektor`). No IR, no executor, no
checker/Spec/emitter change; the friend files were not touched.

Definitions: `PerfMerkmal` (skalar64, skalar32, sseDoppel, paketInt128),
`alleMerkmale`, `HwProfil` (silicon support), `BereitProfil` (MXCSR word +
OS vector state), `hat`, `bereit` (scalars need nothing; sseDoppel needs
`mxcsrGueltig` AND osXmm; paketInt128 needs osXmm), `merkmalZugelassen`
(conjunction), `waehle` (strict Option selection, no silent substitute),
`basisHw`/`basisBereit`, `merkmalBreite`, `fallback`.

Theorems (14, every premise used, no Prop-sorted premises, no
sorry/admit/axiom/native_decide/unsafe):
alleMerkmale_vollstaendig, merkmalZugelassen_heisst_beide,
waehle_verweigert_strikt, waehle_gibt_zurueck, hat_ohne_bereit_verweigert,
basis_skalar_zugelassen, sse_verweigert_ohne_profil, sse_verweigert_bei_ftz,
paket_braucht_os, skalar_braucht_silizium, skalar_fallback_breite,
fallback_verweigert_bleibt_skalar, aufnahme_kein_atomar (reuses
`vecWrite_teilt`: admission never implies atomicity), profil_skalar_zeuge
(joint non-degenerate witness: baseline admits scalar AND a nonzero
write64/read64 round-trip observably changes memory, via `write_read_zeuge`).
File ends with an explicit CUTS block and `#print axioms` for every theorem.

## 2. Verification results (all green, this revision)

- `./lean-probe grammatik/Grammatik/X86/FeatureProfile.lean`: exit 0,
  `== 0 error(s)` (log `.tmp/probe424m.log`). All axioms standard:
  twelve `[propext]`, one axiom-free, two `[propext, Quot.sound]` (via
  reused Speicher/Vektor lemmas) — subsets of
  propext/Classical.choice/Quot.sound.
- `./lean-bau`: exit 0, `Build completed successfully (393 jobs)`
  (log `.tmp/bau424e.log`).
- `gabbro_ziel` axiom check: `./lean-probe
  grammatik/Grammatik/Zielsatz/BeweisAtomar.lean` exit 0;
  `gabbro_ziel` depends on axioms
  `[propext, Classical.choice, Quot.sound]` — exactly the standard set
  (log `.tmp/probe_ziel2.log`).

## 3. Commit state

This commit lands the source (`FeatureProfile.lean`), the additive
umbrella import, and this updated report. History note: the previous
commit 0f08abcf recorded three `./lean-bau` failures at the umbrella
target (`failed to create thread`, exit 134) that reproduced on
unmodified master — environmental, resolved by the resource repair, not
by any source change (the source committed here is byte-identical in
content to the file-green version probed then, modulo the
`zugelassen` → `merkmalZugelassen` rename of §4).

## 4. Findings during the work

1. Own survey miss (repaired before landing): `MulDiv.lean` already
   defines `Gabbro.Grammatik.X86.zugelassen`; the first full build
   caught the collision. Renamed to `merkmalZugelassen` throughout
   (theorem `basis_skalar_zugelassen` keeps its longer distinct name).
   Lesson: survey ALL of `Grammatik/X86/`, not just the named interfaces.
2. Lean lesson: `simp` normalizes BitVec literals, silently breaking
   rewrite rules that mention them (`mxcsr_ftz_verweigert` became an
   unused simp arg; hypothesis `hb` stopped matching). Repaired by
   stating the general MXCSR-invalid theorem with a free word
   (`sse_verweigert_ohne_profil`) and proving the FTZ instance by
   closed `decide`.
3. A crashed check is never acceptance: every green claim above is backed
   by process exit 0, not by the error-count line (which once printed
   `0 error(s)` for an aborted run).

## 5. Believed-wrong items in the task

None. Content cuts are in the file's CUTS block: no native extension
bridge, no source lowering, no concurrency beyond sequential reuse, only
four features modelled.

