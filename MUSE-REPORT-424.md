# MUSE-REPORT-424: FeatureProfile (finite admitted performance-feature profile)

Lane 424, continuous Lean proof reserve. Branch `muse/424` in clone
`/home/simon/Dokumente/gabbro-muse/a424`. Owned files only:
`grammatik/Grammatik/X86/FeatureProfile.lean` (NEW, untracked),
`grammatik/Grammatik.lean` (one import line, REVERTED, see §4),
`MUSE-REPORT-424.md` (this file).

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

## 2. Verification results

- `./lean-probe grammatik/Grammatik/X86/FeatureProfile.lean`: exit 0,
  `== 0 error(s)`, twice on the final content (logs `.tmp/probe424k.log`,
  `.tmp/probe424l.log`). All axioms standard: twelve `[propext]`, one
  axiom-free, two `[propext, Quot.sound]` (via reused Speicher/Vektor
  lemmas) — subset of propext/Classical.choice/Quot.sound.
- `./lean-bau` (three runs, logs `.tmp/bau424b/c/d.log`): RED — but NOT
  because of this lane. 392/393 targets build, including FeatureProfile
  itself (its `#print axioms` lines appear in the build log); the final
  umbrella target `Grammatik` aborts with
  `lean::exception: failed to create thread` (exit 134). Control run with
  my import line stashed fails IDENTICALLY on unmodified master, so the
  failure is environmental (machine-wide thread/memory exhaustion under
  ~15 concurrent lanes; swap was 100% full), pre-existing, and outside
  this lane's control.
- `gabbro_ziel` axiom check: could not run — `./lean-probe
  grammatik/Grammatik/Zielsatz/BeweisAtomar.lean` aborts with the same
  environmental thread failure (exit 134). My module is a leaf (nothing in
  the goal proof can depend on it), so `gabbro_ziel` is unaffected by
  construction, but the standard check itself is unexecuted: NOT claimed.

## 3. Commit state (rule 8)

`./lean-bau` is not green (environmental, §2), so per HARD RULES 8 NO Lean
change is committed: the `Grammatik.lean` import line was reverted
(`git checkout -- grammatik`; tracked tree is clean). ONLY this report is
committed. The finished, file-green module stays UNTRACKED in the working
tree (`grammatik/Grammatik/X86/FeatureProfile.lean`); integration is one
import line plus a green-machine rebuild. Backup copy at
`.tmp/FeatureProfile.424.bak` (pre-rename; final content is the working file).

## 4. What remains open / findings

1. Integration: re-add `import Grammatik.X86.FeatureProfile` to
   `grammatik/Grammatik.lean`, run full `./lean-bau` + `gabbro_ziel`
   axiom check on a healthy machine.
2. Own survey miss (repaired): `MulDiv.lean` already defines
   `Gabbro.Grammatik.X86.zugelassen`; first full build caught the
   collision. Renamed to `merkmalZugelassen` throughout (theorems
   `merkmalZugelassen_heisst_beide`, `basis_skalar_zugelassen` kept).
   Lesson recorded: survey ALL of `Grammatik/X86/`, not just the named
   interfaces.
3. Lean lesson: `simp` normalizes BitVec literals, silently breaking
   rewrite rules that mention them (`mxcsr_ftz_verweigert` became an
   unused simp arg; hypothesis `hb` stopped matching). Repaired by
   stating the general MXCSR-invalid theorem with a free word
   (`sse_verweigert_ohne_profil`) and proving the FTZ instance by
   closed `decide`.
4. Intermittent `failed to create thread` crashes also hit trivially
   small files during peak memory pressure (observed on untouched
   `Typen.lean` before the wrapper mitigation); a crash is never
   acceptance — every green claim above is backed by exit 0, not by the
   error-count line.
5. Content cuts are in the file's CUTS block: no native extension
   bridge, no source lowering, no concurrency beyond sequential reuse,
   only four features modelled.

## 5. Believed-wrong items in the task

None. The task's demand (fail-closed selection, scalar fallback,
explicit CUTS, no mini-machine) is met as far as file-level verification
reaches; the missing full-build/gabbro_ziel evidence is environmental,
not a task defect.
