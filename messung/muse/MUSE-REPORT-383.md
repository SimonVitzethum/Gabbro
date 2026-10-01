# MUSE-REPORT-383: Independent exact-candidate C1 review of 345 TableLayout

Lane 383, reviewer. Clone `/home/simon/Dokumente/gabbro-muse/a383`, branch `muse/383`
verified (`git rev-parse HEAD` = `f737a6f04c22dfdd9499532e0535ad119cf2e56d`,
matches review base). Owns ONLY this report; candidate staged privately
(module + additive umbrella), probed, built, then fully restored
(`git status --short` clean before writing this report).

## Candidate under review

- HEAD `c24590f71f4362e29173ad3c27ad84e2c09c5f12` (base `f737a6f0`), 3 files only:
  `grammatik/Grammatik/X86/TableLayout.lean` (new, 245 lines),
  `grammatik/Grammatik.lean` (one additive import at END, verified in PATCH),
  `MUSE-REPORT-345.md`. No checker/Spec/goal/emitter/docs/friend path touched.
- Namespace `Gabbro.Grammatik.X86`. Definitions: `feldWeite`, `typWeite`,
  `zeilenWeite`, `tabUmfang`, `TabLayout`, `legeTabellen`, `layoutFuer`,
  `alsRegion`, `eintragOk`, `paarOk`, `layoutOk`, `abschnittVon`, `hinweisOk`,
  `slotAufz`. Theorems: `hinweisOk_layoutOk`, `abschnittVon_ausr`,
  `zeugenU_schreibt`, `zeugenLayout_wert`, `zeugenLayout_ok`, `zeugenSlot_ne`,
  `ueberlapp_verweigert`, `unausgerichtet_verweigert`, `layout_zeuge` (JOINT).

## Independent verification (executed, not copied)

- `./lean-probe grammatik/Grammatik/X86/TableLayout.lean` (staged privately):
  `== 0 error(s) in the COMPLETE output`. Axioms: `[]`, `[propext]`, or
  `[propext, Quot.sound]` — inside the standard goal set.
- `./lean-bau` (staged): `== exit 0; 0 error line(s)`,
  `Build completed successfully (386 jobs)`.
- `gabbro_ziel` axiom probe: `[propext, Classical.choice, Quot.sound]` — unchanged.
- Forbidden-token grep over the candidate: only `#print axioms` lines match;
  no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `intro _`/`have _ :=`.
- Every name resolves against actual accepted sources in this clone:
  `UTab`/`UFn`/`UProg` (`Parser/Uebersetze.lean`), `Ty.bool` (`Typen.lean`),
  `Region`/`regionDisjunkt`/`ausricht`/`natAdresse` (`X86/Regionen.lean`),
  `Abschnitt`/`ausrOk` (`X86/Bild.lean`), `write64`/`read64`/`writeBytesN_hit`/
  `read64_nach_write64` (`X86/Speicher.lean`). No invented behaviour.
- No unused/Prop-typed premises; `hinweisOk_layoutOk`/`abschnittVon_ausr` unpack
  decided admission into recomputation equality + alignment (real work, not a
  renamed premise). Joint witness is non-degenerate: table `konto` (2 rows,
  `x in 0 .. 100`), writer `setze` (`schreibt = ["konto"]`), accepted layout
  `[{0, 4096, 16, 8}]`, nonempty `slotAufz`, `write64` of 42 at `natAdresse 4096`
  read back with changed byte — over canonical `Speicher` at the layout base
  inside the computed extent. Refusals are proved `decide` cases (overlap
  `[4096,4112)` vs `[4104,4120)`; base 4104 vs `aligned 4096`), not examples.
- Bounded claim is truthful: no ISA/timing/TSO/float/LOCK/gate/cost claim made;
  CUTS marks correspondence, validator soundness, width bridge, loader, and the
  shared-IR-287 consumer as OPEN/WAITING. Refusal is framed as validator
  admission, never a hardware fault. The `declOf`/`fieldRangeO`/`typAt` bypass
  (direct `UProg` read + `bools` membership test) is the same ground fact,
  justified in the author report, no admission tightened.

## Findings (one real, non-blocking; two notes)

1. FOLLOW-UP (reproduced, 0-error probe): at `ausr = 0`, `legeTabellen`
   (line 55, `none` branch) drops every table, so
   `hinweisOk zeugenU 4096 0 [] = true` for a NON-EMPTY unit — the empty layout
   passes `layoutOk` vacuously. No delivered theorem is false (nothing claims
   coverage; validator soundness is OPEN and the consumer is WAITING), so this
   is not merge-blocking, but the consumer lane needs it: exact repair is a
   coverage conjunct (`hinweis` length/tab-index cover of `u.tabellen`, or
   `Option`-threaded placement) or an explicit `ausr = 0` refusal at
   `layoutOk`/`hinweisOk` level, plus a CUTS line.
2. NOTE: `feldWeite`/`typWeite` are parallel to (not used by) `zeilenWeite`,
   and no theorem speaks about `typWeite`. Harmless; suggest wiring or removing.
3. NOTE: BUILD-EVIDENCE shows one red intermediate (`feldWeite` unknown + stray
   `end`); final state is green and was verified independently here. The joint
   witness's memory change is target-side `Speicher`, not a source `exec` run —
   disclosed in the author report and proportionate for a layout helper (source
   bridge belongs to the TSO-bridge lane).

## What remains open

Per file CUTS (accurate): source-to-target correspondence, per-access TSO
refinement, `valX86_sound`, timing, width bridge, loader/entry, globals/
statics/arenas/gates, shared-IR-287 consumer; plus finding 1 above.

## Task remark

The owner-task witness line ("memory-changing run") is satisfied target-side
with honest disclosure; demanding a full source `exec` run of a pure layout
helper would misplace the TSO-bridge lane's work. No correction to the task needed.

CANDIDATE: 345 c24590f71f4362e29173ad3c27ad84e2c09c5f12
VERDICT: ACCEPT
