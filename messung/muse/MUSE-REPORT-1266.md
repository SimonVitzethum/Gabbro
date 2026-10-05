# MUSE-REPORT-1266: exact re-review of 1265 (AVX2 join, repair)

CANDIDATE: 1265 52652788d6c2b6445a6f47e125a4d975af527fed

Clone verified: `/home/simon/Dokumente/gabbro-muse/a1266`, branch `muse/1266`.
Reviewed input: `.tmp/review/SNAPSHOT.json` (head above, base
`c8bb42086282d1e2a7c5874a40303e7f060d3fad`, clean) via
`.tmp/review/author-1265/PATCH.diff` (1494 lines), the full
`Avx2Join.lean` snapshot (1360 lines), `OWNER-TASK.md`,
`MUSE-REPORT-1265.md` (with repair section) and `BUILD-EVIDENCE.json`
(through the repair commit). No files outside this clone were touched.
This lane adds no Lean code and changes no existing file; it owns only
this report. The previous snapshot (`e7157c4a`) is superseded and was
not approved here; every check below ran against the new head.

## What the repair changed

Integration gate failure on the old head: `import
Grammatik.X86.Avx2State failed, environment already contains
'Gabbro.Grammatik.X86.avxWitS0_wf' from Grammatik.X86.Avx2Join` — the
sibling `Avx2State` piece landed after the lane base and owns the
natural top-level witness name. Repair: the whole module now lives
under `namespace Avx2Join` (5-line comment block plus the
`namespace`/`end` lines; file 1352 -> 1360 lines). Every declaration is
now `Gabbro.Grammatik.X86.Avx2Join.*`, confirmed by the snapshot
`./lean-probe` axiom output. One intermediate repair probe failed (the
`namespace` line first landed inside a doc comment); the final probe is
0 errors. No statement, proof, or definition body changed: key theorems
(`avx2Bruecke_vor/zurueck`, `avx2Schritt_wf`, `avx2Wit_zeuge`, CUTS)
sit at exactly +6 lines with identical text, verified by reading.

## Checks performed (all on the new head)

- Diff scope: same 3 files as snapshotted, no deletions: new
  `grammatik/Grammatik/X86/Avx2Join.lean`, new `MUSE-REPORT-1265.md`,
  one added line `import Grammatik.X86.Avx2Join` in
  `grammatik/Grammatik.lean`. No existing theorem weakened or deleted.
- Banned tokens over the new file: no `sorry`, no `admit` tactic, no
  `axiom` declaration, no `native_decide`, no `unsafe`, no `split_ifs`,
  no `norm_num`/`ring_nf`, no `intro _`, no `have _ :=`.
- Axioms: snapshot evidence prints every main theorem under the new
  qualified names; all dependencies are subsets of `[propext,
  Quot.sound]` (standard). File ends with a `CUTS:` block plus
  `#print axioms` per main theorem.
- Collision closure is by construction: `...X86.Avx2Join.avxWitS0_wf`
  cannot equal the sibling top-level `...X86.avxWitS0_wf`. Residual risk
  (a sibling also opening `namespace Avx2Join`) is named by the author
  and has no evidence behind it. The author honestly notes the
  integration-tree build itself is not reproducible in-clone; the
  name argument does not need it.
- Lifting, not copying (unchanged): register evaluation applies the
  accepted `ymm*` evaluators by reference; the 32-byte store is
  definitionally the accepted `issueListe` fold; loads use 4x accepted
  `ladeAcht`; addresses use accepted `effAddr`/`ripNach`; the old-row
  cross-check reuses `stufe_avx256_verweigert`.
- Premises used: bridge theorems consume every named extra conjunct;
  32-case membership induction, plug equation and `Avx2Schritt`
  constructors all use their hypotheses (re-read, unchanged text).
- Refusals that really refuse (all `decide`, unchanged): absent gate on
  all three paths, register/memory path separation both ways, misaligned
  `vmovdqa` store, VEX.128 shape, non-VEX bytes, byte shifts and `.b64`
  arithmetic shift.
- Witness `Avx2Join.avx2Wit_zeuge` (13 conjuncts, unchanged): reached
  two-step run with lane separation, 32-entry buffered store, canonical
  memory unchanged, owner-only forwarding (core 0 sees `1`, core 1 sees
  `7`), full-word load-back, memory-changing flush (`7` to `1`).
  Non-degenerate. Gate/`#GP`/shift/VEX.128/old-row refusals beside it.
- Silicon (extracts not in this reviewer clone; verified structurally):
  the four pinned VEX rows derive correctly under Vol. 2A 2.3.5;
  aligned `#GP` at the 32-byte boundary and `#UD`-class gate refusal
  are the right classes; ordering is per-byte TSO with torn
  intermediates admitted, never whole-vector atomicity.
- No over-claim: CUTS still leaves open decoder coverage, YMM legacy
  semantics, fault taxonomy, whole-vector atomicity, W/GX simulation
  and source correspondence.

## Previous findings (re-inspected)

1. Import line still mid-file (after `Avx2Ops`), not at file end.
   Cosmetic; one line only, build green. Stands, not blocking.
2. Sibling substitutes still defined here and marked; now one sibling
   (`Avx2State`) is known landed, which confirms the repair motive but
   changes nothing in this tree. Stands, not blocking.
3. `avx2Addr` still zero-extends disp8 (line 562); silicon
   sign-extends; witness uses disp 0; recorded in CUTS. Stands, honest.
4. Bridge still conditional both ways with named conjuncts. Correct.
5. Extended step relation instead of bare `HwAdapter` (task-allowed
   alternative, documented). Unchanged.

## Build

- Own-clone `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (662 jobs)`. (Own clone holds
  the base tree, not the snapshot file.)
- Snapshot `BUILD-EVIDENCE.json` (new head): final `./lean-probe` 0
  errors with `Avx2Join`-qualified axiom output, `./lean-bau` 658 jobs
  green including the new import.

VERDICT: ACCEPT
