# MUSE-REPORT-868: Bound-check elimination rule

Lane 868, branch `muse/868`, clone `/home/simon/Dokumente/gabbro-muse/a868`.
Task: optimiser rule lemma for bound-check elimination (DIRECT-COMPILER-DESIGN
section 7 row "Range/bound/overflow-check elimination").

## What was done

New file `grammatik/Grammatik/X86/OptBoundElim.lean` (plus one import line in
`grammatik/Grammatik.lean`), over the reused canonical vocabulary
(`Typen`, `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`).
No source/checker/Spec/goal/emitter edits, no new numbers, no MARKE changes,
no friend-reserved files touched.

- `BoundCert` (`umfangOk`, `keinSchreiber`, `keinRufSchreiber`) and
  `boundZulassen`: the validator-decided side conditions. Local premise is
  the source extent proof AT the site (N571/N463/N506 shape, carried as the
  recomputation obligation `hLink`, conditional on admission); certificate
  shape is the local rewrite record (`BoundCert`) plus the recomputed
  analysis citation (`hLink`).
- Refusals (both DESIGN failure cases): `boundVerweigert_schreiber`
  (entry invariant inside the writer's own mutating loop),
  `boundVerweigert_ruf` (entry range across a writing call),
  `boundVerweigert_umfang` (missing extent proof); probes
  `probe_boundZulassen_ok/_schreiber/_ruf`.
- `boundWeiter_wert` + `probe_boundWeiter`: widening keeps the value.
- `OptBoundElim_verbindung`: CONNECTION over arbitrary values at a
  `Block.narrow` window — (1) the widened value is the evaluated value,
  (2) the admitted checked window equals the unchecked continuation
  (`Zahl.weiter` value, same `execBlock` outcome: no fault added/removed,
  `sonst` dead; contracts at place, call logs, shared-access `orte`,
  IEEE float state and step budget agree via equal successor worlds).
  Nothing derives `ensures`; refusal keeps the check (falls back, never a
  warning); no faulting form is speculated above its guard.
- `OptBoundElim_verbindung_zeuge`: JOINT witness — literal `7 : .int 7 7`
  against `0..10` (`leave` else, `nil` rest) on non-degenerate `refD`
  (`refEin_schreibt`) beside reached memory-changing run `MB`
  (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptBoundElim.lean`: 0 errors.
- `./lean-bau`: `== exit 0; 0 error line(s)`, 511 jobs, `Built Grammatik`.
- Axioms: at most `[propext, Classical.choice, Quot.sound]` (standard set).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise used
  (`hz` feeds `hLink`; refusal premises drive the `simp`).

## Open / cuts (in-file CUTS block)

No hoisted entry facts, no overflow-check rule, no formal level-(c)
machine-work bound (OPEN per IR-VALIDIERUNG lane 278), no silicon/TSO-GX
correspondence beyond `eval`/`execBlock`.

## Believed-wrong: nothing in the task. The DESIGN row's two failure cases
map 1:1 onto the refusal theorems; the `hLink`-conditional pattern follows
the accepted lane-860 (`OptFoldConst`) precedent.
