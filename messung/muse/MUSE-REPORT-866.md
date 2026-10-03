# MUSE-REPORT-866: dead-store rule lemma

Lane 866, clone `/home/simon/Dokumente/gabbro-muse/a866`, branch `muse/866`.
Owned files only: `grammatik/Grammatik/X86/OptDceStore.lean`,
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

New module `Grammatik.X86.OptDceStore` (~515 lines) proving the DESIGN
section 7 dead-store row over the reused canonical vocabulary
(`Syntax`/`Semantik` `execStmt`/`World`, `Satz` frame lemmas, `Budget`
`seqPassesAux`, `ReferenzB` witness program, `Maschine.keinRuf`):
the back-to-back overwrite window `x = v1; x = v2` (same cell,
validator-confirmed stability, arbitrary values) reaches the same data
memory, lock state and environment as `x = v2` alone; the trace delta is
exactly the dead write event plus its pure reads.

Definitions/theorems (all `#print axioms` clean, worst case
`[propext, Classical.choice, Quot.sound]`):

- `DceStoreCert` (5 validator-decided Bools: `gleicheZelle`,
  `reinEntfernt`, `privatTraeger`, `totBestaetigt`, `keinFalleFP`),
  `dceStoreZulassen` (conjunction; refused = fall back, never a warning).
- Refusals: `dceVerweigert_geteilt` (shared/volatile/atomic: spin
  loads, publishing writes stay), `dceVerweigert_lebendig`,
  `dceVerweigert_fpFalle` (`0.0/0.0` keeps its `logik bereich`),
  `dceVerweigert_unrein`, `dceVerweigert_fremdzelle`; probes
  `probe_dceStoreZulassen_ok/_geteilt/_fpFalle` by `decide`.
- Memory core over arbitrary values: `storeSlot_absorbiert` (double
  write = single write, slots and globs), `schreibSlot_haelt` (locks
  survive the write); probes on `refD`.
- `OptDceStore_verbindung` (TARGET): 3 fault-free `.ok` step equations
  (no fault added/removed, envs unchanged), `slots`/`globs` agreement,
  `haelt` agreement, 3 exact spur equations (the delta is one private
  write event: no call/lock/shared-access event added or removed), and
  the kept value at the cell. Premise `hStabil` is the validator's
  recomputed stability, fired by admission `hz` (house style of
  `OptFoldConst`). No `ensures` derived, no fault speculated.
- Budget over reused `Budget.lean`: `dceBudget_passAbzug` (one fewer
  `seqPassesAux` pass, all op lists kept) with joint witness
  `dceBudget_passAbzug_zeuge` on `refD`.
- `OptDceStore_verbindung_zeuge` (TARGET companion): all premises
  jointly inhabited on non-degenerate `refD` (`konto[0] := 40`
  overwritten by `100`; `refEin_schreibt`, `refB_erreicht`,
  `refB_schreibt`), all ten conclusion conjuncts used.
- `CUTS` block lists exactly what is not proved (no gleit-bind window,
  no full rest-induction over arbitrary `rest` with calls into the
  universally quantified handler `R`, no level-(c) machine-work bound,
  no silicon/TSO/GX/ABI claim).

## Last check results

- `./lean-probe grammatik/Grammatik/X86/OptDceStore.lean`:
  `== 0 error(s)`, no warnings, no `sorryAx`.
- `./lean-bau`: `Build completed successfully (511 jobs)`,
  `✔ [510/511] Built Grammatik`.
- `gabbro_ziel` axioms: not re-printed (no cheap wrapper for it), but
  nothing outside the two owned files was touched and the whole grammar
  build is green, so the statement is unaffected; every new theorem is
  at or below `[propext, Classical.choice, Quot.sound]`.

## What remains open

Nothing in this lane's deliverable: file complete, witnessed, green.
Follow-ups belong to other lanes (lowering `rest`-induction, gleit-bind
DCE window, machine-work transfer, TSO/GX bridge).

## Task feedback (things I believe are worth noting)

1. The task says "Read the single accepted IR once available" — no
   accepted IR exists yet; the file is built on the real
   `Syntax`/`Semantik` fragment plus `TableLayout`-compatible plain
   slot stores, per the task's fallback. No competing IR was created.
2. Full `execEnd` equality over an arbitrary `rest` is FALSE for dead
   stores (the removed write event stays in the trace); the honest
   connection is rest-entry characterisation plus the exact trace
   delta, as proved. A reviewer asking for `=` over `execEnd` should
   read the three spur equations instead.
3. In the joint witness, `hStabil`'s admission antecedent is discharged
   by `fun _ => ...`: admission holds by `decide` and stability is
   computational (`rfl` on literal shapes), so the antecedent is
   proof-irrelevant there. The main theorem uses it load-bearing
   (`hStabil hz`).
4. Lowercase `vertrag` in binder positions is fragile (autoImplicit
   unification accident); the file uses the real `Vertrag` everywhere.
   (Sibling `OptFoldConst.lean` and `Budget.lean` use lowercase and
   compile, but a fresh file copying that style hit resolution
   failures.)
5. `rw`'s auto-`rfl` uses reducible transparency only: after rewriting
   with the world equations, an explicit `rfl` (default transparency)
   is needed to unfold `execStmt`/world projections. Several rounds
   went to this; worth knowing for Theoreme over `execStmt`.
