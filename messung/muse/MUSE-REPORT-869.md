# MUSE-REPORT-869: Overflow-check elimination rule (lane 869)

## What was done

New file `grammatik/Grammatik/X86/OptOverflowElim.lean` (333 lines) plus its
register line in `grammatik/Grammatik.lean`. It proves the OPTIMIZER B3 rule
(§3.5: overflow check removed only under a proved-impossible overflow, range
entailment recomputed; certificate content per §7.2 "checks (B1–B3)" row) as a
generic rule lemma over arbitrary values with validator-decided side
conditions, over the REUSED canonical vocabulary (`Typen`, `Syntax`,
`Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`) and the ACCEPTED checker
(`X86.InvariantenOpt`: `isWahr` / `isWahrAll_sound` / `exec_pruefung_wahr`).
No accepted IR exists in-tree (IR287 still uncommitted), so per the task the
real `Syntax`/`Semantik` `Block.pruefung`/`execBlock` fragment is covered.
Modelled on the accepted `OptFoldConst.lean` (lane 860) structure.

New definitions/theorems, exactly:

- `OverflowCert` (structure: `bereichPasst`, `breiteOk`, `vorzeichenFix`,
  `keinShiftDiv`, `nurGanzzahl`), `overflowZulassen` (admission Bool).
- Refusals: `overflowVerweigert_bereich`, `overflowVerweigert_breite`,
  `overflowVerweigert_vorzeichen`, `overflowVerweigert_shiftDiv` (R4:
  signed-division-via-shift reasoning refuses), `overflowVerweigert_gleit`
  (IEEE: float-tainted windows refuse, §3.9 default REFUSE).
- Probes: `probe_overflowZulassen_ok`, `probe_overflowZulassen_shiftDiv`,
  `probe_overflowZulassen_gleit` (all `decide`).
- Per-width CF-vs-OF identity: `tragU` (unsigned carry at width `w`),
  `ueberlaufS` (signed overflow at width `w`); `tragU_kein`,
  `tragU_trifft`, `ueberlaufS_kein`, `ueberlaufS_trifft` (both directions:
  inside range clears the flag, outside sets it, so the guard is live);
  `tragU_cf_of_auseinander` (width-8 divergence: `150+50` sets no carry
  but overflows the signed byte range, so signedness must be named);
  width probes `probe_tragU_8/16/32/64`, `probe_ueberlaufS_8/64`.
- `overflowBedingung_wahr`: the recomputed entailment decides the
  two-sided literal bound check `isWahr`-true (re-run in the kernel, S1
  precedent; nothing trusted from Rust).
- `OptOverflowElim_verbindung` (TARGET): admitted (`hz`) + recomputed
  entailment (`hEnt`, conditional on admission) imply jointly (1) the
  bound check evaluates true and (2) exact `execBlock` outcome equality
  with the check-free continuation in the post-read world — same
  successor worlds, same `orte` reads, same call logs, same downstream
  budget; the `sonst` branch is unreachable, proved, not assumed. No
  `ensures` derived, no refusal weakened, no fault speculated.
- `OptOverflowElim_verbindung_zeuge` (TARGET companion): ALL premises
  jointly on `refD` (u8 check `0 ≤ 200 ≤ 255`, admitted cert,
  `Block.nil` rest, `Endblock.leave` sonst) plus non-degeneracy
  (`refEin_schreibt`, `refB_erreicht`, memory-changing `refB_schreibt`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptOverflowElim.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` at every step.
- `./lean-bau` (full project): `Build completed successfully (511 jobs)`,
  exit 0.
- `#print axioms` for every main theorem: `overflowZulassen`/`tragU`/
  `ueberlaufS`/divergence axiom-free; refusals/bridge `[propext]`;
  carry/OF-clear `[propext, Quot.sound]`; connection + witness
  `[propext, Classical.choice, Quot.sound]` — all within the standard
  `gabbro_ziel` set, no new axioms.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise used;
  English only. `gabbro_ziel` untouched: no existing proof file modified
  (only the added import register line); its axiom closure cannot move.
- Owned files only: the new module, `Grammatik.lean` (+1 line),
  this report. No diagnostic/gift/example/CLI numbers, no MARKE_EMIT
  changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files.

## What remains open (see CUTS in the file)

- Validator-side recomputation (`hEnt` producer: SSA versions +
  entailment `decide`) is a premise, not proved — the analysis is
  future work; only admitted sites refine.
- No signed-division overflow rule (R4 refusal stands), no float rule,
  no `totalCost` inequality (formal machine-work bound OPEN per
  OPTIMIZER §6.4), no TSO/GX bridge, no silicon/ABI/loader claims.

## Task notes (believed wrong or imprecise)

- "Premises from the DESIGN section 7 row": the overflow-check rule is
  OPTIMIZER §3.5 B3; §7.2 carries only the certificate-content row
  ("checks (B1–B3)"). Used both, cited exactly.
- "Read the single accepted IR": none exists in-tree; used the real
  syntax/semantics fragment as the task permits.
- Cosmetic, not mine to fix: `OptFoldConst.lean` line 256 writes
  lowercase `vertrag refD`, which only works via autoImplicit as an
  untyped hole (no such definition exists). My witness uses the real
  `Vertrag refD`; both elaborate today, but the model lane's form is
  fragile — suggest `Vertrag` there.
