# MUSE-REPORT-894: Optimiser rule — call-argument selection rule (repair of review 1044)

## What was done

Repaired `grammatik/Grammatik/X86/OptCallArgSel.lean` per independent
review MUSE-REPORT-1044 (verdict REPAIR, findings R1-R3). No other files
touched (`grammatik/Grammatik.lean` import unchanged). Built in small
pieces through `./lean-probe`, one section at a time.

- **R1 (load-bearing): placement connected to the call.** New §3 adds the
  recomputable integer projection `wertInt` (number out of an
  integer-typed value) and `envInts` (integers of an evaluated argument
  environment, left to right), with lemmas `wertInt_int`,
  `envInts_cons` and probe `probe_envInts`. The TARGET
  `OptCallArgSel_verbindung` now LINKS its value list to the calls via
  `hVs : vs = envInts (evalArgs …)` / `hVs'` and DERIVES through the
  shared record: both read-back round-trips (`rw [hVs, platziere_liest]`)
  and the value agreement `envInts … = envInts …` (`rw [← hVs, ← hVs']`)
  — the `hVals`-like equality obtained through the placement, not
  assumed. The remaining `execStmt` outcome conjunct is kept as an
  explicitly CONDITIONAL congruence (assumed equal footprints `hOrte`
  and equal full evaluation `hVals`); full `evalArgs`-preservation by
  the lowering is CUT as OPEN for the lowering/validator lane. The
  report and file header no longer claim "selected call behaves like
  the source call".
- **R2 (real rewrite in the witness):** the joint witness now calls
  `einzahlen` (`refEin`, the reference function WITH an integer
  parameter) with two SYNTACTICALLY DIFFERENT argument terms —
  `argDreiLit` (widened literal `3`) versus `argDreiAdd` (widened sum
  `1 + 2`) — same value `3`, empty footprints, `vs = [3]` tied to both
  evaluations by `rfl` computation, non-trivial placement
  `[(.reg 0, 3)]`. New scaffolding: `refHeldIff` (exact held-set iff)
  and `refHpEinAt` (call-site `RufPasst`, same lock-set shape as
  `refHpLiesAt`). Non-degeneracy unchanged (`refEin_schreibt`,
  `refB_erreicht`, `refB_schreibt`, slot `0 -> 100`).
- **R3 (boundary honesty):** CUTS extended with register classes
  (one `reg` file, no int/xmm split), REX/width/flag effects, 16-byte
  entry alignment (only per-slot 8-alignment proved), convention content
  beyond one `Bool`, `maxArgs = 64` provenance (fixed constant, decided
  per-site bound check), and TSO effects of stack-slot stores.

New definition/theorem names this round: `wertInt`, `envInts`,
`wertInt_int`, `envInts_cons`, `probe_envInts`, `refHeldIff`,
`refHpEinAt`, `argDreiLit`, `argDreiAdd` (plus the reworked
`OptCallArgSel_verbindung` / `OptCallArgSel_verbindung_zeuge`).
Every premise of every new theorem is used; no `ensures` derived; no
refusal weakened; no fault speculated above its guard.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed successfully
(511 jobs)`. `./lean-probe` on the file: `0 error(s)`. Axioms: at most
`[propext, Classical.choice, Quot.sound]` (standard `gabbro_ziel` set).
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (forbidden-pattern
shape re-checked: only the words "admitted"/"admission" appear). No new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved files touched.

## What remains open (see CUTS block in the file)

Full `evalArgs`-preservation by the lowering (R1 remainder, validator
lane); byte correspondence through decoded final machine bytes; counted
per-class cost maxima; per-site spill/fence accounting; TSO/GX bridge.

## Task feedback

Nothing in the lane-894 task text is wrong. Review 1044 §7's suggestion
(a derived-rewrite requirement for optimiser-rule tasks) is sound and
is now satisfied by construction here (linked `vs`, derived round-trips,
non-identical witness pair).
