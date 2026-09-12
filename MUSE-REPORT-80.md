# MUSE-REPORT-80

## Lane 80: oracle writes record access events; own-state theorem without remainder

### What was done

Changed `GutO` (`grammatik/Grammatik/Satz.lean`) so the oracle's answer world
RECORDS a write access event for every table in `D.aschreibt a` and every
global in `D.agschreibt a`, prepended to `σ.spur` in a fixed order (tables,
then globals), and proved the TARGET in the original statement, with no
remainder premise.

### Reviewer revision (conditional trace -- vacuity fix)

The first version demanded the guard trace unconditionally for every world,
so no guarded-table writer satisfied `GutO` (vacuity trap: `hO` unsatisfiable
for ordinary programs). The trace clause is now CONDITIONAL on the axiom's
lock guards being held in the calling world; elsewhere the trace is
unconstrained. Consequences:

- `axiomAntwort_gut` takes the statement guards `hd`/`hgd` plus
  `HeldGenau Λ σ.haelt` and discharges the antecedent from them (rule 12
  does not freeze it; the old signature is unprovable under the conditional
  bound). Call sites: `stmt_gut` axiomCall arm (names its `hd`/`hgd`),
  `block_gut` bindAxiom arm.
- `Block.bindAxiom` now carries `hd`/`hgd` like `Stmt.axiomCall`
  (`Syntax.lean` constructor change; 8 pattern sites updated in
  `Semantik`/`Satz`/`Geist`/`Extraktion`; no term constructions exist).
  This completes the lane-74 repair for both axiom forms.
- `EZD.axiomCall_slots_frame` uses the unconditional `Rahmen` conjunct
  directly (no `axiomAntwort_gut` needed).
- `Extraktion.execEreignis_aus_axiomCall` and
  `hmark_hcar_aus_progAus_axiomCall` take `HeldGenau` and discharge the
  antecedent at the read world (`lese_haelt`: reads preserve `haelt`);
  forwarded through the `Ziel` oracle lifters (which already hold `hΛ`).
- `axiomCallRecordsWrite` takes `HeldGenau Λ σ.haelt`, discharged the same
  way; `foreignStepKeepsSlots` forwards its `hΛ`.
- `FremdSperre.hOF` RESTORED (guarded write satisfies the conditional bound:
  vacuous where the guard is not held, events where it is) and
  `axiomCall_haelt_waechter_zeuge` RESTORED; new `gutO_bewacht_zeuge`
  packages the joint guarded-oracle inhabitation.
- `EigenZustand.oracleWriteHoldsGuard` REMOVED: unprovable as stated under
  the conditional bound (its only link to the goal needs the full
  antecedent), trivial with guard premises. Guarded writers exist.
- `O2gut` reproved under the conditional bound (antecedents vacuous on
  unguarded carriers). Both own-state witnesses kept unchanged.

### New definitions / theorems

`Satz.lean`:
- `axiomSpur tabs globs a Λ h : List (Ereignis D)` — one
  `Ereignis.zugriff t true Λ h` per declared table write, one
  `Ereignis.gzugriff g true Λ h` per declared global write, tables then
  globals. Carrier domains ride along because carrier types are not
  enumerable (same reason `stmtTraeger` takes them); `Λ`/`h` ride along
  because a recorded event must be good and consistent.
- `axiomSpur_mem`, `axiomSpur_zugriffMit`, `axiomSpur_gut`,
  `axiomSpur_write_tab`, `axiomSpur_write_glob` (member/introduction lemmas).
- `GutO` (changed): frame + held-locks clauses kept; trace clause is now
- `GutO` (changed; conditional per reviewer revision): frame + held-locks
  clauses kept unconditionally; trace clause conditional on the axiom's
  lock guards being held in `σ`:
  guards held implies `∃ tabs globs Λe, ... ∧
  spur = axiomSpur tabs globs a Λe σ.haelt ++ σ.spur`.
- `axiomAntwort_gut` (proof rewritten, `hd`/`hgd` + `HeldGenau` premises
  added): discharges the antecedent from them; the new events
  are good (`axiomSpur_gut`) and consistency is preserved
  (`konsistent_merke`). `stmt_gut`/`block_gut`/`exec_*` stand.
- `lese_haelt` (new helper): argument reads preserve the held locks.

`EigenZustand.lean` (new file, imported at the end of `Grammatik.lean`):
- `axiomCallRecordsWrite` — a fired `axiomCall` with
  `D.aschreibt a t = true` leaves `∃ ev ∈ neu, ev.traeger = some (Sum.inl t)`
  (discharges the conditional antecedent from `hd`/`hgd` + `HeldGenau`).
- `foreignStepKeepsSlots` — foreign leaf step keeps `slots t`, reusing the
  lane-56 dispatch; the oracle-write arm is discharged through the recorded
  event (`hcar` + `hNurG`). No `hNoAx`.
- `eigenzustand_nur_eigene_schritte` — the TARGET, exact fixed statement.
  (`oracleWriteHoldsGuard` was removed in the reviewer revision, see above.)
- `eigenzustand_nur_eigene_schritte_zeuge` — witness 1 on `refD`
  (carrier-free `ezdProg`, foreign `leave` step, non-degeneracy via `refEin`
  writes + `refB_pc` memory-changing run).
- `eigenzustand_axiom_zeuge` — witness 2 on the one-axiom unguarded
  declaration (`EZD.AxGegen.D2`): premises hold there too
  (`EZD.AxGegen.hNurF` over carrier-free `progF`, foreign `leave` step);
  non-degeneracy via the axiom's own memory-changing step
  (`axiomMemStep`, slot `false → true`) under the carrying `axiomProg`.

`Extraktion.lean`: `execEreignis_aus_axiomCall` rewritten (oracle prefix +
argument reads; reads name `Λ`, writes name the mark-free `Λe`; carriers via
caller-domain completeness premises `hct`/`hcg`, new; antecedent discharged
from new `HeldGenau` premise via `lese_haelt`); doc updated.
`hmark_hcar_aus_progAus_axiomCall` forwards it.
`Ziel.lean`: `pcSchritt_blatt_progAus_axiomCall`,
`pcReach_blatt_progAus_axiomCall`, `kette_mit_zeugen_orakel` take and forward
`hct`/`hcg`; the lifter forwards its `hΛ`.

`FremdSperre.lean`: `OF` emits its write event; `hOF` RESTORED (guarded
write satisfies the conditional bound) and
`axiomCall_haelt_waechter_zeuge` RESTORED; new `gutO_bewacht_zeuge`
packages the joint guarded-oracle inhabitation. Main theorem kept
unchanged. CUTS updated. (`oracleWriteHoldsGuard` was removed in the
reviewer revision, see above.)
`EigenZustandD.lean`: `Wflip2`/`O2` emit the write event; `O2gut` reproved;
`axNeu_kein_schrieb` and `axiomCall_ohne_ereignis_falsch` REMOVED (false
under the recording bound — the recorded list DOES carry the write event).
`refO`/`wGutO` (empty `Ax`) unchanged: nothing changes there, as tasked.

### Task item 2 (atom carriers)

Checked: `stmtTraeger` (`Extraktion.lean`) already lists the axiom's declared
written carriers for `axiomCall`
(`(tabs.filter (D.aschreibt a)).map .inl ++ (globs.filter ...).map .inr`),
and `stmtAtome` builds the leaf atom from `stmtTraeger ... ++ stmtOrte ...`.
No change needed; `hcar` holds for the new events through the rewritten
characterization.

### Last `./lean-bau` result

`== 0 error line(s) in the COMPLETE output`, `Build completed successfully
(51 jobs)` (after the reviewer revision; same result before it). All
`EigenZustand`/`FremdSperre` `#print axioms` depend only on
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
Text guardians: `pruefe-englisch.py` exit 0, `pruefe-kennungen.py` ALL PASS.

### What remains open

- `Block.bindAxiom` (value-returning form) now carries `hd`/`hgd` and its
  `Gut` strength flows from the rewritten `axiomAntwort_gut` (reviewer
  revision); nothing booked there anymore.
- Oracle domains are chosen per `GutO` proof; callers owe completeness
  (`hct`/`hcg`) where they extract atoms.
- Pre-existing `lean-probe`-only arity noise in `Satz.lean` (stale oleans;
  `./lean-bau` is green) was left untouched.

### Believed-wrong in the task

Nothing structural. One note: the task's suggested shape
`(O.wirkt a σ ρ).1.spur = axiomSpur a ++ σ.spur` with a domain-free
`axiomSpur a` is not expressible — carrier types are not enumerable, so the
domains must ride along (as `stmtTraeger` already does). The trace clause is
therefore existential over the oracle's own domains, plus completeness,
guard, mark-freedom, and held-locks evidence so `axiomAntwort_gut` keeps
full `Gut` strength.
