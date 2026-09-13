# MUSE-REPORT-134 (lane 134, final audit wave)

## What I did

Read-and-probe lane. New file `grammatik/Grammatik/AuditFinal.lean`
(12 checked lemmas, no new programs or runs built) plus
`import Grammatik.AuditFinal` at the end of `grammatik/Grammatik.lean`.
Read: `dokumente/SATZKARTE.md` §11, `ZielOrtVoll.lean`,
`ZielOrtGeraet.lean`, `ZielOrtGeraetSem.lean`, `ZielOrtRegister.lean`,
`RennfreiG.lean`, `KostenG.lean` + `KostenGZeuge.lean`,
`ReferenzB.lean`, both goal witnesses, and corpus programs
`beispiele/02-geraet.gab`, `04-schleifen.gab`, `05-nebenlaeufigkeit.gab`.

## New theorems (all in `Grammatik.AuditFinal`, standard axioms only)

- `audit_vP_requires_true`, `audit_vP_ensures_true`: the `voll`
  witness gates are `.wahr` (both by `rfl`).
- `audit_geO_zeitveraenderlich_lokal`: `RegLokal geO` jointly with
  `∃ σ σ', geO.regLies () σ ≠ geO.regLies () σ'`.
- `audit_regwechsel_braucht_traeger`: differing answers on
  carrier-agreeing worlds refute `RegLokal` (every premise used).
- `audit_zugriff_nimmt`, `audit_zugriff_gibt`: lock take/release
  record no carrier access (both `rfl` over `zugriffVon`).
- `audit_lesen_kein_rennen`: if either step preserves `c`, the pair
  is no `SchreibRasse` (disjunction premise consumed by case split).
- `audit_schreibrasse_braucht_waechter`: a race names its guard.
- `audit_schleife_unter_schranke`: `9 ≤ kostenTief hP 0 2 (initF 0).1`.
- `audit_vlauf_schreibt`: `vP` reaches a machine with the slot `true`.
- `audit_geP_ensures_leser`: `geP.ensures geLeser = .var .hier`.
- `audit_gelauf_zwei_faeden`: `geP` reaches a machine with both
  `tafel` and `notiz` changed (two-threaded run).

## Verdict table (item, verdict, evidence)

| # | Item | Verdict | Evidence |
|---|---|---|---|
| 1a | `ziel_ort_voll` premises jointly satisfiable non-degenerate | PASS (weak) | `ziel_ort_voll_zeuge`: all premises jointly on `vP`; 14-step run of thread 0 with axiom memory change `false → true`. |
| 1b | `voll` witness uses `true` contracts, one moving thread | CONFIRMED GAP | `audit_vP_requires_true`, `audit_vP_ensures_true` (both `.wahr` by `rfl`); `ZielOrtVollZeuge.lean` CUTS: thread 1 never moves. No stronger joint instance exists in the tree; I did not build one (would need frame reasoning for a non-trivial contract under `KoerperGutV` plus a two-thread run — a full lane of its own). |
| 1c | `ziel_ort_geraet` has the stronger instance | PASS (new finding vs task text) | `ziel_ort_geraet_zeuge` + `audit_geP_ensures_leser` (non-trivial `ensures result`), `audit_gelauf_zwei_faeden` (two threads interleave: thread 0 reads twice with own write between, thread 1 writes `tafel`), `audit_geO_zeitveraenderlich_lokal` (memory-dependent oracle). |
| 1d | `KoerperGutV`/`KoerperGutG` over ALL oracles satisfiable for axiom-calling body with result-dependent ensures | MIXED | PASS for registers: `geLeser_lauf` proves the reader against every local oracle, locality used at the `hloc` step (own write to `notiz` leaves `geraet` carriers alone). OPEN for axioms: `KoerperGutV` quantifies over all `RahmenO` oracles with no locality (`ZielOrtVollBeweis.lean:59`); the only axiom-calling witness body (`vHaupt`) has `true` contracts. No counter-lemma: `RahmenO` still fixes the frame, so result-dependence is not obviously fatal — precise gap, not a refutation. |
| 2 | `RegLokal` satisfiable by a time-varying device | PASS | `audit_geO_zeitveraenderlich_lokal`: local yet memory-dependent. Time-variance across WRITES is the intended semantics. Complement: `audit_regwechsel_braucht_traeger` — change with NO carrier write violates `RegLokal`, so self-changing devices without a declared axiom write are outside (matches `ZielOrtGeraet.lean` CUTS; device's own axiom must write its carriers). |
| 3a | `rennfrei_g` = data-race freedom for writes | PARTIAL | PASS for guarded write/write: holder form + adjacent form with joint witness `rennfrei_g_zeuge`. |
| 3b | Reads covered? | NO (by design) | `audit_lesen_kein_rennen`: `SchreibRasse` needs two memory changes, so read/read and read/write pairs never qualify. No read/write formulation over `zugriffe` exists (`RennfreiG.lean` CUTS). |
| 3c | Non-adjacent write/write via release/acquire | NO (precise gap) | `rennfrei_g_nah` concludes adjacent steps only; no theorem with an explicit release event between the steps. `audit_zugriff_nimmt`/`audit_zugriff_gibt`: lock events are not even in the access set. What IS there: `rennfrei_g`'s holder form composes across the gap informally (next writer takes the guard only after release), but no Lean statement says it. |
| 3d | Unshared carriers, atomics, payloads | NO (by design, documented) | `audit_schreibrasse_braucht_waechter` (guard mandatory); atomics/payloads excluded by `SchreibRasse` itself; unshared = checker duty `PCUnsharedSep`. |
| 4a | `frame_schritte_beschraenkt` / `kosten_passt_deklaration` premises satisfiable, witness non-degenerate | PASS | `frame_schritte_beschraenkt_zeuge` (zP runs with memory change), `zP_kostenPasst` (`kostenPasst … = true` by `decide`); `audit_schleife_unter_schranke` (9 ≤ 18). |
| 4b | Bound holds for a looping frame; loop witness run | PASS (narrower than asked) | `frame_schritte_beschraenkt_zeuge_schleife`: `retry 1` frame, 9 own steps ≤ 18. The task text says "no loop witness run" — outdated: a `retry` run exists. What is still missing: `traverse`/`forever` reached runs (step lemma `schrittArt` covers them, `KostenGZeuge.lean` CUTS says so explicitly; no run fires `dannTrav`/`travNext` anywhere in the tree — verified by grep). |
| 5 | Rust-accepted programs runnable on G (device register / locks+call / retry-traverse) | PARTIAL (construct-level, no hand translation) | I did NOT hand-translate the three corpus programs — say so plainly. What the probes show: every construct HAS a G step rule (`dannRegLies` :1703, `dannLocks` :626, `ruf`/`rufDann` pushes, `dannRetry` :762, `wiederSchritt` :818, `dannTrav` :679, `dannAwaits` :1773, all `RufMaschineG.lean`) and all but two FIRE in reached runs: locks+call+axiom+indirect+retry+leave (`audit_vlauf_schreibt`, 14 steps), register reads + two-thread interleave (`audit_gelauf_zwei_faeden`), retry loop (`frame_schritte_beschraenkt_zeuge_schleife`). NO reached run fires `traverse` or `awaits`. So the precise statement: a checker-accepted program using `traverse` or `awaits` has step rules but zero witnessed runs — the model proves more about programs it never demonstrably runs. Stuck states (`ewig 0`, unmet `awaits`, held `locks`) take no steps and satisfy `VertragAmOrtG` vacuously per `KostenG.lean` CUTS (waiting is a scheduler assumption). |

## What remains open

1. Stronger `voll` witness (non-trivial contract + two moving threads).
2. `KoerperGutV` instance for an axiom-calling body with result-dependent
   ensures (or a refutation showing the universal over all `RahmenO`
   oracles is too strong).
3. Read/write race formulation; non-adjacent race with explicit release.
4. `traverse`/`forever`/`awaits` reached runs on G.
5. Full hand translation of corpus programs into Lean syntax.
6. Rule-13 note: none of my theorems quantifies over program syntax, so
   no `_zeuge` companions were required; the two witness-projection
   lemmas (`audit_vlauf_schreibt`, `audit_gelauf_zwei_faeden`) reuse the
   existing non-degenerate witnesses rather than weakening them.

## Build result

`./lean-bau`: `Build completed successfully (89 jobs).` (last line).
`./lean-probe grammatik/Grammatik/AuditFinal.lean`: 0 errors; all 12
theorems depend only on `[propext, Classical.choice, Quot.sound]`.

## What I believe is wrong in the task

- "The `voll` witness is known to run one thread with `true` contracts:
  build or find a stronger joint instance" — the stronger instance
  already exists for the flagship: `ziel_ort_geraet_zeuge` (non-trivial
  ensures, two threads, memory-dependent oracle). The gap is specific to
  `ziel_ort_voll`, not to the goal family.
- "The file says there is no loop witness run" — outdated for `retry`
  (`frame_schritte_beschraenkt_zeuge_schleife`); still true for
  `traverse`/`forever`.
