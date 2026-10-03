# MUSE-REPORT-865: Optimiser rule — dead code (overwrite window)

Lane 865, clone `/home/simon/Dokumente/gabbro-muse/a865`, branch `muse/865`.
Task: DESIGN section 7 DCE row as a generic Lean rule lemma with
validator-decided side conditions, preservation proofs, exact
certificate shape, and precise refusal cases.

## What was done

New file `grammatik/Grammatik/X86/OptDceDead.lean` (≈770 lines),
plus the one-line `import Grammatik.X86.OptDceDead` at the end of
`grammatik/Grammatik.lean`. Nothing else touched: no diagnostic/gift/
example/CLI numbers, no MARKE changes, no source/checker/Spec/goal/
emitter edits, no friend-reserved optimiser files.

The rule is the overwrite window `x = e1; x = e2; rest` → `x = e2;
rest` over the REAL canonical semantics (`eval`/`execBlock`), with two
validator-recomputed side conditions straight from the DESIGN row:
purity (`hRein : e1.orte = []`, no token/atomic/call/check/stop/
trap-capable FP observation) and dead-confirmed (`hTot : liest e2 x
= false`, the first write is dead). The main theorem proves
`execBlock` outcome equality, which jointly covers value, fault
(`assignVar` never faults; `e2` evaluates identically), observations
(same successor worlds/envs, hence same downstream contract reads at
their place, same call logs — the window holds no call — and no
added/removed shared access for concurrency), and shrinking
step-budget (separate cost inequality). IEEE is covered by refusal:
a dead float block can fault, exhibited, so the rule never fires
there. No `ensures` derived, no refusal weakened to a warning, no
fault speculated above its guard.

## New definitions/theorems (all in `Gabbro.Grammatik.X86`)

- `DceCert` (`orteLeer`, `zielTot`), `dceZulassen` (admission Bool).
- `dceVerweigert_orte`, `dceVerweigert_tot` + decide probes
  (`probe_dceZulassen_ok/_orte/_tot`).
- `liest` / `liestNutz` (decided local-read analysis; quantified
  bodies answer `true` = conservative refusal), `lese_nil`,
  `envSet_twice`.
- `eval_set_frisch` (frame lemma by `Expr.rec`: setting an unread
  local changes no `eval`) + `eval_set_frisch_zeuge`.
- `OptDceDead_verbindung` (TARGET) + `OptDceDead_verbindung_zeuge`.
- `dceKosten_faellt` (`kostenBlock` nonincreasing) +
  `dceKosten_faellt_zeuge`.
- `dceGleit_beispiel` (`gleitPasst (0,1) (0,1) (bruch (1,1)) = none`
  by `decide`), `dceVerweigert_gleit` (dead `gleitLit` faults with
  `logik bereich`) + `dceVerweigert_gleit_zeuge`.
- `dceSpin_beobachtet` (a shared read appends exactly one trace
  event, so `hRein` refuses spin-load removal).
- Witness components `dceE1`, `dceE2`, `dceRho`, `dceV7`,
  `dceE1_rein`, `dceE2_tot`, `dceE1_tot` (closed defs on `refD`).
- CUTS block (section 12) + `#print axioms` for every main theorem.

All witnesses are joint on non-degenerate `refD` (`einzahlen`
writes its table) beside reached run `MB` with a memory-changing
step, following the `OptFoldConst` pattern. Read but not imported
beyond need: DESIGN §7 row, `TableLayout` (layout is orthogonal to
this local rule), `CostSummary` (its `kostenSummeOk` schema is the
consumer of the section-9 inequality; budget-exhaustion timing stays
OPEN per IR-VALIDIERUNG), `InvariantenOpt` (checker pattern),
`KostenG` (imported), `CFormenI` (imported for `Var.idx`,
`Env.get_set_other` reuse).

## Check results

- `./lean-probe grammatik/Grammatik/X86/OptDceDead.lean`: `== 0
  error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (511 jobs)`.
- Axioms: every new theorem depends only on subsets of `propext`,
  `Classical.choice`, `Quot.sound` (the `gabbro_ziel` standard; full
  list in probe output). No new `axiom`, no `sorry`/`admit`/
  `native_decide`/`unsafe`.
- `gabbro_ziel` itself untouched (no goal files edited); the full
  build passing implies no regression.
- Rust/emission checks not applicable: no Rust, corpus, or emission
  surface touched.

## What remains open (also in CUTS)

Non-overwrite deadness (needs whole-block recomputed liveness),
block-window float rewrites (avail facts, lowering lane),
`budget_simulation` exhaustion timing (lane 278), and the full
target chain (silicon correspondence, TSO/GX bridge, ABI/loader) —
all explicitly not claimed.

## Findings / task notes

1. The naive overwrite statement (purity only) is FALSE: if the
   overwriting expression reads the target (e.g. `e2 = .var x`),
   the two sides compute different values. The DESIGN "dead
   confirmed" premise is load-bearing, not bureaucratic: it is the
   `liest e2 x = false` side condition with the `eval_set_frisch`
   frame lemma discharging it. I consider this the one subtle point
   of the row, handled, not a task defect.
2. `simp only` unfolds and rewrites reliably in this tree but
   frequently leaves a reflexive goal open; every such closer here
   ends with an explicit `rw`/`rfl`/`congrArg`. Not a task issue,
   recorded so reviewers are not surprised by the style.
3. Nutation cases of `Expr.rec` with an explicitly given `motive_2`
   arrive pre-introduced (inaccessible); `keine` closes by `rfl`,
   `zahl` by `refine ih _ _ _ ?_` + `assumption`. Same category as
   (2).
4. Contracts/call-log preservation is carried by the outcome
   equality (identical rest, worlds, envs; no calls in the window),
   not by a separate `Folge` theorem. If a stricter reading wants an
   explicit ghost-event lemma, that is follow-up work, not a gap in
   the stated connection.
