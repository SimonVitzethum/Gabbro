# MUSE-REPORT-572: Source budget-stop and target work connection

Lane 572, branch `muse/572`, commit `94e77cca` (module + umbrella import).
Owner files only: `grammatik/Grammatik/X86/BudgetExecution.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

New module `Grammatik/X86/BudgetExecution.lean` connects actual source
budget exhaustion with accepted finite target runs through an explicit,
checkable coverage interface. No source checker/Spec/goal/emitter file
touched; no friend optimiser file touched; no IR/executor duplicated;
no desired correspondence assumed.

Inspected first (read, not modified): `Semantik.lean` (`foreverLauf`,
`rufAt`, `execStmt`), `Budget.lean` (`runOps`/`runPasses`), `KostenG.lean`
(cost doctrine), `X86/CostSummary.lean`, `X86/TimeTransfer.lean`,
`X86/HardwareAssumptions.lean`, `X86/Ausfuehrung.lean`,
`X86/Byteschritt.lean`, `X86/ObservationProjection.lean`,
`X86/LockedOps.lean` (`cas_schleife_unbeschraenkt`), `dokumente/x86/`
`QUELLBRUECKE.md`, `AUDIT-BUDGET-OBSERVATIONS.md`, `FLOAT-ZEIT.md` §8.1
doctrine. All names below are the real ones.

Definitions/theorems (all premises used; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`; no `Prop`-typed premise):

- `Deckung s src xs : Prop` — explicit representation/checkable coverage
  interface: the target segment's machine work sits inside the summary
  bound over the source budget `src` (a `kostenTiefF` value at the use
  site). Which source step lowers to which target instruction is carried
  data, never a premise.
- `forever_erschoepft_benannt` — actual source `forever` exhaustion:
  `foreverLauf … 0 … = .hardware (.fortschritt a)` by `rfl`.
- `rufAt_tiefe_erschoepft` — actual depth exhaustion:
  `rufAt … 0 … = .logik (.abstieg f)` by `rfl`.
- `totalCost_anhang` — new induction lemma: ops split over `++`, pinning
  the arithmetic an elimination/inlining cost recomputation owes (E3/A3).
- `deckung_leer` — empty segment covered under a zero work bound.
- `budgetAusfuehrung_transfer` — where target work is spent: named
  per-form hardware bound (`laufKosten_schranke`) plus summary coverage
  (`Deckung`) give `t ≤ B * k` for every summary bound `k` of `src`.
  Two independent facts composed, never one sum renamed; units (source
  steps / retired instructions / named time) kept separate.
- `stoppReihenfolge` — stopping order preserved: over-budget head op
  names the source breach AND refused head form refuses the whole target
  aggregation (head-first, fail-closed, both sides, each under its own
  name; proved axiom-free).
- `kein_freier_versuch` — retry obstruction: unbounded retry behind a
  constant refuses admission AND transfer together.
- `stutter_ohne_schranke` — from `cas_schleife_unbeschraenkt`: every
  claimed constant is exceeded by some retry count; waits/CAS retries get
  no free cost or constant bound.
- `optimierung_darf_nichts_verstecken` — hidden-stutter obstruction: a
  successful aggregation names every step's cost, so an unpriced
  introduced step breaks success instead of hiding.
- `beobachtung_stopp_sichtbar` — observation order: `beobAusgang`
  `fehler` implies `byteschritt = .verweigert`; no stop is silent.
- `budgetAusfuehrung_zeuge` — JOINT non-degenerate witness: reached
  memory-changing run of table-writing `eP` (slot 5 vs 0, log entry,
  `ReqAmEintritt`) jointly with source within (`runPass ⟨5⟩ [fremdOp 3]
  = .ok 1`), source exhaustion (`runOps 3 3 [fremdOp 3]` names budget),
  finite target run (`laufKosten … zeugeProg = some 7`, register 42,
  memory byte 0→42), transfer bound (`7 ≤ 3 * k`), planted refusals
  (unpriced `ret`, unbounded retry behind constant), and the real
  `kostenTiefF` bound plugging into the schema.

Last full build: `./lean-bau` → `Build completed successfully (428 jobs)`.
`./lean-probe` on the file → 0 errors. Axioms: every theorem within
`propext`, `Classical.choice`, `Quot.sound` (`stoppReihenfolge` axiom-free).

## What remains open (labelled blocked, not closure)

1. The `Deckung` producer leg: deriving per-segment coverage from
   validator acceptance needs the generic `valX86_sound` and the
   per-access target-to-W/GX bridge — OPEN, owned by decoder/bridge lanes.
2. The single IR is absent (no `IR.lean` in the tree); nothing here
   pre-empts owner 287. Measurable next integration: prove `Deckung`
   for the `blattSummary`/`zeugeProg` pair from a committed IR lowering
   once available, then replace the carried-data hypothesis at that use
   site.
3. Check-elimination/inlining cost recomputation over the lowered body,
   per-site waiting-exclusion correspondence, cycle/silicon bounds —
   all booked in CUTS, none claimed.
4. Stable producer/consumer interface: producers supply
   `expand` maxima + `Deckung` evidence per segment and `profilZeuge`-style
   named per-form bounds; consumers (`budgetAusfuehrung_transfer`,
   `stoppReihenfolge`, `beobAusgang`) take only those plus the executed
   prefix. No other module needs to change.

## Belief about the task

The task's demand that a "resummed cost inequality with a desired
correspondence premise is not completion" is met by construction: the
correspondence (`Deckung`) is an explicit open interface, and the only
closed end-to-end fact is the jointly witnessed instance over admitted
summaries and executed prefixes. A full source→target budget simulation
(`budget_simulation` in FLOAT-ZEIT §8.1) remains OPEN and is not claimed.
