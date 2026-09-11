# PORT-PFLICHT — the WIP obligation register, and the merge-or-keep verdict

*Specifies the `Pflicht.lean` obligation register from the WIP commit, read-only.
Nothing here edits the WIP, merges it, or builds it.*

## 0. Source and status

| | |
|---|---|
| Source | commit `85cb4f4`, `grammatik/Grammatik/Pflicht.lean`, **544 lines** |
| Read here via | `git show 85cb4f4:grammatik/Grammatik/Pflicht.lean` (never checked out) |
| Status of the source | **WIP on a stale base — NOT mergeable as is** (commit message, `85cb4f4`) |

The WIP was written against the 2026-09-09 night state. Against current master
it drops 17 theories from the `Grammatik.lean` index, removes `SYNTAX.md`
sections 19–21, and renames `Logik.vorzustand` back to `uebergang`, reversing
the recorded B26 decision. Any verdict below that says "keep" means: keep the
*ideas* behind a port boundary, never fast-forward the branch.

## 1. Register semantics — what `Pflicht.lean` registers

### 1.1 The obligation shape: `Logik` (7) and `Hardware` (6)

The register does not invent its obligation type; it enumerates over one that
lives in the WIP `Semantik.lean` (`git show 85cb4f4:.../Semantik.lean:288-312`):

`Logik D` — what the **writer** owes:

| constructor | meaning |
|---|---|
| `.vorbedingung f` | the caller establishes `f`'s precondition |
| `.nachbedingung f` | the body establishes `f`'s postcondition |
| `.invariante i` | invariant `i` (over `D.Inv`) holds |
| `.schleife` | the loop invariant survives a pass |
| `.abstieg f` | the `decreases` descent of `f` |
| `.uebergang` | a `state`-transition left its declared `von` field |
| `.behauptung n` | `assert`/`lemma n` number `n` does not hold |

`Hardware D` — what is **not** the writer's, but is named, not silent:

| constructor | meaning |
|---|---|
| `.annahme a` | `assume` / extern / prim / asm / entry / entrust |
| `.fortschritt a` | `progress` assumption |
| `.ieee` | float left its declared range, or NaN/infinity (IEEE 754) |
| `.register r` | a device register answered outside its declared type |
| `.geraet r` | a register answered against its `requires` (device assumption) |
| `.sichtbarkeit a` | an `awaits` missed its publication (memory model A10) |

### 1.2 The enumeration: `pflichten`, per syntactic class (`:116-167`)

Five mutually recursive functions `syntax -> List (Logik D)`:

- `Stmt.pflichten`: `.behauptung n -> [.behauptung n]`; `.uebergang -> [.uebergang]`;
  `ite`/`onOption`/`onTag`/`onGrund` recurse; `.call f` and `.bindCall f` /
  `.bindCallElse f` contribute `[.vorbedingung f]`; `traverse`/`forever`
  contribute `.schleife :: body`; `retry` contributes `body ++ overflow`;
  **everything else contributes `[]`** — stores, register traffic, `awaits` /
  `exchange`, floats, narrowing, checks, axiom calls, and indirect calls
  (`.callInd -> []`).
- `Block.`, `Endblock.`, `Arms.`, `GrundArms.pflichten` lift the statement
  walk over sequencing, bindings, and match arms.

The `[]` rows are the load-bearing design statement (header `:17-19`): types,
ranges, rights, locks, marks, races, interleaving are "Satz der Grammatik"
and never fall back on the writer.

### 1.3 Completeness: every `Logik` outcome is listed or came from a call

- `AusRuf R e` (`:170`): some function `f` answers `.logik e` through the call
  oracle `R` — the escape hatch that keeps the enumeration honest about calls.
- `pflichten_vollstaendig` theorem family (`:276-456`): for statements,
  blocks, end blocks, and both arm lists — `exec… = .logik e` implies
  `e ∈ ….pflichten ∨ AusRuf R e`. Supported by outcome-shrink lemmas
  (`:175-196`) and three loop-runner dissections: `traverseLauf_logik`,
  `retryLauf_logik`, `foreverLauf_logik` (`:197-260`).

### 1.4 The program register (`:461-539`)

- `Programm.pflichtenVon f = [.vorbedingung f, .nachbedingung f, .abstieg f]
  ++ D.invs.map .invariante ++ (P.rumpf f).pflichten` (`:465`): the per-body
  walk plus the three function-level duties plus every declared invariant.
- `Programm.Pflicht e = ∃ f, e ∈ P.pflichtenVon f` (`:469`).
- `rufAt_pflicht` (`:472`): a call at any depth yields only program-duty
  logic (induction over call depth; the invariant case goes through the
  `D.invs` prefix).
- `exec_pflicht` (`:504`): a body outcome is in the body's list or the
  program's register — "the Satz vom Pflichtenheft".
- `Hardware.name` (`:512`): every hardware outcome carries a printable
  assumption name for the checker message.
- `verifikationsflaeche` (`:526`): the trichotomy — control flow, or duty
  logic (body or program register), or named hardware. "Between them is
  nothing."

### 1.5 The ghost appendix: G001 (`:33-112`)

`geistOrt`, `geistfrei` (spec may read ghost, executable code may not), and
`ausfuehrbar` per statement/block/arm. Ghost erasure itself is booked as an
**emitter** duty in `PLAN-UMSETZUNG.md`, not proved here.

## 2. Relation to the `Coverage.lean` passlogik register

`programmlogik/Gabbro/Coverage.lean` (1415 lines) answers a different question
over a different model:

| | `Pflicht.lean` (WIP) | `Coverage.lean` (master) |
|---|---|---|
| Model | grammatik core (`Deklaration`/`Vertrag`/WIP `Semantik`+`Maschine`) | programmlogik `Body` (`Env`/`Typing`/`State`/`World`/`Contract`/`Frame`) |
| Register | `syntax -> List (Logik D)` (what the writer owes) | `Form -> Verdict` (`classify`, total by construction, `:314-338`) |
| Verdicts | listed-or-came-from-a-call; duty vs named hardware | `carried` (general lemma) / `carriedByTactic` / `assumed <name>` / `refused <tag>` / `ownLogic` |
| Own-logic boundary | implicit: everything not listed is grammar theorem | explicit definition: `IsOwnLogic` over `ensures`/`invariant`/`requires`/`reaches` (`:375`), proved to agree with `classify` (`ownLogic_is_the_persons`, `:1312`) |
| Completeness claim | `exec_pflicht` / `verifikationsflaeche` | `the_sentence` (`:1375`): every non-own-logic form is carried, tactic-closed, assumed, or refused |
| Guard against drift | none | `instrumente/pruefe-deckung.py` holds `Reason` against `lean.rs` line for line; the file's own header (`:35-41`) names the W7/W16 trap |
| What is NOT proved | ghost erasure (emitter duty) | tactic closure, `Form` = whole grammar, emitter statement correctness (`:1387-1412`) |

In short: `Pflicht.lean` enumerates the writer's debt with a membership-or-call
completeness; `Coverage.lean` enumerates every obligation-generating form with
a per-form answer and per-carried-form general lemmas (calls, frame, chain,
stores, reads, ranges, control flow, matches, arithmetic meaning, quantifier
domains, loops, recursion — sections 5.1–5.8b).

## 3. Relation to the S2 `UmgebungOK` / `SchleifenOK` duties

S2 (`messung/S2-UMGEBUNG-ENTWURF.md`, `messung/S2-SCHLEIFE-ENTWURF.md`) discharges
two premises of `exec_sicher` as theorems instead of assumptions:

| S2 premise today | theorem after S2 | evidence |
|---|---|---|
| `UmgebungOK` (every callee keeps the world, answers per signature) | `umgebung_ok_of_runs` | per-body `pruefeBlock_sicher` duty lifted via `contract_of_duty` (acyclic: graph order; cycles: `Below`/`BelowM` + `decreases`, `K008`/`K009`) |
| `SchleifenOK` (every loop keeps world + scope) | `schleifen_ok_of_runs` / `schleifen_ok_of_runsloop` | `looprule_of_body` over the `iterate` index list under `RunsLoop`/`RunsLoopIn`/`RunsLoopN`, using the `exited`/`left` scope rows; plus a new `rumpf` `LogikS` constructor for stuck-in-body |

`Pflicht.lean` names the *owed* side of exactly these duties
(`.vorbedingung`/`.nachbedingung`/`.abstieg`/`.invariante`/`.schleife`); S2
supplies the *lifting* that discharges them. Neither replaces the other: the
register says what must be proved per function, S2 says how the per-body proof
becomes an environment contract.

## 4. Overlap map — what overlaps, what complements

| `Pflicht.lean` duty | `Coverage.lean` counterpart | S2 counterpart | relation |
|---|---|---|---|
| `.vorbedingung f` (caller owes; one entry per call site) | `callStatement`/`callResultBound`/`callChain`/`contractFromDuty` (mechanics: contract fires, frame, chaining) + `ownRequires` (the clause text is the person's) | `UmgebungOK` call half via `contract_of_duty` | **overlap** on the fact, complement on the direction: Pflicht books the debt, Coverage+S2 book the discharge |
| `.nachbedingung f` (program level, per function) | `answerWithShape`/`answerWithoutShape` (what the caller may read) + `ownEnsures` | callee-contract post inside `UmgebungOK` | **overlap**, same split as above; granularities differ (per-function list vs per-site lemma) |
| `.invariante i` (over `D.Inv`, mapped at program level, checked per call) | `ownInvariant` + `loopPass*` family | `SchleifenOK` loop rule (WF+inv per pass) | **partial overlap**: declaration-indexed global invariants exist only in Pflicht; per-loop preservation only in Coverage/S2 |
| `.schleife` (one token per `traverse`/`forever`) | `loopPass`/`loopPassInRange`/`loopPassCounted` + `environmentRunsLoop`/`environmentBoundsPasses` | `iterate` induction + `exited`/`left` rows | **overlap** on the debt, complement on the shape: Pflicht has one token, Coverage/S2 have three inductions |
| `.abstieg f` (per function) | `recursionSelf`/`recursionCycle`/`recursionInLoop` | `Below`/`BelowM` inductions, `K008`/`K009` evidence | **overlap**, same debt/discharge split; common-bound problem (S2 §6.1) is owed by both sides equally |
| `.uebergang` | — (no counterpart) | — | **complement**: WIP-only form, portable as a delta |
| `.behauptung n` | — (no counterpart) | — | **complement**: WIP-only form (`assert`/`lemma`), portable as a delta |
| `Hardware.*` (6 named outcomes) | 6 `assumed` names (`Initially`, `Runs*`, carriers, checker/emitter) + 42 `refused` tags | foreign bodies stay hypotheses (S2 §6.2) | **partial overlap**: environment/device/memory-model assumptions appear in both, under different names and shapes; float/device/refusal granularity differs |
| `.callInd -> []` + `AusRuf` pass-through | `callInExpressionHoisted`/`callChain`, `foreignBody`/`devicePromise` assumptions | — | **overlap with opposite booking**: Pflicht charges indirect calls nothing and attributes their logic to the callee register; Coverage assumes/names them |
| stores/reads/ranges/matches/sequencing/quant-domains/arithmetic (`[]` rows) | carried by general lemma each | `Welt_store`-style preservation inside passes | **deliberate non-overlap**: both sides agree these are grammar theorems, stated once per side from its own model |
| G001 ghost (`ausfuehrbar`/`geistfrei`) | — | — | **complement**: emitter-erasure rule with no Coverage/S2 counterpart |

## 5. Verdict: KEEP both registers — port deltas, never merge

**Do not merge `Pflicht.lean` into `Coverage.lean`, and do not replace
`Coverage.lean` with it.** Keep one register per question and cross-link the
overlap rows of section 4 instead.

Reasons:

1. **Different inductive base.** `Logik D` is indexed by the WIP grammatik
   declaration; `Form` is indexed by the programmlogik `Body` model plus the
   emitter's decision points (`lean.rs`). A merged register would have to be
   indexed by both, i.e. by a shared syntax that does not exist — the merge
   itself would create the second register the next change drifts against.
2. **Different completeness statements.** Membership-or-came-from-a-call
   (`exec_pflicht`) and total-classify-plus-per-form-lemma (`the_sentence`)
   are proved by different inductions over different types. Unifying them
   proves neither; it restates both.
3. **Different guards.** `Coverage.lean`'s `Reason` half is held against
   `lean.rs` by `pruefe-deckung.py`; `Pflicht.lean` has no guard at all. A
   merge would either drag unguarded constructors under a guarded name or
   leave half the merged file unguarded — both strictly worse than today.
4. **Stale-base contamination.** The WIP branch carries reversions (17 dropped
   theories, lost `SYNTAX.md` §§19–21, B26 rename reversal, §0). A merge
   imports them together with the register; a port imports only section 6.
5. **W7 cuts against the merge, not against keeping.** W7 forbids *two
   registers over one thing*. These are two registers over two things
   (writer-debt enumeration vs per-form channel answer) that share five rows
   of debt/discharge vocabulary. Merging them makes one register over two
   models — the failure class this folder writes against (cf. S2-UMGEBUNG
   §6.5: "a second register over the same graph").

Port list (deltas worth carrying onto master's core, in order):

1. `.uebergang` / `.behauptung n` constructors with their single-row
   enumeration — new debt, no counterpart, no conflict.
2. Program-level booking of `.nachbedingung` / `.abstieg` / `.invariante`
   (`pflichtenVon` shape): per-function duties beside the per-site S2
   discharge, closing the gap where Coverage proves the mechanics but no
   register lists what each function owes.
3. `Hardware.name` strings reconciled against Coverage's assumed/refused
   names — one naming table, read (not copied) by the checker message.
4. G001 as an emitter duty (already booked in `PLAN-UMSETZUNG.md`): port the
   predicate, not the erasure proof.
5. Re-examine `.callInd -> []`: master's `foreignBody` assumption and the
   WIP's charge-nothing must become one explicit decision, not two silences.

*Base: `58d6b83` (lane-113). WIP read at `85cb4f4`, file `grammatik/Grammatik/Pflicht.lean`
(544 lines). `Coverage.lean` read at base (`programmlogik/Gabbro/Coverage.lean`,
1415 lines). S2 designs read at base (`messung/S2-UMGEBUNG-ENTWURF.md`,
`messung/S2-SCHLEIFE-ENTWURF.md`). No builds run.*
