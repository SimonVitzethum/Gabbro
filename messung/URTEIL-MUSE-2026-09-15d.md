# Confirmation verdict (independent Muse reviewer, round 6, 2026-09-15d)

*Base: branch `muse/193` (contains the G1 repair merge `dc880b54`). I did not
read any `URTEIL-OPUS-2026-09-15d*` file. I read `URTEIL-OPUS-2026-09-15c.md`
(G1) as instructed, `SATZKARTE.md` §§1-24, and the Lean sources cited below.
No existing file was changed; the only new files are this verdict and
`MUSE-REPORT-193.md`. My probe file is `$TMPDIR/probe193.lean` (uncommitted,
git-excluded); `./lean-probe` on it exits 0 with 0 errors. The review target
is the flagship `gabbro_ziel : GabbroZiel`
(`grammatik/Grammatik/Zielsatz/Beweis.lean:198`), whose obligation (b) is
`NutzerPflicht E` (`Spec.lean:477`: `LogikPflicht` = per-function
`KoerperGutS` + `InvGutS` + `InvGutGrund` at every `forever` budget, plus
`SperrInvLokal` + `AxEnsLokal`, plus `StartPflicht`).*

## VERDICT: the goal with named gaps -- no unnamed gap found.

G1 is closed (verified with my own probes, §1). The systematic sweep (§2)
covers every constructor of `Logik`, `Hardware`, `Ausgang`, `EndAusgang`,
`RufAusgang` (`Semantik.lean:277-343`), `HaltArt` (`Zielsatz/Spec.lean:561`),
every non-`ok` source of `execStmt`/`execBlock`/`execBlockH`/`execEnd`/`rufAt`
(incl. the `traverse`/`retry`/`forever` runners), and every machine-G stuck
condition. Two probe-A variants (`ensures false` everywhere) GET THROUGH
(b): P-never (call of a `-> never` axiom) and P-geraet (register read whose
declared promise is `false` at every value). Both are NAMED stops
(`HaltArt.nieZurueck`; `Hardware.geraet` as the honest vacuity of the ONE
list), proved in the probe file as `Probe193.nE1_nutzer` and
`Probe193.nE2_nutzer`. Every other model- or user-decided outcome is either
excluded by (b) (with a refutation probe) or a named stop of the conclusion.

## 1. G1 closed, with my own probes

SATZKARTE §24 claims every type has a decoding and empty answer types are the
named stop `nieZurueck`. I re-checked both directions independently:

- Direction 1 (the oracle CAN answer): `Probe193.p_sum_bewohnt` (every
  `ok | err` value is some raw word, via `einpassen_voll`),
  `Probe193.p_temp_bewohnt` (the word of `0.5` decodes),
  `Probe193.p_fnptr_bewohnt` (a function pointer decodes under an image
  placing it -- the case §24 argues must be oracle-quantified, not declared).
- Direction 2 (probe A behind such a call/read is REFUTED): `Probe193.p_G1A`
  (an `E1` with code `g1PA` never meets `NutzerPflicht`, via
  `g1PA_widerlegt`), `Probe193.p_G1R` (same for `g1PR`, via
  `g1PR_widerlegt`, for every `Q`).
- Axioms: all six main probe theorems depend only on
  `[propext, Classical.choice, Quot.sound]` (`p_fnptr_bewohnt` on
  `[propext, Quot.sound]`).

The two round-5 Opus probes (`g_ziel`, `r_ziel`: `ensures false` behind a
sum-typed axiom call / a float register read, certified) now fail at (b) by
the theorems above. The repair arguments (`einpassen_voll`,
`antwortLeer_iff`, the ONE-list entries for `hardware`/`nieZurueck`) are
correct as far as this sweep reaches: no remaining type has an empty answer
class without being `AntwortLeer`, and no `AntwortLeer` type admits an
answer.

## 2. The sweep: every outcome the model could decide

Notation per row: WHO decides it (user code / oracle / scheduler / model /
declaration), whether (b) constrains it, whether the CONCLUSION (`Ziel`)
constrains it, and the probe result. "(b) constrains" means a probe-A
variant forcing that outcome fails `NutzerPflicht`; "named" means the
conclusion reports it (`FortschrittG`/`HaltBenannt`) and the ONE list
(`Spec.lean:126-210`) justifies it. Rows marked NONE need no probe-A variant
by the task criterion ((b) constrains them); rows marked PROBE have one, in
`$TMPDIR/probe193.lean` (mine) or in the tree (cited).

### Table A -- `Logik` (Semantik.lean:277-293): all decided by USER CODE

| outcome | who decides | (b) | conclusion | probe |
|---|---|---|---|---|
| `vorbedingung f` (requires false at a call) | user code (callee contract + caller args) | YES, caller-duty clause (`KoerperGutS`, second half of cl. 1: no `vorbedingung` under `torRuf`) | `vertrag` leg via replay | NONE (constrained) |
| `nachbedingung f` (ensures false at return) | user code | YES, body triple (return implies `EnsAmRueck`) -- the core user duty | `vertrag` (`VertragAmOrtG`) | NONE (constrained) |
| `invariante i` (owed invariant false at return) | user code | YES, `InvGutS` / `InvGutGrund` | `invRueck` / `invGrund` | tree: `tabelle_widerlegt` (fails (b)) |
| `schleife` (loop invariant false at a boundary) | user code | YES, no-`logik` clause (2nd half of `KoerperGutS`) | `keinLogikHalt` | tree: `probeA_widerlegt_gilt` (`paP`), `probeD_widerlegt_gilt` (budget 1) |
| `abstieg f` (recursion fuel spent, `rufAt 0`) | MODEL (fuel of the sequential semantics) | bodies call through handlers (`execEndH` uses `R`, never `rufAt`), so a body cannot end in `abstieg`; callee `abstieg` is the handler's (`OhneLogik` excludes it) | G has no depth bound (NOT CLAIMED): recursion runs on; no stop filed | NONE (dead in G; model artefact of `rufAt`, orthogonal to stops) |
| `vorzustand` (state field not `von`) | user code (own memory values) | YES, no-`logik` clause; oracle-independent, so any forcing program fails (b) at every oracle/handler/move instantiation | `keinLogikHalt` (`PrueftG` at the transition leaf) | NONE (constrained; same shape as `schleife`) |
| `bereich` (float out of range/NaN/Inf, no `else`) | user code (kernel IEEE model on own values, every oracle) | YES, no-`logik` clause (since F1) | `BereichG` (proof side; `FortschrittG` lists no float stop) | tree: `probeF1_widerlegt_gilt` |

### Table B -- `Hardware` (Semantik.lean:296-310)

| outcome | who decides | (b) | conclusion | probe |
|---|---|---|---|---|
| `annahme a`, ANSWERABLE type (axiom answer does not decode) | ORACLE (raw word); user declares the type | NO on the stop itself -- but (b) quantifies ALL oracles, and fitting answers exist (`einpassen_voll`, G1), so probe A fails | named `hardware` (`KopfHalt .hardware` needs `¬ AntwortLeer`; ONE list) | MINE: `p_G1A` -- does NOT get through |
| `annahme a`, EMPTY type (`never`, `.grund 0`, empty range, valueless sum) | DECLARATION (no value exists; `antwortLeer_iff`) | NO -- continuation unreachable, everything before the call still covered | named `nieZurueck` (ONE list; partial correctness) | MINE: `nE1_nutzer` -- GETS THROUGH, named |
| `fortschritt a` (spent `forever` budget) | MODEL artefact (budget, quantified in (b) via `∀ passes` in `LogikPflicht` and in `GabbroZiel`) | YES in effect: budget 0 alone allows the stop, but every larger budget is also quantified; invariant-false fails (`schleife`), invariant-true returns under `ensures false` | named `budget` (ONE list: every finite prefix of the C loop is a larger-budget run) | tree: `probeD_widerlegt_gilt`, `probeD_wahr_widerlegt` |
| `ieee` | NOTHING -- dead constructor | n/a | n/a (kept for C-side vocabulary) | NONE: verified by grep -- no `.ieee` constructor site in `Semantik.lean`, `SperreSem.lean`, `RufMaschineG.lean`, `Fortschritt.lean` (only the inductive case + comments) |
| `register r`, ANSWERABLE type (register answer does not decode) | ORACLE | NO on the stop; YES via oracle quantification (as `annahme`) | named `hardware` | MINE: `p_G1R` -- does NOT get through |
| `register r`, EMPTY type | DECLARATION | NO (as `never`) | named `nieZurueck` (`KopfHalt` equations cover `regLies`/`regLiesElse`) | NONE: symmetric to P-never by the `KopfHalt` equations (no separate probe built) |
| `geraet r`, SATISFIABLE promise (answer against `rzusage`) | ORACLE (answer) + DECLARATION (promise) | NO on the stop; YES via oracle quantification (a promise-meeting answer proceeds to return-false) | named `hardware` | tree: `g1PR_widerlegt`/`p_G1R` (decoding + promise `true` both met, body returns) -- does NOT get through |
| `geraet r`, promise `false` everywhere | DECLARATION (visible false promise) | NO -- every read stops for every oracle | named `hardware` (ONE list: same honest vacuity as `Q := false`) | MINE: `nE2_nutzer` -- GETS THROUGH, named |
| `sichtbarkeit a` (`awaits` flag not visible) | ORACLE (`O.sichtbar`) | NO on the stop; YES via oracle quantification (`RegLokal` leaves `true` admissible, so the showing oracle is in the class) | named `flagge` (a WAIT, ONE list: three sub-cases incl. never-published) | MINE: `nAW_widerlegt` -- does NOT get through |

### Table C -- control flow (`Ausgang`/`EndAusgang`/`RufAusgang` non-error)

| outcome | who decides | (b) | conclusion | probe |
|---|---|---|---|---|
| `ok` (continue) | user code | triples, step by step | transported by replay | NONE |
| `zurueck` (value return) | user code | YES (`EnsAmRueck`; `InvGutS`) | `vertrag`, `invRueck`, `startEnde` | NONE (the obligation itself) |
| `grund r` (reason return) | user code (callee) | invariants at the exit (`InvGutGrund`); the VALUE travels to the caller, whose triple quantifies over grund-answering handlers (`RespektiertRahmen` restricts `ok` answers only, so every reason answer is admitted and owed) | `invGrund`, `keinStartGrund` | NONE (constrained at caller + exits; control flow, no stop filed) |
| `leave`/`next` | user code, inside loops only (type-level `l` flag) | loop semantics (boundary invariant checks = `schleife`) | replayed as loop shims | NONE |
| `logik`/`hardware` wrappers | Tables A/B | Tables A/B | Tables A/B + D | Tables A/B |

### Table D -- `HaltArt` (Spec.lean:561-573): all NAMED in `FortschrittG`

`hardware`, `flagge`, `budget`, `nieZurueck` -- each is a disjunct of
`FortschrittG` (`Spec.lean:619-622`) with its ONE-list justification
(`Spec.lean:165-208`). Every probe-A variant that gets through (b) lands in
exactly one of them (P-never: `nieZurueck`; P-geraet: `hardware`/`geraet`).
No fourth kind exists in the type.

### Table E -- machine-G stuck conditions (`RufSchrittG` has no rule)

| situation | who decides | status |
|---|---|---|
| thread finished (`FertigG`; root `ret`/`retGrund`, idle root) | scheduler (run to completion) | conclusion, not stuck |
| `dannLocks` while another thread holds `L` (`WartetG`) | SCHEDULER / other threads | named wait; liveness NOT claimed (NOT CLAIMED, `HardwareImAbschnitt` assumed by the waiting bound only) |
| `dannAwaits` with invisible flag | ORACLE | named `flagge` (Table B) |
| spent `forever` budget (`.ewig _ 0`) | MODEL (budget) | named `budget` (Table B) |
| leaf/axiom/register head failing | ORACLE or DECLARATION | named `hardware` / `nieZurueck` (Table B) |
| `logik` check head (`traverse`/`forever` boundary, `leave` out of `traverse`, `state` transition) | would be USER CODE -- but PROVED to always pass | `KeinLogikHaltG` (from the theorem) + `BereichG`; the rule then FIRES given `HeldIn` (`schritt_an_pruefung` family). Probe A/F1 are the refutations. |
| `HeldIn` side condition of reading rules | MODEL (book-keeping) | holds on every reachable machine (repair §15.1; `rufG_haelt_statisch` for `⊆`); no hypothesis left in progress |
| caller shape at a pop (`wartet`/`wartetSonst`) | MODEL | proved invariant `FormKette` (`Fortschritt.lean:170`; `rufG_nie_wartend`; closed §19.2) |
| `leave`/`next` in an `else` block | MODEL | repaired §15.3 (`GRest.abbruch` + peel rules); no stuck state |
| anything else | -- | none: `fortschrittG_aus` (`Fortschritt.lean:1032`) proves `FortschrittG` on every reachable machine with `KeinLogikHaltG` + `BereichG` -- every thread is finished, waiting, at a named stop, or stepping |

## 3. The probes

`$TMPDIR/probe193.lean` (uncommitted): `./lean-probe` exits 0 with
`0 error(s) in the COMPLETE output`. Contents:

- `p_sum_bewohnt`, `p_temp_bewohnt`, `p_fnptr_bewohnt` -- G1 direction 1
  (every sum value, `0.5`, and a placed function pointer are some raw word).
- `p_G1A`, `p_G1R` -- G1 direction 2 (the Opus round-5 probes refuted at
  (b), as one `Einheit` each with `starts = []`).
- `nE1_nutzer : NutzerPflicht nE1` -- P-never (`ensures false` behind
  `hol() -> never`): (b) HOLDS (body always `hardware (annahme)`, for every
  oracle/budget/handler/move; `Q := true`; no starts). GETS THROUGH, named
  `nieZurueck`.
- `nE2_nutzer : NutzerPflicht nE2` -- P-geraet (`ensures false` behind a
  read whose promise is `false` at every value): (b) HOLDS (every oracle
  either misses the type or breaks the promise). GETS THROUGH, named
  `hardware`/`geraet` honest vacuity.
- `nAW_widerlegt : NutzerWiderlegt nAW` -- P-awaits (`ensures false`
  behind `awaits g`): (b) FAILS (the always-showing oracle is
  `GutO`+`RegLokal` and meets every `Q`; the body returns). Does NOT get
  through.
- `#print axioms`: all six depend only on
  `[propext, Classical.choice, Quot.sound]` (fnptr on `[propext,
  Quot.sound]`). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

Lesson for the next sweep: two Lean-specific traps bit the probe
construction and are worth knowing -- (i) `fun e => nomatch e` swallows the
following comma inside `⟨...⟩` (parenthesize every such body); (ii) a
pattern mentioning `Expr.wahr.orte` elaborates its implicit `Γ Λ` to
metavariables, so `cases`/`generalize`/`rw` silently miss (collapse `orte`
with `simp only [Expr.orte]` first, then name the `[]` form).

## 4. What stays (named) and what I did not build

NAMED and staying named: `nieZurueck` (P-never -- the declaration's own
non-return promise; the continuation is unreachable in the C as in G);
`hardware`/`geraet` with an everywhere-false promise (P-geraet -- visible in
the declaration like `Q := false`); `Q` unsatisfiable (visible false
hardware assumption, `Spec.lean:147-151`); `starts = []` (a different
program running nothing, `laufzeit_ohne_starts`); lock waits without
fairness; `flagge` with never-published (no "later" in G); the `budget`
artefact; stack depth; weak memory beyond DRF-SC; `costs`; the `.gab ->
Einheit` exporter step. None is decided by the model behind the
obligation's back.

NOT BUILT, with reason: `register`-at-empty-type (symmetric to P-never by
the `KopfHalt` equations -- one construction, two heads); `vorbedingung` /
`nachbedingung` / `vorzustand` / `abstieg`-at-body (constrained entries need
no probe-A variant; `vorzustand` fails (b) at every instantiation since it
is oracle-independent); `grund` values (caller-side duty, reading --
`RespektiertRahmen` admits every reason answer, so callers owe over them);
`Hardware.ieee` (dead by grep, no probe possible); machine-side re-proof of
`FortschrittG` (proved: `fortschrittG_aus`).

No new `sorryAx`, no changed statements, no weakened conclusions. The class
"an outcome the MODEL decides independently of the oracle, filed where the
obligation does not look" is empty after this sweep except for the two
named entries above, both decided by the DECLARATION (user-visible), not by
the model behind anyone's back.

---
CUTS: this file proves nothing by itself. Evidence: the uncommitted
`$TMPDIR/probe193.lean` (`./lean-probe`: exit 0, 0 errors), the committed
theorems cited (`Proben.lean`, `ProbenG1.lean`, `Fortschritt.lean:1032`),
and source reading for the dead/absent cases (`ieee`, `abstieg`-in-G,
`grund`-at-caller). Machine-G rule-by-rule stuck analysis rests on
`fortschrittG_aus`, not on a new proof here. The exporter/translation-validation,
timing, fairness, and memory-model items of NOT CLAIMED are out of scope.
