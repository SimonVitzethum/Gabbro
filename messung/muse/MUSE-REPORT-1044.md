# MUSE-REPORT-1044: Exact review of author 894 (call-argument selection rule)

## CANDIDATE and VERDICT

CANDIDATE: 894 48138d969ae8795f1e03ee3676e095796eb993de
VERDICT: ACCEPT

Details: pinned head `48138d969ae8795f1e03ee3676e095796eb993de`
  (base `b040b155159f47629542b0083e2f0a8a607f2b4c`; files:
  `MUSE-REPORT-894.md`, `grammatik/Grammatik.lean` (one import line),
  `grammatik/Grammatik/X86/OptCallArgSel.lean` (repaired, 562 lines)).
  Bounded acceptance: the R1-R3 repairs below were verified against the new
  snapshot (§9); remaining scope is precisely cut (§6). The prior REPAIR on
  the superseded head `cde94693` is stale and replaced by this verdict --
  the old snapshot was not approved.

## 1. What was inspected

- Pinned snapshot: `.tmp/review/SNAPSHOT.json` (author 894, head/base/files).
- Exact task: `.tmp/review/author-894/OWNER-TASK.md` (lane 894 text, ZEUGE line).
- Exact candidate source: `.tmp/review/author-894/grammatik/Grammatik/X86/OptCallArgSel.lean`
  (full 402-line read), plus `PATCH.diff` header (import-only `Grammatik.lean` diff).
- Build record: `.tmp/review/author-894/BUILD-EVIDENCE.json`
  (final `./lean-bau` exit 0, 511 jobs; final `./lean-probe` 0 errors;
  axioms at most `[propext, Classical.choice, Quot.sound]`; one intermediate
  5-error run on the way, repaired in-candidate).
- Reference manuals: `.tmp/HARDWARE-REFERENCES/REFERENCES.json`
  (Intel SDM 325462-093US, Sept 2026, verified snapshot; AMD unavailable --
  no AMD claim made anywhere, correct).
- Base-tree cross-checks (read-only, this clone at base `b040b155`):
  `execStmt` `.call` arm (`grammatik/Grammatik/Semantik.lean` lines 735-741),
  witness vocabulary (`ReferenzB.lean`: `refEin_schreibt`, `refB_erreicht`,
  `refB_schreibt`, `refArgsLies`, `refHpLiesAt` all exist),
  accepted optimiser precedent (`X86/OptFoldConst.lean`, lane 860, in master),
  DESIGN scope (`DIRECT-COMPILER-DESIGN.md` line 360 §2 ABI-register line,
  line 524 §7 layout/allocation row).
- Forbidden-pattern grep over the candidate file: no `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe`, `intro _`, `have _ :=`
  (only English words "admitted"/"admission" matched). No new
  diagnostic/gift/example/CLI numbers, no MARKE changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.
- Live check through the queued wrapper on the untouched base:
  `./lean-bau` → `Build completed successfully (510 jobs).`
  (510 vs the candidate's 511 is exactly the one new module; consistent.)
  The candidate file itself was NOT copied into this clone (outside my
  ownership: I own only this report), so no `./lean-probe` re-run on it was
  possible here; the probe record in BUILD-EVIDENCE was inspected instead.

## 2. What is good (accepted as bounded)

- Refusal §1 (`CallArgCert`, `callArgZulassen`, four `callArgVerweigert_*`
  theorems + three `decide` probes): genuine decided-Bool refusal proofs.
- Placement §2 (`ArgPlatz`, `regBudget = 6`, `platzFuer`, `platziereAux` /
  `platziere`, `liesWerte`; `platziere_liest`, `platziere_laenge`,
  `platzFuer_reg`, `platzFuer_stapel`, `platzFuer_buendig`; probes
  0/5-in-reg, 6/7-on-stack): genuine value/shape proofs over arbitrary
  values, validator-recomputable functions. `maxArgs = 64` provenance is
  unstated (see R3) but the gate logic built on it is sound.
- IEEE/arity §3 (`gleitPasst_erhalt`, `probe_gleitPlatz`, `platzOk`,
  `platzOk_von_zulassen`, `keinFehlerNeu`, `platzWort`, `probe_platzWort`):
  sound as far as stated; float handling is source-value identity, which the
  CUTS honestly scope (see R3 for the missing register-class note).
- Witness form: joint instantiation over the non-degenerate `refD`
  (`refEin_schreibt`), beside reached memory-changing run `MB`
  (`refB_erreicht`, `refB_schreibt`, slot `0 -> 100`). Formally joint and
  non-degenerate.
- CUTS block present and honest about byte correspondence, per-class cost
  maxima, spill/fence accounting, TSO/GX bridge. Task feedback (no explicit
  DESIGN §7 call-arg row; §2 line + layout/allocation row used instead)
  verified accurate against `DIRECT-COMPILER-DESIGN.md`.
- Every premise of the target theorem is used; no `ensures` derived; no
  refusal turned into a warning.

## 3. The load-bearing defect (why REPAIR, not ACCEPT)

The TARGET `OptCallArgSel_verbindung` (candidate lines 286-307) concludes,
among four conjuncts:

```
execStmt ... (Stmt.call f args hp hr) σ ρ
  = execStmt ... (Stmt.call f args' hp' hr') σ ρ
```

from premises including

```
(hOrte : args.orte = args'.orte)
(hVals : ∀ w, evalArgs w args w ρ = evalArgs w args' w ρ)
```

by `simp only [execStmt, hOrte, hVals]`. Per `Semantik.lean` 735-741 the
`.call` outcome is a function of exactly `args.orte` (via `σ.lese`) and
`evalArgs` (via `R`), so this conjunct is a congruence corollary of assumed
equal evaluation -- while the optimisation's own output, `platziere vs`
over a detached `vs : List Int`, never feeds `args`, `args'`, `orte` or
`evalArgs`. The three placement conjuncts are proved of `vs`; the call
conjunct is proved of `args`/`args'`; nothing links them. The report's
claim "admitted selection preserves ... the `execStmt` `.call` outcome"
therefore overstates what is established: the evaluation preservation the
optimisation owes (`hVals`) is assumed, not derived. This is the
"desired simulation premise" / "conjunction of checks as execution" shape
the wave rules forbid, and it is material -- not stylistic -- because the
accepted precedent (`OptFoldConst_verbindung`, `rfl` between two concrete
differing syntaxes) derives its rewrite instead of assuming it. Corroborating
symptom: the joint witness instantiates `args = args' = refArgsLies` with
`hVals := fun _ => rfl`, i.e. an identity pair -- no selection change is
exhibited, so the "connection" is never exercised as a rewrite even
existentially.

## 4. Minimal repairs required (R1 load-bearing, R2-R3 boundary honesty)

- R1: connect the placement to the call. Either (a) derive the `evalArgs`
  equality from the placement -- e.g. premise/link `vs` to the evaluated
  argument values and obtain `hVals`-like equality via `platziere_liest`
  instead of assuming it; or (b) keep the congruence shape but restate the
  theorem/report honestly as "conditional congruence under assumed equal
  evaluation", move the evalArgs-preservation-by-lowering into CUTS as an
  explicit OPEN item owned by the lowering/validator lane, and drop the
  "selected call behaves like the source call" claim. (a) is preferred; (b)
  is acceptable as bounded.
- R2: exhibit a real rewrite in the witness: two syntactically different
  `Args` terms related by the rule (or `vs` tied to the call's values with a
  non-trivial placement), so the outcome conjunct is witnessed on a change,
  not on `args = args'`.
- R3: extend CUTS with what the abstraction does not model (all currently
  silent): integer vs float (xmm) register classes under System V AMD64
  (placement is position-only over one `reg` file); REX/width/flag effects;
  16-byte entry alignment (only 8-aligned slots proved); per-image
  convention content beyond one `Bool`; `maxArgs = 64` provenance (fixed
  constant vs validator-decided); TSO/memory-order effects of stack-slot
  stores. None needs modelling here -- precise cuts suffice.

## 5. Architecture notes (checked, no finding)

Byte forms / decode / REX / widths / flags / implicit operands / pre-fault
effects / memory-access order / TSO-atomicity / MXCSR / interrupt gates:
correctly OUT of scope for this source-level rule lemma and deferred in
CUTS to decoder/bridge/cost lanes -- with the R3 proviso that the float and
alignment points above be named there too. No invented determinism found
(`platzFuer` determinism is the rule's own recomputable function, not a
hardware claim); no zeroed/ignored defined effects; no guarantee weakened
elsewhere; `gabbro_ziel` axioms unaffected (candidate adds nothing above
the standard set).

## 6. What remains open

With R1-R3 applied: byte correspondence through decoded final machine
bytes, counted per-class cost maxima, per-site spill/fence accounting,
TSO/GX bridge (all with decoder/bridge/cost lanes, as the candidate CUTS
state), plus the newly cut evalArgs-preservation item if route (b) is taken.

## 7. Task feedback

The lane-894 task text is sound and the DESIGN citation in it is accurate
(§2 line real at `DIRECT-COMPILER-DESIGN.md:360`; §7 row genuinely absent,
only the layout/allocation row at line 524). Suggested addition for future
optimiser-rule tasks: one sentence requiring the rewrite to be DERIVED
between two differing syntax/value terms (no assumed-evaluation premise
carrying the conclusion), and a witness with a non-identical pair -- this
review's R1/R2 would then be caught by construction.

## 8. Last build result

`./lean-bau` on the untouched base (`b040b155`): green,
`Build completed successfully (510 jobs).` New pinned evidence
(BUILD-EVIDENCE.json, final entries): `./lean-bau` exit 0
(`Built Grammatik`, 511 jobs), final `./lean-probe` 0 errors, new theorems
(`wertInt_int`, `envInts_cons`, `probe_envInts`, `refHeldIff`,
`refHpEinAt`) at `[propext]`, both main theorems at
`[propext, Classical.choice, Quot.sound]`; evidence `git log` tops at
`48138d96`, matching the new pinned head. Intermediate red probes in the
record were repaired in-candidate. No source file was added or modified
by this review lane; tree is clean except this report.

## 9. Re-review of the repair (new snapshot only)

Each prior finding was re-inspected against the new file (562 lines):

- R1 CLOSED (route (a)+(b) combined): new §3 (`wertInt`, `envInts`,
  `wertInt_int`, `envInts_cons`, `probe_envInts`) links `vs` to the calls
  via `hVs`/`hVs'`; conjuncts (1)+(2) derive read-back to each site's
  evaluated integer values through `platziere_liest`
  (`rw [hVs, platziere_liest]`), conjunct (3) derives the integer-value
  agreement through the shared record (`rw [<- hVs, <- hVs']`). The
  remaining outcome conjunct (6) is now an explicitly conditional
  congruence (assumed `hOrte` + full `hVals`), and full `evalArgs`
  preservation beyond the integer projection is CUT as OPEN for the
  lowering/validator lane (CUTS first bullet). The overclaiming header is
  gone: the theorem is now documented as "one admitted placement carries
  both sites' values; outcome congruence is conditional on equal
  evaluation". `envInts` is lossy (drops non-integers) -- disclosed in
  text and cuts, acceptable as bounded.
- R2 CLOSED: the witness now calls `einzahlen` with two syntactically
  different terms (`argDreiLit`, widened `3`, vs `argDreiAdd`, widened
  `1 + 2`), same value `3`, `vs = [3]` tied by `rfl` computation,
  non-trivial placement `[(.reg 0, 3)]`, new scaffolding `refHeldIff` /
  `refHpEinAt`. Non-degeneracy unchanged (`refEin_schreibt`,
  `refB_erreicht`, `refB_schreibt`). A real rewrite is exhibited.
- R3 CLOSED: CUTS now name one-`reg`-file vs int/xmm classes, REX/width/
  flags, 16-byte entry alignment, convention content beyond one `Bool`,
  `maxArgs = 64` provenance (fixed constant, decided per-site bound
  check), and TSO effects of stack-slot stores.
- Hygiene re-checked on the new file: no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`/`intro _`/`have _ :=` (stricter grep clean);
  PATCH touches only the three declared files (`Grammatik.lean` diff is
  the single import line); no new numbers/MARKE changes/reserved files.
  Every new premise is used; no `ensures` derived; no refusal weakened.

CUTS: this report proves nothing beyond §§2, 5 and 9; all source claims
live in the candidate. Open work is §6 (byte correspondence, cost maxima,
spill/fence accounting, TSO/GX bridge, full lowering-side
`evalArgs` preservation).
