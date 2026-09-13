# MUSE-REPORT-131: audit of `ziel_ort` and the G repairs

Lane 131, read-and-probe. One new file: `grammatik/Grammatik/AuditZiel.lean`
(plus the `import Grammatik.AuditZiel` line in `grammatik/Grammatik.lean`).
Nothing else in `grammatik/` touched; `RufMaschineG.lean` and `ZielOrt*` untouched.

## 1. `ziel_ort` premise table (ZielOrtBeweis.lean:1098-1104)

| Premise | Filed class | My class | Jointly satisfiable | Finding |
|---|---|---|---|---|
| `hO : GutO O` | (b) hardware | (b) | yes (`zO_gut`, `refO_gut`) | honest |
| `hvoll : ∀ g, g ∈ fs` | (c) decidable program fact | (c) | yes (`zFs_voll`, by cases) | honest |
| `hFrag : programmImFragment P fs = true` | (c) | (c) | yes, non-vacuously: `zP` contains calls, a `locks` block, a write and reads (`zP_fragment` by `decide`) | honest |
| `hFuss : fussOrtB P fs = true` | (c) | (c) | yes (`zP_fuss`), incl. callee contract carriers in the caller footprint | honest |
| `hK : ∀ f, KoerperGut P O passes f` | (a) user | (a) | yes, incl. bodies that CALL (`zP_koerper_wrap`, `zP_koerper_haupt`) | honest; the `∀ R` is over handlers, not syntax (see §2) |
| `hStart : StartGut P sp init` | (a) user/caller | (a) | yes (`zP_start`) | honest |
| `hex : StartExklusiv init` | (a) boot assignment | **(d) start-configuration fact** | yes, but ONLY with a lock-free entry (`zInit_exklusiv`) | **NO — misclassified, load-bearing. Counter-lemma `audit_same_lock_start_excluded`.** As stated (`∀ t u : Faden`, `Faden = Nat`) it is not a decidable program fact; for constant assignments it collapses to a finite check (`audit_startExklusiv_const`), whose content is "the start function holds no lock" — i.e. two threads running the same lock-holding routine are excluded. Necessity is proved (`ziel_ort_form_falsch`), so this is a real restriction, not a bug; but (a) is the wrong column. |
| `e0 : Ereignis D` (data) | carrier existence | (d) | yes iff the declaration has a table, global or lock (`zE0`); `Ereignis D` is empty otherwise (Semantik.lean:59-65) | honest, and the CUTS of ZielOrtBeweis.lean admits the carrier-less gap. `e0` is load-bearing (`audit_antwortWelt_uses_e0`: every recorded answer sits at `e0 :: key-spur`, keeping the record a function via `funk_append`). |

## 2. `KoerperGut`'s `∀ R` is not a hidden syntax universal

`KoerperGut` (ZielOrt.lean:100-109) quantifies over handlers `R`
(a semantic domain), worlds and actual parameters — never over
`Vertrag`/`Stmt`/`Expr`. The domain is inhabited:
`audit_handler_inhabited` (the empty record's `rufAus` respects every
contract of `zP` and never blames a caller). Satisfiability for ordinary
bodies that CALL other functions is proved, not assumed:
`zP_koerper_wrap` (calls `lies` then `einzahlen`, both conjuncts) and
`zP_koerper_haupt` (calls through a `locks` block). No rule-13 issue.

## 3. Vacuity: the witness is non-degenerate, no premise vacuous

`ziel_ort_zeuge` instantiates ALL premises jointly on `zP`. Non-degeneracy
(`audit_cross_thread_return`, from `zLauf`/`ziel_ort_zeuge_interferenz`):
memory moves `0 → 100`; `einzahlen` and `lies` are entered and returned;
thread 0's `lies` returns `100`, a value written by thread 1 while thread 0
had logged only its own start (true two-thread interleaving, under the
common signature lock). No premise holds vacuously there: the fragment
check fires on calls/locks/writes; the caller-duty conjunct of
`KoerperGut` is exercised by `wrap`/`haupt`; `StartExklusiv` holds
substantively (lock-free entry, with the exclusion proved real by B2).

## 4. Faithfulness of the G repair: both disciplines still run

G has no bare `nimmt`/`gibt` (RufSchrittG constructors listed: `dannLocks`
is the only take, `freiGib`/peels the only releases; every memory step
carries `HeldGenau`). Both checker-accepted kinds execute on reached runs:
* `requires Held(L)` (caller holds): `audit_sig_held_executes` — thread 0
  inside `zLies` holding `()` while thread 1 does not.
* `effects { locks L }` (takes L itself): `audit_takes_lock_executes` —
  thread 0 starts lock-free (`offen = []`) and later holds `[()]`, i.e. the
  `locks` statement of `zHaupt` fired through `dannLocks` (which demands
  `RufFreiG`, so exclusivity is enforced at take time).
`HeldGenau` cannot strand a checker-accepted run at entry: entry holdings
are exactly the signature locks (`offen_startSpur`), and `zLauf` fires 18
steps through takes, calls, writes and returns. Residual gap (by design,
not a finding): bodies outside `kOk` (loops/axioms/error channel) have no
run at all — an Opus lane is extending `ziel_ort` there now.

## 5. `VertragAmOrtG` says what the goal needs

`ReqAmEintritt P g s0 rho` at every logged `eintritt` with the logged
`rho`/`s0`; `EnsAmRueck P g s0 s1 rho v` at every logged `rueck` with the
logged `s0`, `s1`, `rho`, `v` (ZielOrt.lean:67-72; `ReqAmEintritt`/
`EnsAmRueck` evaluate with actual values, VertragOrtB.lean:114-123).
Nothing quantified away — unlike the old `QRequires`/`QEnsures` ∀-env shape
(SATZKARTE R8). `audit_cross_thread_return` exhibits `EnsAmRueck` at a
logged return with actual values.

## New theorems (all in AuditZiel.lean)

* `audit_handler_inhabited`
* `audit_startExklusiv_const`, `audit_same_lock_start_excluded` (counter-lemma)
* `audit_sig_held_executes`, `audit_takes_lock_executes`
* `audit_cross_thread_return`, `audit_antwortWelt_uses_e0`
* None takes a universal-over-syntax premise, so no `_zeuge` companions are
  owed (rule 13); the task names no `ZEUGE:` targets.

## Build

`./lean-probe grammatik/Grammatik/AuditZiel.lean`: 0 errors; all seven
theorems depend only on `[propext, Classical.choice, Quot.sound]`.
`./lean-bau`: `Build completed successfully (75 jobs).` — whole project green.

## What I believe is wrong in the task

Nothing load-bearing. One classification correction (filed above as the
single "no"): `StartExklusiv` is booked as a user obligation (a) but is a
start-configuration fact (d) — undecidable as stated, finite only for
constant assignments, and it excludes same-function lock-holding threads.
The file is otherwise honest: the exclusion's necessity is proved
(`ziel_ort_form_falsch`), and the CUTS lists exactly what is open.
