# VERDICT: Is the project goal reached? (lane 143, independent review, 2026-09-13)

Owner's goal: "A Gabbro user who wants to formally verify a Gabbro program proves
only their OWN logic plus named hardware assumptions; everything else -- memory
safety, data-race freedom, contracts holding where claimed in concurrent runs, and
time -- is carried by the language."

**Verdict: reached for the Lean model, not yet for the implementation.**

The Lean theorems are real, adversarially audited, jointly witnessed on a
non-degenerate corpus program, and axiom-clean. But the chain from a Gabbro source
file a user writes to those theorems is unwired in three load-bearing places, and
the emitted C -- the thing that actually runs -- is connected to machine G by
nothing at all. Details below.

## 1. Every premise of `ziel_ort_rahmen`, classified

Exact statement verified by probe (`.tmp/sonde143.lean`, `./lean-probe` 0 errors;
see section 2). Premise order as printed by `#check @ziel_ort_rahmen`.

| Premise | Class | Rust checker computes it TODAY? |
|---|---|---|
| `P`, `O`, `passes`, `fs`, `sp`, `init` | DATA (binders, not obligations) | n/a |
| `e0 : Ereignis D` (declaration has a table, global or lock) | OTHER: declaration-shape datum | No. Excludes ~28/91 corpus files (surface heuristic, section 3). Nothing to "compute"; carrier-less programs are simply out. |
| `hO : GutO O` | Named HARDWARE assumption (axiom answers inside declared frames, held locks and trace untouched) | No -- per-oracle assumption by nature. Frame half discharged inside by `gutO_rahmenO`; the assumption itself is the user's hardware story. |
| `hRL : RegLokal O` | Named HARDWARE assumption (register answers from declared device carriers; `awaits` visibility from the awaited global only) | No -- per-device assumption. Satisfiable by a memory-dependent oracle (`audit_geO_zeitveraenderlich_lokal`); a device whose answer changes with no carrier write is provably outside (`audit_regwechsel_braucht_traeger`). |
| `hvoll : forall g, g in fs` | Decidable program fact (member-list completeness) | TRIVIAL/NO -- it is a list the tool would have to emit; no checker rule produces or checks it today. |
| `hFrag : programmImFragmentG P fs = true` | Decidable program fact (widened `gOk` fragment; indirect calls only under `KandOk`) | NO -- Lean-decidable only (`programmImFragmentG_ok`). `dokumente/SYNTAX.md` states explicitly: "Lean-decidable, not yet a checker rule -- wiring it per program is emitter work." No Rust rule decides the Lean fragment predicate. |
| `hFuss : fussOrtGB P fs = true` | Decidable program fact (every widened-footprint carrier guarded by a signature lock or written by none) | PARTLY -- fragments exist as Rust rules but the Bool itself is Lean-side (`fussOrtGB_ok`). Related enforced rules: `H007` (every access under its guard, `geteilt.rs`), `H222` (guarded carrier under one entry, `geteilt.rs`), `E220`/`E221` (contract footprint covered, `wirkungen.rs`/`saetze.rs`), `N240` (start exclusivity, `startexklusiv.rs`). None of them IS `fussOrtGB`; the composition (footprint covers callees' contract carriers + device carriers, guard-by-signature-or-unwritten) is not computed by the checker. |
| `hK : forall f, KoerperGutR P passes f` | OWN LOGIC (per-function sequential triple against frame-respecting handlers + caller duty) | No -- this is the user's proof. Correctly shaped: quantifies over handlers/oracles, not over program syntax (no rule-13 defect); handler domain inhabited (`audit_handler_inhabited`); place-correct (`ReqAmEintritt`/`EnsAmRueck`, no `Post`-at-entry). Strictly weaker than the old obligation on the corpus (`r4_rahmen_echt_schwaecher`). |
| `hStart : StartGut P sp init` | OWN LOGIC (boot contracts at the start world) | No -- user's proof. |
| `hex : StartExklusiv init` | OTHER: start-configuration fact (no two threads start in functions sharing a signature lock) | PARTLY -- `N240` enforces the per-entry shape (two starts under one signature lock fall; `startexklusiv.rs` tests both directions). But `StartExklusiv` quantifies over infinite `Faden = Nat`; only the constant-assignment case collapses to a finite check (`audit_startExklusiv_const`). And it bans the most ordinary shape -- same lock-holding routine on two threads (`audit_same_lock_start_excluded`, `ziel_ort_form_falsch`). So: checker covers the common case, the premise still excludes a program class no warning names. |
| `hr : RufErreichbarG ...` (in conclusion) | Run DATA | n/a |

Honest booking: of the three "decidable program facts", ZERO are computed by the
Rust checker today as the exact predicate the theorem needs. Four neighbouring
rules exist (N240, E220/E221, H222, H007) and all fire (tests: `startexklusiv.rs`,
`vertragsfuss.rs`, `bau.rs`, korpus `H007`/`H008`), but the composition the goal
needs (`hvoll` + `hFrag` + `hFuss` jointly) has no producing rule and no wiring
from a `.gab` file to `P`/`fs`. The hand translation `r4P` is built by hand.

## 2. Joint satisfiability: YES, non-degenerate (probed, not believed)

Probe `.tmp/sonde143.lean` (not committed, per task), `./lean-probe`: **0 errors**.
Results:

- `ziel_ort_rahmen` prints with all premises used (each feeds the proof term; the
  file's CUTS-equivalent doc lists every premise's consumer: `GutO` in rely/frames,
  `RegLokal` in register/visibility steps, `hvoll`/`hFrag`/`hFuss` in the rely of
  head AND suspended frames via `rufG_rahmen`, `KoerperGutR` in `popR_ens`/`pushR_req`,
  `StartGut`/`StartExklusiv` via `exklusivG`, `e0` for fresh trace positions).
- `ziel_ort_rahmen_ref104` holds JOINTLY on the hand translation of
  `beispiele/104-referenz.gab`: memory `0 -> 100` (a step that changes memory),
  the `ensures` of `einzahlen` at its LOGGED return, conclusion on EVERY reachable
  machine. Non-trivial contract (`old(stand) <= stand`), two functions, real frame
  reasoning (`lies` declares no write). This is a non-degenerate witness.
- Axioms: `ziel_ort_rahmen`, `ziel_ort_rahmen_ref104`, `rennfrei_g_voll`,
  `frame_schritte_beschraenkt` ALL depend only on
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no extra axiom.
- `./lean-bau` full project: `Build completed successfully (103 jobs).`

The old vacuity defects are gone at the flagship: no premise quantifies over all
contracts/statements/expressions; `KoerperGutR` quantifies over handlers with an
inhabited domain; contracts sit at entry/return with actual logged values
(`audit_cross_thread_return`: thread 0 returns 100 written by thread 1).

## 3. Outside the covered fragment (counts over 91 files in `beispiele/`)

Covered by `ziel_ort_rahmen`: `gOk` bodies in the widened fragment (loops, exits,
reasons, axioms, indirect calls under `KandOk`, register reads and `awaits` under
`RegLokal` + `fussOrtGB`), on declarations WITH at least one carrier, from an
exclusive start, with signature-held guards.

| Outside construct | Count (surface heuristic, `grep -l`) | Status |
|---|---|---|
| Carrier-less declarations (no `table`/`global`/`lock`/`register` at surface) -- no `e0`, theorem says nothing | 28 files (list in MUSE-REPORT-143.md) | TOTAL gap; many are test/grammar files, but the exclusion is structural, not incidental |
| No surface `table` | 38 files | Heuristic only; some have other carriers |
| Same lock-holding routine on two threads (`StartExklusiv` excludes) | `concurrent` in 2 files (104, 108); same-function threading is the ordinary shape the premise bans | Documented counter-lemma, no repair |
| Locks-block-only readers (guard taken in `locks`, not held by signature) | `locks` in 26 files -- how many of those rely on block-taken guards for footprint/device carriers is NOT counted (needs per-program analysis) | TOTAL gap for those readers |
| Non-local oracles (device answers depending on undeclared state, `publishes` payloads) | Not a surface-countable property; `register` in 9 files, `atomic` in 10 | `ziel_ort_voll` for non-local oracles stays as proved WITHOUT registers/awaits; flagship needs `RegLokal` |
| Reason (`grund`) answers | `reason` carriers widespread; any callee that fails with a reason gives the caller NO contract and NO frame in the obligation | By design, unnamed in the goal slogan |
| Per-slot frames (callee writing one slot may have changed the whole table for the caller) | Affects every table callee; count = every program with table calls | Whole-carrier frames only, no finer grain |
| Indirect calls outside `KandOk` | 1 file matches pointer-call heuristic | Narrow admission |
| Stuck states (false invariant, spent budget, `leave`/`next` in `else`, unmet `awaits`) | Uncountable statically | Vacuous satisfaction: G does not step, `VertragAmOrtG` covers logged steps only |
| Traverse (13 files) / forever (7) / awaits (8) reached runs | Step rules exist; `traverse`/`awaits` reached runs now exist (`TravAwaitsLauf.lean`: `rennfrei_g_voll_zeuge`); adequacy converse still loop-free fragment only | Partially closed since the last audit; adequacy gap remains |

## 4. The four goal legs

- **Memory safety: PROVED for the fragment, with a named boundary.** Lock-guarded
  carriers are held across accesses (`zugriff_haelt`, `HeldGenau` on every memory
  step, `rufG_haelt_statisch`, `exklusivG`); the frame fact `rufG_rahmen` delivers
  callee frames from the machine. Boundary: whole-carrier frames, unshared
  carriers are checker duty (`PCUnsharedSep`, Lean-pending D2-family), oracle reads
  record no access events.
- **Race freedom: PROVED in full form on G (`rennfrei_g_voll` + `keine_datenrasse_g`),
  deliberately partial by design.** Every pair of accesses (reads included, any
  distance) to a lock-guarded carrier is ordered through release/acquire
  (`GeordnetG`), joint witness exists. By design excluded: read-involving pairs as
  *races* (needs a write by definition), atomics (`AtomarAusgenommen`), published
  payloads (`PaarungAusgenommen`), unguarded/unshared carriers, oracle-internal
  reads. The "race freedom" in the slogan therefore means "no unordered
  write-involving pair on a guarded carrier" -- true, but narrower than the word.
- **Contracts at place in concurrent runs: PROVED (`vertragAmOrtG` on every
  reachable machine).** Entry/return logging with actual values, place-check repair
  built in, cross-thread witness. Deductions priced honestly: `KoerperGutR`
  quantifies over ALL frame-respecting register-local oracles (user's sequential
  proof must survive adversarial register answers that change between reads);
  reason returns carry no contract; adequacy relates the machine to the
  contract-ignoring `rufRumpf`, never to the checking `rufAt`, so sequential
  contract reasoning reaches G only through the handler record.
- **Time: NOT carried -- bounded steps only, no time.** `frame_schritte_beschraenkt`
  / `kosten_passt_deklaration` / `frame_schritte_pruefer` bound a frame's OWN STEPS
  (relative to depth/budget, plus scheduler assumption for waiting). Waiting
  (locks held by others, unmet `awaits`) is a named-but-unproved scheduler
  assumption; termination is not shown (bound until return, not return itself);
  steps are not cycles and the Lean number is not the checker's number (F1-F9
  findings, remainder `zusatz`). "And time" in the goal is the least-reached leg:
  what exists is cost bounds, not timing.

## 5. Machine G is NOT linked to the emitted C

Translation validation is planned, not done. Concretely:

- No theorem relates `RufMaschineG` steps to anything the emitter (`emit.rs`)
  produces. The lowering leg of the old goal family is numeric only
  (`proPrimitiv <= 18` counts C forms; says nothing about the 30 undecided forms
  in real output, count preservation lives downstream in `Budget.lean`).
- `kostenK` is a HAND READING of `kosten.rs` over the Lean syntax, not extracted
  from the checker; the correspondence (`spiegel_*`, `frame_schritte_pruefer`) is
  only as good as that reading, and forms without a checker number in the Lean
  term (`retry`, `forever`, axioms, indirect calls, `transition`, ...) are outside
  it. Findings F1-F9 document places where the checker undercounts what G does
  (assignment target indices, `narrow` subjects, `traverse` invariants, recursive
  calls costing nothing, ...).
- Meaning for the claim: every "proved" above holds about runs of the Lean
  machine G over hand translations (`r4P`) or generated witnesses. Whether the C
  the toolchain emits for a user's `.gab` file behaves as G does is supported by zero theorems. A user verifying against the Lean model trusts an unwitnessed
  correspondence at exactly the point where the compiler -- the most
  bug-dense component -- sits.

## 6. Verdict restated, with the separation list

**"Reached for the Lean model, not yet for the implementation."**

What separates the current state from "reached" (ordered by load-bearing weight):

1. **C linkage (heaviest):** translation validation G-to-emitted-C, or at minimum
   a proved correspondence for the covered fragment. Without it the theorems
   certify models, not programs as compiled.
2. **Checker wiring:** exact rules computing `programmImFragmentG`, `fussOrtGB`
   (as the composed predicate, not its neighbours), and the member list `fs`
   from each `.gab` file; a per-program pipeline from source to `P` so no hand
   translation stands between the user and the theorem. (N240/E220/E221/H222/H007
   exist and fire; the composition does not.)
3. **Cost/time honesty:** either bound waiting under stated fairness (needs the
   `held <= N` surface bound carried into `Deklaration` -- TARGET 4, "not in the
   model"), or drop "and time" from the slogan to "step bounds under scheduler
   assumption". Plus closing the F1-F9 undercounts so the checker's number means
   what the bound assumes.
4. **Fragment edges, named in the slogan's fine print:** carrier-less
   declarations, locks-block-only readers, non-local devices, reason-answer
   frames, per-slot frames, same-routine threading. Each needs either a theorem
   or an explicit "the language does not cover X" the user can read BEFORE
   writing code -- several already have counter-lemmas (`audit_same_lock_start_excluded`,
   `ziel_ort_form_falsch`, `ziel_ort_register_falsch`), which is the honest form
   of the boundary.
5. **Adequacy direction:** sequential contract reasoning reaches G only via the
   handler record (`rufRumpf`, contract-ignoring); a proved link to the checking
   handler (`rufAt`) and a loop-carrying converse would close the user's actual
   reasoning path.

Adversarial note: the strongest evidence FOR the project is
`ziel_ort_rahmen_ref104` -- a real corpus program's real contract certified
jointly, with the old obligation provably failing on it
(`r4_rahmen_echt_schwaecher`). The repair direction is right. What is missing is
not mathematics but connection: the theorems float above hand translations while
the compiler below is unverified. The distance is engineering and semantic
linkage, not a flaw in the proved statements -- but until items 1-2 close, "the
language carries it" overclaims: the Lean model carries it; the language does
not yet.

---
CUTS (this verdict file): proves nothing; it classifies and counts. Counts in
section 3 are surface `grep -l` heuristics over `beispiele/*.gab` (91 files),
not parser judgments; the locks-block-only-reader overlap and the non-local-oracle
spread are not statically counted. No existing file was changed; probe
`.tmp/sonde143.lean` is uncommitted scratch. `#print axioms` record: the four
goal-family theorems probed depend only on `[propext, Classical.choice, Quot.sound]`.
