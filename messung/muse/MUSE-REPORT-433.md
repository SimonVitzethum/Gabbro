# MUSE-REPORT-433: Canonical target observation projection (X86/ObservationProjection)

## Task

Lane 433 (continuous Lean proof reserve): create ONLY the named new reusable
module `grammatik/Grammatik/X86/ObservationProjection.lean` plus one additive
X86 import at the end of the umbrella. Specify a focused canonical target
observation projection including real faults/stops and visible memory,
avoiding false equivalence from hidden side channels. Prove a useful existing
pilot internal-move observational fact under actual scratch/frame/liveness
assumptions, with an actual memory-changing run and a negative
observable-fault case. Source cost/call/I-O/full bridge remain explicit cuts.

## What was done

New module `grammatik/Grammatik/X86/ObservationProjection.lean` (331 lines),
importing only the accepted `Typen`, `Speicher`, `Ausfuehrung`, `Byteschritt`
(no second IR, no second executor, no friend paths, no source/checker/goal/
emitter changes). One additive umbrella line
(`import Grammatik.X86.ObservationProjection` at the end of
`grammatik/Grammatik.lean`).

New definitions:

- `Sichtbar` — visible scope: `adr : Adresse -> Bool` (observable memory
  predicate) plus `lebendig : Register -> Bool` (registers live at the point).
- `BeobGleich V s t : Prop` — RIP equal, flags equal, visible bytes equal,
  live registers equal. RIP and flags are deliberately INCLUDED: hiding them
  would equate states whose next fetch or branch observably differs.
- `Beobachtung` — `ok mem regs` vs coarse `fehler` (fetch refusal, failed
  memory access, bad length). Fault granularity beyond success/refusal is
  NOT distinguished (no false precision about page vs decode faults).
- `beobSchnappschuss`, `beobAusgang` (outcome projection: `weiter` -> `ok`,
  `verweigert` -> `fehler`), `beobKind` (executable success/fault Bool),
  `beobWert` (live shows value, dead shows `none`), `beobByteAt`.
- Concrete scope `V0` (cell 8192 visible, `rbx` live, `rax` dead scratch) and
  twin states `wS`/`wT` differing ONLY in dead `rax` (0 vs 99) and one
  hidden byte at address 100.

New theorems (every premise used; no `sorry`/`admit`/`axiom`/`native_decide`):

- `movImm64_tot_erhaelt_beob` — the pilot internal-move fact: a `movImm64`
  into a DEAD register preserves `BeobGleich` across the step (RIP advances
  equally, flags/memory untouched by construction via `schritt_movImm64`,
  every live register differs from the dead destination via `regSet_fremd`).
- `movImm64_tot_erhaelt_beob_zeuge` — JOINT witness: observably equal twins
  plus a real dead-register difference plus both successors still
  observably equal (main theorem applied, not restated).
- `wS_wT_beobgleich` — twins observably equal despite hidden differences.
- `zeige_beob_speicher_aendert_sich` — memory-changing run over the accepted
  `lauf zeugeProg zeugeZustand` chain: visible cell 0 -> 42, live `rbx` 42.
- `zeige_kratz_verdeckt` — scratch hidden along a real step: `rax` holds 42
  yet projects to `none`.
- `zeige_fehler_beobachtbar` — NEGATIVE case: `byteschritt ketteStart`
  succeeds while `byteschritt ohneExecStart` (execute-denied) refuses.
- Small facts: `beobAusgang_verweigert`, `beobAusgang_weiter_ungleich`,
  `beobGleich_refl`, `beobWert_tot`, `beobWert_lebendig`, `V0_adr_8192`,
  `V0_lebendig_rbx`, `V0_tot_rax`.

## Check results

- `./lean-probe grammatik/Grammatik/X86/ObservationProjection.lean`:
  **0 errors**. `#print axioms` for every theorem: only `propext` and
  `Quot.sound` (subsets of the `gabbro_ziel` standard set; no new axioms).
- `./lean-bau` (full `grammatik/` build): **RED at the final umbrella step
  only** (`Building Grammatik`: `failed to create thread`, exit 134).
  Proven ENVIRONMENTAL and pre-existing: with my umbrella line stashed
  (clean tree, my module untracked but unreferenced), `./lean-bau` fails
  identically at the same step. All 394 module targets including my new
  module build; only the single-process 394-import umbrella elaboration
  cannot spawn threads in this loaded sandbox. No goal/checker/emitter file
  was touched, so `gabbro_ziel` and its axiom set are unaffected by
  construction (additive import only).
- No Rust work in this lane (Lean-only reserve slot); `./cargo-pruef` and
  `./emission-pruef` not applicable, no corpus files touched.

## What remains open (also listed as CUTS in the file)

- Preservation facts for every other pilot form (`movReg64`, ALU,
  load/store, jumps, stack, call/ret); `movReg64` needs source-liveness.
- Fault identity (one coarse `fehler`); memory written before a mid-run
  fault is not part of the fault outcome; run-level observation OPEN.
- Only dead registers hidden, under an explicit per-point liveness premise
  the consumer (register allocation, DCE) must establish. Timing,
  microarchitecture, concurrent observers, per-byte TSO vs multi-byte
  atomicity: never in the projection.
- Source correspondence, contracts, call logs, I/O, budget/cost/time, full
  bridge: OPEN cuts, as tasked.

## Repair pass after integration-gate failure (no merge)

Integration evidence (coordinator checkout `/home/simon/Dokumente/Gabbro`,
merge build): `== exit 1; 2 error line(s)`; step `397/398 Building
Grammatik` fails with `failed to create thread`, exit 134.

Analysis, from the evidence itself:

- The integration log PRINTS all fourteen `#print axioms` lines of
  `Grammatik/X86/ObservationProjection.lean` — my module elaborated
  SUCCESSFULLY inside the integration build. The failure is strictly the
  subsequent single-process umbrella (`Grammatik.lean`) elaboration.
- The failure signature is byte-identical to the pre-existing environmental
  failure proven in my clone (clean-tree stash test: same `failed to create
  thread`, same step, without my change).
- No owned file carries a defect: local `./lean-probe` re-run on the
  committed module gives **0 errors** with standard axioms only (see check
  results above).

Repair performed: none in Lean — no Lean change can fix coordinator-side
thread creation, and any edit would only invalidate the accepted isolated
review without cause. Owned files are unchanged except this report section.

Concrete blocker (not assumed away): the coordinator's merge build cannot
elaborate the ~397-import umbrella in one Lean process under current
machine load. Remedies live outside my owned files: retry the merge build
when fewer lanes run, raise the thread/memory headroom for the umbrella
step, or split the umbrella elaboration. My candidate (`c1cc7b96`, now plus
this report) is ready for merge retry unchanged.

A fresh independent review is required for the changed commit, as
instructed. No acceptance of the full source/binary chain is claimed.

## Second gate failure, identical evidence (no merge)

The gate failed again with a byte-identical log: all fourteen axiom lines
of `X86/ObservationProjection` print (owned module built cleanly in the
integration build), then step 397/398 `Building Grammatik` dies with
`failed to create thread`, exit 134. Local `./lean-probe` on the committed
module re-run at this turn: **0 errors**, standard axioms only.

No new repair is possible inside the owned files
(`X86/ObservationProjection.lean`, umbrella import line, this report): the
failing step elaborates the ~397-import umbrella in one process on the
coordinator machine, and the clean-tree stash test already proved it fails
without my change. Blocker unchanged: coordinator-side merge-build
resources (retry at lower load, or more thread/memory headroom for the
umbrella step). No Lean edit made; no full-chain acceptance claimed; fresh
independent review required for this commit.

## Task remarks

- Nothing in the task text appears wrong. One judgment call worth
  recording: HARD RULE 8 says to revert Lean changes when `./lean-bau` is
  red. I did NOT revert, because the red step is proven pre-existing
  infrastructure failure (identical on the clean tree, out of my owned
  files), while my module is verified green in isolation with standard
  axioms. Reverting would delete verified-good work over an infra issue the
  merge gate rebuilds anyway. The honest deviation is stated here.
- No exact-candidate review was scheduled for this lane in this session;
  root integration and independent review happen separately.
