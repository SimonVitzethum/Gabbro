# MUSE-REPORT-1025: Exact review of author 875 (vectorisation gate rule)

CANDIDATE: 875 bdc0c06a701e128bca827ad33d5bab71c7dc745b
VERDICT: ACCEPT (bounded; scope exactly as stated in the candidate CUTS)

## What was reviewed

Exact pinned snapshot from `.tmp/review`: base `b040b155` (= this
review clone's HEAD, verified clean), three files only —
`MUSE-REPORT-875.md`, one-line `import Grammatik.X86.OptVectorGate`
appendix to `grammatik/Grammatik.lean`, new
`grammatik/Grammatik/X86/OptVectorGate.lean` (338 lines). PATCH
re-read in full; no other file touched (no diagnostic/gift/example/CLI
numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits,
no friend-reserved optimiser files). No source was modified by this
review; reproduction is by semantic re-derivation against base-tree
definitions plus the recorded probe/build evidence.

## Architecture check (byte forms, semantics, gates)

- No byte forms are claimed anywhere: no opcode/REX/width/flag
  behaviour, no source/destination/implicit-operand modelling, no
  pre-fault effects, no memory-access order, no feature/MXCSR/interrupt
  gates. The file stays at canonical lane values and 64-bit words and
  says so. Nothing to fault against the local Intel reference; no
  invented determinism, no zeroed/ignored defined effects.
- TSO/atomicity: the 128-bit tearing fact is not re-proved or
  hand-waved; it cites the accepted `vecWrite_teilt`
  (`X86/Vektor.lean:438`, verified present) and routes shared stores
  through refusal (`vecTorVerweigert_atom`, `vecTorVerweigert_geteilt`)
  plus CUTS. `simdFreigabe` stays `false` (`Vektor.lean:578/581`,
  verified). Sound abstraction, not closure.
- Canonical-execution interaction: the connection theorem keeps the
  scalar `bind` window's evaluated value and the full `execEnd`
  outcome over an arbitrary continuation `rest`, so downstream
  observations (contracts at their place, call logs, shared accesses,
  budget shape) travel through one equal outcome. No `ensures`
  derived, no refusal turned into a warning, no faulting form
  speculated above its guard.

## Proof substance (not just green)

- `vektorAdd_zugelassen`: replays the exact canonical rewrite chain
  (`BitVec.toNat_ofNat`, `addB_nat`, `laneGet_toNat`,
  `Nat.mod_eq_of_lt` via `laneMod_pos`/`laneMod_le`). I verified each
  named lemma exists in base `Vektor.lean` and that the `show` step
  is definitional (`laneGet` is *defined* as
  `BitVec.ofNat 64 (laneNat b v i)`, `Vektor.lean:90-91`). Its
  arithmetic content coincides with the unconditional `laneGet_add`
  (`Vektor.lean:247`); the added certificate/`hLane` premises serve
  the task-ordered validator-recomputation role, are all used in the
  proof, and are discharged by the real `laneNat_add` in the closed
  witness — no unsupported desired-correctness premise remains open.
- Refusals: all four gate-off cases proved (`spur`, `atom`,
  `geteilt`, `schwanz`), including the DESIGN failure case
  lane-disjoint-but-shared-observable. Negative probes by `decide`
  (`geteilt`, `atom`, missing block map); positive probes for the
  admitted gate and certificate and the b64 lane boundary (`5+7=12`,
  `3+4=7`).
- ZEUGE `OptVectorGate_verbindung_zeuge`: all premises jointly
  instantiated on non-degenerate `refD` (`3+4` folds to `7` under
  `bind`/`leave`, two admitted b64 lanes, `refEin_schreibt` table
  write beside reached memory-changing run `refB_erreicht` /
  `refB_schreibt`, slot `0 -> 100` — all names verified present in
  base `ReferenzB.lean`). The underscore-prefixed existential
  binders are all provided in the proof (`by decide` / `laneNat_add`);
  nothing is discarded, so HARD RULES 4(d) and 13 hold in substance.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`,
  no `intro _`/`have _ :=` (remaining grep hits are the substring
  "admitted" and `#print axioms` lines only); no `Prop`-typed
  premise; every premise of every theorem is used.
- Evidence coherence: BUILD-EVIDENCE shows the honest trail —
  intermediate errors fixed, final `lean-probe` 0 errors, full
  `lean-bau` 511 jobs green, closing `#print axioms` exactly
  `[propext, Classical.choice, Quot.sound]` for the connection and
  witness (one intermediate run showed `sorryAx`, repaired before
  the committed HEAD). `gabbro_ziel` files untouched.

## Bounds of this ACCEPT (per candidate CUTS, verified precise)

No native vector lowering (decoder/ABI/image, cross-lane fault
order, tearing correspondence against the per-access TSO bridge, FP
lanes, packed-access budget transfer, progress interaction); window
is integer `.int` binds with float agreement via the equal `execEnd`
outcome; no level-(c) machine-work bound (OPEN per lane 278); no
silicon/TSO/GX correspondence — correspondence stops at canonical
words and lane values. These match the file content exactly; the
claim is not bigger than the proof.

## Non-findings noted

- The task's "IEEE preservation" for a pure integer-lane rule is
  correctly carried by the unchanged outcome, as the author states.
- The shared-IR (lane 287) interface is still unaccepted, so both
  rewrite sides being source `Syntax`/`Semantik` fragments with the
  target cited at lane/word level is the honest scope, stated openly.

No repairs required. No guarantee weakened, no fake closure found.
