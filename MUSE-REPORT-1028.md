# MUSE-REPORT-1028: Exact review of author 878 (linear-scan allocation rule)

## CANDIDATE

878 `c48bbf5251533d8f90f2278022c3c10cb6d1c2f6` (base `b040b155159f47629542b0083e2f0a8a607f2b4c`)

## VERDICT: ACCEPT (bounded)

Bounded acceptance of the rule-lemma scope: linear-scan colouring against
recomputed liveness with colouring/spill certificate, and the fused 16-byte
spill refusal. The machine-level legs the owner task names (place-level
contracts, log-append, TSO-step, work-bound transfer into `CostSummary`)
are precise obstructions waiting on the not-yet-accepted IR-287 lowering,
filed as CUTS — demanding them here would force manufacturing the missing
lowering premise, which the architecture rules forbid. No repair required;
details below.

## What was reviewed

Exact pinned snapshot from `.tmp/review/author-878/`: `OWNER-TASK.md`,
`MUSE-REPORT-878.md`, `BUILD-EVIDENCE.json`, `PATCH.diff` (735 lines),
and the full new file `grammatik/Grammatik/X86/OptAllocLinear.lean`
(624 lines, read in three slices: 1-150, 151-390, 391-624).
Reference inputs: `.tmp/HARDWARE-REFERENCES/REFERENCES.json` (Intel SDM
325462-093US, Sept 2026; AMD unavailable, no AMD claim made — respected),
`DIRECT-COMPILER-DESIGN.md` §7 row (line 524) and §8 (lines 614-618),
`dokumente/x86/REVIEW-OPT-BINAER.md` CE-5.

PATCH scope is exactly three files: `MUSE-REPORT-878.md` (new),
`grammatik/Grammatik.lean` (one appended import line, correct placement),
`grammatik/Grammatik/X86/OptAllocLinear.lean` (new). No friend-reserved
optimiser files, no source/checker/Spec/goal/emitter edits, no new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes.

## Architecture checks (independent, against base `b040b155`)

- DESIGN §7 row match: "colouring vs recomputed liveness; spills fresh
  private frame slots" with failure case "fused 16-byte spill over two
  live carriers" — the candidate implements exactly this row (scan order
  + colouring + cited fusions + recomputed live sets + frame depth;
  general refusal theorem `allocFused_verweigert` plus decided instance
  `allocVerweigert_fusion`). The fused-spill hazard is independently
  grounded in `REVIEW-OPT-BINAER.md` CE-5, not invented.
- Byte forms / REX / flags / MXCSR / interrupts: N/A by construction —
  the lemma claims no instruction encoding, touches no flags, names no
  gates. Nothing to get wrong; nothing claimed.
- Registers: reuses canonical `regSet`/`regSet_fremd` (`X86/Ausfuehrung.lean`
  lines 33/144) and the pinned `rsp` via `reserviertReg`
  (`RegisterInterference.lean` lines 134/144/365) with a decided refusal
  instance (`allocVerweigert_rsp`). Register file total — no fault
  possible there, correctly stated.
- Width/memory: spill slots are 8-byte `Stapel` slots via `schlitzAddr`
  (`Stapel.lean` line 32); frame bound `s < depth / 8`; reload through
  permission-checked `read64` requiring a `lesbar8` premise
  (`allocSpill_behält` over `read64_nach_write64`, `Speicher.lean`
  line 327) — fault guarded, never speculated above the guard.
- TSO/atomicity: honestly OPEN in CUTS (slot-index separation proved;
  address-arithmetic bridge to footprint disjointness not claimed).
- Fail-closed admission: `homesDiffer` none-arms are `false`,
  `allocHomeOk` none-arm is `false`, `allocScanOk` requires coverage +
  sortedness; anything missing or conflicting is `false`, never a silent
  pass. `intervalsOverlap` over-approximates on empty intervals (demands
  distinct homes unnecessarily — conservative, not unsound); the author
  found this, added non-emptiness premises to `overlapHasPoint`, and
  recorded the check-side gap in CUTS. Correct direction, honestly filed.
- No invented determinism, no `ensures` derived, no refusal turned into
  a warning. IEEE leg is guard agreement on identical carried values
  (`gleitHeim_behält` rewrites `heq : qa = qb`; values carried whole,
  never re-rounded) — legitimate, not a quantified-away contract.

## Proof-hygiene checks (hard rules 3/4/6/13)

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `Prop`-typed
  premise, no `intro _` / `have _ :=` (grep over the snapshot file;
  hits were only comment text "admitted" and `#print axioms` lines).
- Every premise of every theorem is used — traced by hand, including
  the 8-premise connection theorem (admission via `allocOk_pair`,
  membership/overlap via `allocSeparate`, home equations into `hne`,
  `hWx`/`hWy` via `allocWort_rund`, `heq` by rewrite, all of
  `x y r0 wx wy qa qb lo hi σ₀ σ ρ` in the conclusions) and the general
  fused refusal (traced the `simp only [huv, hüber, … ha, hb, hf]`
  reduction to `false = true` + `absurd`; same shape for `allocSeparate`).
- Conclusion is not a restated premise; observers (`heimBeobachter_bleibt`)
  apply to actual carried values. File ends with CUTS + `#print axioms`
  for every main theorem. English only.
- Inhabitation: `OptAllocLinear_verbindung_zeuge` instantiates ALL
  premises jointly on non-degenerate `refD` (`refEin_schreibt` writer,
  `refB_erreicht` + memory-changing `refB_schreibt` on `MB`) — all names
  verified present in base (`ReferenzB.lean` lines 51/101/123/314/329/
  341/719/910/987/1007); idiom matches precedent (`ZeugnisStmt.lean:1059`,
  `X86/OptFoldConst.lean:271`). No Lean name collisions with base
  (`Home`, `Assign`, `Interval`, `spillAnzahl`, `OptAllocLinear_*` all
  absent from base).
- Negative mutations: four decided refusals (shared register, `rsp`,
  shared slot, fused 16-byte) + general fused theorem. Positives: three
  decided admissions, including adjacent slots without cited fusion and
  slot sharing for non-overlapping carriers. Non-degenerate overlap
  (`[0,10)` vs `[5,15)`) with a `decide`d admission.

## Evidence and methodological bound

Author's `BUILD-EVIDENCE.json` records `./lean-bau` green (511 jobs),
`./lean-probe` 0 errors, and standard `gabbro_ziel` axioms
(`propext, Classical.choice, Quot.sound`) for `OptAllocLinear_verbindung`
and `_zeuge`, including the intermediate repair trace (Bool-algebra
restructuring after `rewrite`/`omega` failures — credible). I could NOT
re-run the queued wrappers: shell execution is denied to this review lane
by the permission classifier, so no independent `lean-bau`/`lean-probe`
reproduction was possible. The verdict therefore rests on complete static
inspection of the exact snapshot (all 624 lines read), base-vocabulary
resolution of every referenced name, hand-traced proof reductions, and the
recorded build evidence. No finding emerged that required execution to
settle (all concrete instances are `by decide` over tiny inputs).

## What remains open (carried from the candidate's CUTS, endorsed)

No source-syntax rewrite leg, no per-access TSO/GX bridge, no
`CostSummary` work transfer; place-level contracts, log-append, TSO-step
and work-bound legs wait for the accepted IR-287 lowering. Source safety,
concurrency and budget guarantees are proved at value/home level only.
Correspondence stops at canonical words and decided admission Bools —
no silicon/ABI/loader claim. All within the owner task's scope; the
report states this plainly per hard rule 4.

## Owned files and commit status

Own only `MUSE-REPORT-1028.md` (this file). No source or live-control
changes made. Commit via `commit.sh` was NOT possible (no shell in this
lane); the file is written and ready — commit requires a shell step.
