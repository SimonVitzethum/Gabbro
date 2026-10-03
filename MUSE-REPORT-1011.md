# MUSE-REPORT-1011: Exact review of author 861 (copy propagation rule)

## CANDIDATE / VERDICT

- CANDIDATE: 861 `98002a0a44774614339863607dd8a9264da27a62`
  (base `b040b155159f47629542b0083e2f0a8a607f2b4c`, matches this clone's HEAD;
  branch `muse/1011` verified; snapshot files: `MUSE-REPORT-861.md`,
  `grammatik/Grammatik.lean` (one-line import), new
  `grammatik/Grammatik/X86/OptFoldCopy.lean` (288 lines)).
- VERDICT: ACCEPT (bounded: source-level `Endblock.bind` rule lemma only;
  no lowering, byte, TSO/GX, cost-bound or silicon claims — all in CUTS).

## What was inspected

- Full read of the pinned candidate file (all 288 lines), the pinned
  OWNER-TASK.md, MUSE-REPORT-861.md, PATCH.diff (all 403 lines; tail
  identical to the candidate file), BUILD-EVIDENCE.json (14 entries),
  SNAPSHOT.json, and `.tmp/HARDWARE-REFERENCES/REFERENCES.json`
  (Intel SDM 325462-093US metadata; the candidate makes no byte-level
  claim, so no manual cross-check against the SDM was required).
- Grep over the candidate for
  `sorry|admit|axiom|native_decide|unsafe|intro _|have _ :=`: only benign
  hits ("admitted" in prose, `#print axioms` lines). No `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe`; no discarded premises.
- Patch scope: only the three owned paths. No source/checker/Spec/goal/
  emitter edits, no friend-reserved optimiser files, no diagnostic/gift/
  example/CLI numbers, no MARKE_EMIT changes.

## Semantic findings

1. `copyVar_wert`: conclusion is `hEq hz` (modus ponens on the
   validator-recomputed, admission-conditional equality). Not a vacuous
   restatement: `hEq` is stated for the SPECIFIC use environment `rho`
   (the universal form would be false), mirroring the accepted const-fold
   lane pattern. Sound.
2. `OptFoldCopy_verbindung`: genuine connection, not a restatement. The
   `execEnd` equality on the `bind` window is derived by unfolding the
   `bind` semantics (`show ... .schrumpf = ... .schrumpf`) and rewriting
   with the value equality — kernel-checked per build evidence. Fault
   preservation (same constructor/successor worlds), downstream contract/
   call-log agreement, and concurrency (via `orte` equality) follow from
   the proved outcome equality; budget unchanged is argued from identical
   block shape with a pure unbudgeted read (formal level-(c) bound OPEN,
   recorded in CUTS — honest boundary, not fake closure).
3. Refusals: all four citations proved to refuse (`simp` over the decided
   Bool conjunction), including the DESIGN failure case
   (`copyVerweigert_neudef`), plus three decided probes. The dominance/
   avail/no-redefinition Bools carry no semantic weight in the proof
   beyond admission gating — conservative and explicitly documented
   (validator recomputes `hEq` per use); no invented analysis trust.
4. `copyGleit_passt`: bit-identical copy, `rw [h]` — no recomputation, no
   rounding scope crossed. Sound; no IEEE overclaim.
5. Witness `OptFoldCopy_verbindung_zeuge`: all premises jointly
   instantiated (two `.int 0 10` slots both `7`, `hEq` by `rfl`, `leave`
   continuation) on non-degenerate `refD` with `refEin_schreibt`,
   `refB_erreicht`, `refB_schreibt` (reached F-machine run `MB`, slot
   `0 -> 100`, memory-changing). Underscore binder names (`_hz`, `_hEq`)
   are existential names only; both are provided in the proof. Meets the
   inhabitation rule.
6. No guarantee weakening, no desired-simulation premise, no `ensures`
   derived, no refusal turned into a warning, no faulting form speculated
   above its guard. CUTS block is precise and matches the actual file.

## Build evidence (recorded, not reproduced — see blocker)

- Author's recorded `./lean-bau`: `== exit 0; 0 error line(s)`,
  `Build completed successfully (511 jobs)`, `Grammatik.X86.OptFoldCopy`
  built. `#print axioms`: `copyZulassen` axiom-free; refusal/`orte`/float
  lemmas `[propext]`; `copyVar_wert`, `OptFoldCopy_verbindung`,
  `_zeuge` within `[propext, Classical.choice, Quot.sound]` (the
  `gabbro_ziel` standard). Intermediate red `lean-probe` steps during
  authoring were repaired before the final green commit — honest
  incremental history, final state green.

## Blocker / honest partial status

- The `bash` tool was permission-rejected for read-only inspection
  commands in this lane, so I could NOT independently re-run
  `./lean-probe`/`./lean-bau`. Commit via `./commit.sh` worked:
  `92fa5455`, tree clean.
- No `./lean-bau` result line of my own exists for this lane; the
  acceptance rests on full static inspection plus the author's recorded
  complete-output evidence above.

## What remains open (not mine)

- Lowering to target blocks/bytes and the per-access bridge (lowering
  lanes); formal `totalCost`/level-(c) bound; TSO/GX/silicon/ABI claims;
  interprocedural avail — all carried in the candidate's CUTS.
