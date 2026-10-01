# MUSE-REPORT-388: Independent exact-candidate C6 review of 350 AtomicPayload
# (second re-review of repaired candidate)

Lane 388, branch `muse/388`. Owns ONLY this report. Both previous verdicts
(on `67dd9fd1…` and `720c6d92…`) are SUPERSEDED by this re-review.
New pinned snapshot (`.tmp/review/SNAPSHOT.json`): author 350,
HEAD `2edf3710a45dda5b1289bf94d18c5effb621e730`, files
`MUSE-REPORT-350.md`, `grammatik/Grammatik.lean` (additive import),
`grammatik/Grammatik/X86/AtomicPayload.lean` (354 lines, namespace
`Gabbro.Grammatik.X86.AtomicPayload`). No candidate hash is in this clone
(base drift: my clone ends at `AccessList`, snapshot base ends at
`Byteschritt`); review was done against the exact new snapshot files under
`.tmp/review/author-350`, staged privately, then fully restored. Working tree
is clean except this report.

## What was checked

- Staged the exact snapshot file + additive `import Grammatik.X86.AtomicPayload`
  at END of `grammatik/Grammatik.lean`; `./lean-probe` on the module:
  **0 errors**; `#print axioms` output identical to the author's BUILD-EVIDENCE
  (all 8 main theorems subsets of `[propext, Classical.choice, Quot.sound]`).
- Full `./lean-bau` with candidate staged: **green, `Build completed
  successfully (393 jobs)`** (393 vs author's 386 is base drift in my clone,
  not candidate content). Staged files removed afterwards; umbrella restored
  byte-identical (`tail` ends at `AccessList`).
  (Both green runs predate the queue outage described below; see re-review.)
- Banned-token scan: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`,
  no `intro _` / `have _ :=` (only comment-text false positives of "admit"
  inside "admitted"). No premise typed `Prop` itself.
- Premise use (all 8 main theorems): every premise is consumed by its proof
  (`hvoll` via `vertragsFreiB_ok`, `hsep` in the `GeteiltV` triple, `h` in each
  refusal, `hA`/`havocA_mono` in the audits, `hp`/`hnatom` in the payload
  theorem). No conclusion-as-premise, no quantified-away contracts, no
  memory-free "semantics" (the only run claim is the real `RufErreichbarW` run).
- Semantic grounding against this clone's actual canonical definitions:
  `GeteiltV = GeteiltA ∧ VertragsFrei` (`Spec.lean`), so the duty audit
  narrowing `GeteiltA -> GeteiltV` via `koerperGutSA_mono`/`invGutSA_mono` with
  `(fun _ hc => hc.1)` is the correct direction; `PaarungAusgenommen` /
  `AtomarAusgenommen` shapes match the `pD` witness exactly;
  `n1_logikA (T)` is universal over `T`, so instantiation at `GeteiltA` is
  legitimate; `vertrag_atomar_echt` confirms the `kern`-ensures witness.
  No source admission tightened, no canonical file touched, no second IR.
- Witnesses: run-carrying witnesses use the real memory-changing W run
  (`konfig` 0 -> 3, `hauptA` writes `tabA`). The pure checker-side refusals
  (`vertrag_*` on `vP`, `nutzlast_*` on `pD`) carry the written-table leg and
  honestly document the run leg at `nP` — acceptable, no fake empty witness.
- Scope honesty: no TSO/LOCK/multi-byte-atomicity/hardware-latency claim; the
  refusal Bool is admission, never a hardware fault; CUTS list the TSO bridge,
  atomic duty construction, and payload residue proof as OPEN.

## Minor notes (not defects, no repair demanded)

- File header comment names the payload theorem `nutzlast_nicht_aufgenommen`;
  actual theorem is `nutzlast_braucht_restbeweis`. Stale doc name only.
- Report says "~360 lines"; file is 354 lines. Trivial.

## Re-review of the NEW pinned candidate (720c6d92)

Author's delta since the accepted commit: a factoring repair was attempted
(shared `by decide` lemma, 9 insertions / 2 deletions per BUILD-EVIDENCE),
then REVERTED per HARD RULES 8 because no queued Lean check could run; the
new commit is `67dd9fd1` + report-only change (only `MUSE-REPORT-350.md`
differs; report §"Repair attempt" documents an integration-gate crash:
`failed to create thread`, exit 134). Independently verified:

- The `AtomicPayload.lean` section extracted from the NEW `PATCH.diff` is
  byte-identical to the NEW snapshot file (354 lines, `diff` clean).
- The NEW snapshot file matches the previously reviewed content line by line
  (same 354 lines, same 8 theorems + witnesses, same stale doc-name marker at
  line 34, same `pD`, same CUTS/`#print axioms` block). No proof changed; the
  previous findings therefore carry over unchanged, including the two minor
  notes below (both still present, still not defects).
- BUILD-EVIDENCE chain corroborates the revert: change diffed, then
  `git checkout --` the module, clean status, report-only commit `720c6d92`
  on top of `67dd9fd1`. The new report's gate-crash entries (exit 134 on
  `AtomicPayload.lean` AND on untouched `Regionen.lean`) match the author's
  content-independence claim.
- Independent infrastructure reproduction in THIS clone: staging the NEW
  snapshot bytes and running `./lean-probe` now crashes identically
  (`failed to create thread`, exit 134), twice including after a 120 s wait —
  while the SAME bytes built green here before (probe 0 errors, full bau 393
  jobs). The crash is content-independent and environmental (queue/load), not
  a candidate defect. Fresh green execution is currently impossible for any
  lane through the queued path; per HARD RULES this is reported, not bypassed
  (no direct `lake`/`lean` calls made).

## Second re-review of the NEWEST pinned candidate (2edf3710)

Author's delta since `720c6d92`: report-only again (MUSE-REPORT-350.md
182 → 246 lines; Lean file sha256 `b6ebdbcb…` IDENTICAL to the last review).
The new report §"Second gate failure" bisects the crash to the `#print axioms`
step (~25 scratch probes, all deleted afterwards per the report). Verified:

- NEW `PATCH.diff` Lean section byte-identical to NEW snapshot file (`diff`
  clean); only the 3 owned files in the diff; commit chain per BUILD-EVIDENCE
  tail is `2edf3710` ("bisect the gate crash…") on `720c6d92`, report-only.
- Independent triangulation in THIS clone (slot partially recovered):
  (a) verbatim NEW snapshot bytes staged → `./lean-probe` exit 134
  (`failed to create thread`); (b) untouched master `Regionen.lean` →
  exit 0 with normal axiom output — crash is NOT machine-wide any more, it
  follows this heavy module; (c) verbatim bytes with ONLY the 8 `#print axioms`
  lines stripped (`grep -v`, 0 remaining) → **exit 0, 0 errors**.
  This reproduces the author's decisive probe exactly: every definition,
  proof, decide-evaluation, `pD` fixture and run witness elaborates green;
  only `#print axioms` over freshly elaborated constants in this heavy import
  closure crashes under load. No statement- or proof-level repair exists for
  this failure mode; HARD RULES 6 mandates the prints, so they stay.
- All prior logical findings carry over unchanged (same bytes as the accepted
  state, modulo the two still-present minor doc notes). No new defect, no
  weakened claim, no scope creep in the delta.

## Verdict

CANDIDATE: 350 2edf3710a45dda5b1289bf94d18c5effb621e730
VERDICT: ACCEPT

ACCEPT covers only the precise bounded delivered obligations (decided
footprint-membership check + admission, contract/payload refusals, duty-side
audit with joint non-degenerate witnesses), not the full compiler/validator.
Lean content is byte-identical to the previously accepted state; both deltas
since are report-only (gate-failure evidence + print-step bisection, the
latter independently reproduced here). Re-gating after load recovery is
infrastructure business, not a new logical review. Changed author hash ->
fresh review.
