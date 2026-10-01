# MUSE-REPORT-388: Independent exact-candidate C6 review of 350 AtomicPayload
# (re-review of repaired candidate)

Lane 388, branch `muse/388`. Owns ONLY this report. Previous verdict (on
`67dd9fd1e6e00d9435a61a868308ef0f5192b156`) is SUPERSEDED by this re-review.
New pinned snapshot (`.tmp/review/SNAPSHOT.json`): author 350,
HEAD `720c6d92f786dc530e90ca5f15a0be037c8a680b`, files
`MUSE-REPORT-350.md`, `grammatik/Grammatik.lean` (additive import),
`grammatik/Grammatik/X86/AtomicPayload.lean` (354 lines, namespace
`Gabbro.Grammatik.X86.AtomicPayload`). Neither hash is in this clone (base
drift: my clone ends at `AccessList`, snapshot base ends at `Byteschritt`);
review was done against the exact new snapshot files under
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

## Verdict

CANDIDATE: 350 720c6d92f786dc530e90ca5f15a0be037c8a680b
VERDICT: ACCEPT

ACCEPT covers only the precise bounded delivered obligations (decided
footprint-membership check + admission, contract/payload refusals, duty-side
audit with joint non-degenerate witnesses), not the full compiler/validator.
Lean content is byte-identical to the previously accepted state; the only
change is the author's report (gate-failure evidence). Re-gating after queue
recovery is infrastructure business, not a new logical review. Changed
author hash -> fresh review.
