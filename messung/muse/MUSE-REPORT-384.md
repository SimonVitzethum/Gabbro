# MUSE-REPORT-384: Independent exact-candidate C2 re-review of 346 GateStub

## Candidate under review (NEW PIN — previous verdict is stale)

- Author lane 346, NEW pinned HEAD `dabdb1771f215044dc7938e0dcd1d7c6ef6080be`,
  base `f737a6f04c22dfdd9499532e0535ad119cf2e56d` (per `.tmp/review/SNAPSHOT.json`).
- Owned files per snapshot: `MUSE-REPORT-346.md`, `grammatik/Grammatik.lean`
  (one additive import), `grammatik/Grammatik/X86/GateStub.lean` (443 lines).
- Delta vs previous pin `240846a7` (which got VERDICT: ACCEPT with an
  environmental full-build caveat): exactly ONE change — the integration-gate
  repair renaming `klassifiziere` (+ 5 `klassifiziere_*` theorems) to
  `torKlassifiziere` (`torKlassifiziere_*`), because master
  `X86/OverlapRefusal.lean` already owns `klassifiziere` and the gate failed
  with `environment already contains 'Gabbro.Grammatik.X86.klassifiziere'`.
  No semantics changed. This round re-reviews the renamed candidate only.
- Review run on branch `muse/384` at `66ce5933`. Staged privately in this clone
  (file copy + appended import), probed, build-attempted, then fully restored
  (`git status` clean apart from this report). No other clone read, no
  network, no push.

## What was checked

1. **Byte identity:** staged `GateStub.lean` diffed against
   `.tmp/review/author-346/grammatik/Grammatik/X86/GateStub.lean` → IDENTICAL.
2. **Rename completeness:** `grep klassifiziere` over the snapshot file shows
   only `torKlassifiziere` hits (def + 5 theorems + 2 joint-witness uses + 5
   `#print` lines); zero bare `klassifiziere` remains. Line count unchanged
   (443), consistent with a pure identifier rename.
3. **Collision plausibility:** this clone predates `OverlapRefusal.lean`
   (absent from `grammatik/Grammatik/X86/`, no `klassifiziere` anywhere in
   `X86/`), so the gate's collision cannot be reproduced here — but the rename
   eliminates any collision with that name regardless of what master holds.
   The new name follows the module's existing `tor*` convention
   (`torOkB`, `torStapelAntwortBelegt_verweigert`, …).
4. **Staged `./lean-probe grammatik/Grammatik/X86/GateStub.lean`: 0 errors.**
   Axioms all standard: admission/refusal/stub theorems depend on nothing or
   `[propext]`; `m140_*` on `[propext, Quot.sound]`; renamed
   `torKlassifiziere_*` on nothing; `torStub_zeuge` on
   `[propext, Quot.sound]`.
5. **Forbidden tokens:** `grep -nwE "sorry|admit|axiom|native_decide|unsafe"`
   → single hit is CUTS prose ("never a hardware axiom"), not a command.
   No `intro _` / `have _ :=` discards. No `: Prop` premise anywhere.
6. **Prior findings F1/F2:** untouched by this delta (C187 pool/occupancy and
   site-indexed M140 verified fixed last round; the rename affects only the
   decode classifier). Re-confirmed present and unaltered in the snapshot:
   `trampolinVorrat`, `freieTrampolin`, `torStapelAntwortBelegt_verweigert`,
   `m140_geschmiedet`/`m140_echt_kein_fund`/`m140_zahl_erlaubt` all present
   with identical statements.
7. **Merge mechanics:** snapshot's `Grammatik.lean` still predates the
   SpillPrivate merge (appends `GateStub` where this clone has `SpillPrivate`
   last) — trivial import-union conflict, auto-resolvable per the merge
   script. The rename additionally resolves the real `OverlapRefusal`
   duplicate-identifier conflict at integration.

## BLOCKER (environmental, unchanged, proven not candidate-caused)

- Full staged `./lean-bau` still cannot go green in this clone: Lean dies with
  `failed to create thread` (exit 134) under box-wide memory/thread
  exhaustion. New evidence this round: the build log shows ALL of
  `GateStub.lean`'s `#print axioms` lines (including the renamed
  `torKlassifiziere_*`) elaborating cleanly — the crash is again the
  `Grammatik` aggregate step only. Baseline control from last round stands
  (candidate removed → identical crash on `Grammatik` itself).
- The author's report independently confirms the same signature on their
  machine (385/386 modules incl. renamed `GateStub.olean` clean; aggregate
  step crashes; pristine-tree `git stash` control crashes identically) and
  honestly declares the aggregate step red.
- Backstop remains the merge-gate rebuild (`muse-merge.sh` builds `grammatik/`
  before committing).

## Findings

- No material findings. The single delta (rename) is correct, complete, and
  semantics-preserving; prior F1/F2 fixes intact; no new defects introduced.
- No observations beyond the standing merge-mechanics note above.

## Last check result lines

- Staged `./lean-probe`: `== 0 error(s) in the COMPLETE output; exit 0`.
- Staged `./lean-bau`: red — environmental thread exhaustion at the
  `Grammatik` aggregate step (see BLOCKER); `GateStub.lean` itself elaborates
  cleanly inside the build.
- Tree restored before this commit: `git status` clean except
  `MUSE-REPORT-384.md`.

## Re-review note 2026-10-01 (same pin, fresh evidence)

- Snapshot still pins `dabdb177`; candidate bytes unchanged
  (md5 `a86694e3889643ab237920e7940fe19c`, 443 lines, zero bare
  `klassifiziere`). Full substantive re-read of all 443 lines this round:
  N065/arity exact-once binding is a genuine bijection (length = n, Nodup
  indices, full `0..n-1` coverage); `stubEndsTrapB` cannot false-accept short
  stubs (Nat subtraction saturates, suffix compared against 2-byte trap);
  `torKlassifiziere` `lo`/`hi` are free profile parameters with provenance
  OPEN (recorded, not a defect); all prior F1/F2 statements present unaltered.
- Fresh execution, staged identically: `./lean-probe` 0 errors exit 0 with
  standard axioms; **full `./lean-bau` now GREEN —
  `Build completed successfully (387 jobs)`** (prior thread-exhaustion
  blocker resolved by calmer machine, not by any candidate change);
  `gabbro_ziel` probe 0 errors, still exactly
  `[propext, Classical.choice, Quot.sound]`.
- Static re-checks: one `axiom` token hit is CUTS prose only; no discards;
  no `: Prop` premise. Standing unresolved CUTS (unchanged, all openly
  stated in-file): callee-side obligation (c); trap semantics; bare-metal
  `int $0x80` clobber rule; M140 tag detection (`m1.rs`); kernel-side
  table/range/cost meaning; source-to-byte correspondence; scalar fallback
  as consumer obligation.
- Verdict unchanged.

CANDIDATE: 346 dabdb1771f215044dc7938e0dcd1d7c6ef6080be
VERDICT: ACCEPT
