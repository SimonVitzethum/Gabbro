# MUSE-REPORT-934: Exact review of author 784 (CAS retry attempt bound)

## Clone check

- Clone `/home/simon/Dokumente/gabbro-muse/a934`, branch `muse/934`: MATCH.
- HEAD `56537272a31df3de5d9b7898bbade91c3de817b8` equals the snapshot base. MATCH.

## CANDIDATE and VERDICT

- CANDIDATE: 784 `eda490e62ac0403ffd7650478072ffe598395763`
  (base `56537272a31df3de5d9b7898bbade91c3de817b8`).
- VERDICT: ACCEPT (bounded — see apparatus blocker below).

## What was reviewed

Pinned material under `.tmp/review/author-784/`: `OWNER-TASK.md`, `PATCH.diff`,
`MUSE-REPORT-784.md`, `BUILD-EVIDENCE.json`, and the exact new-file copy
`grammatik/Grammatik/X86/CasRetryBound.lean` (290 lines). PATCH was read in
full and matches the file copy line for line; the `Grammatik.lean` hunk is a
single added import line.

## Architecture verification (independent, against this clone at base)

- Byte form: `pinCmpxchg` is `F0 48 0F B1 8D disp32` = LOCK + REX.W +
  CMPXCHG r/m64, r64 at `[rbp+0]`. Matches the cited manual rows.
- Manual provenance verified at the exact cited lines of the clone-local
  snapshot (`intel-instruction-reference.txt`): CMPXCHG heading at line 46967
  with `REX.W + 0F B1/r`, RAX compare and ZF semantics; LOCK heading at line
  63495. The candidate's summary of both rows is accurate. The candidate
  correctly states the manual gives NO software-retry bound and carries
  contention as program data instead of inventing one.
- Every reused name resolves in this clone with a signature matching its use:
  `casSchritt`/`casKosten`/`lockAddr`/`lockStart`/`casNach`/`cas_fehlschlag_zeuge`
  (`LockedOps`), `decodeLock`/`decodeLockExt`/`decodeLockExt_lock`/`pinCmpxchg`/
  `pin_lock_cmpxchg_decodiert`/`pin_lock_ext_verweigert_cmpxchg`
  (`LockedInstructionExecution`), `decodeExt` (`ExtendedExecution`),
  `kostenSummeOk`/`kostenSummeOk_verweigert_unbegrenzt`/`blattSummary`/`retryTry`
  (`CostSummary`), `stutter_ohne_schranke` (`BudgetExecution`), `read64`
  (`Speicher`), `ziel_ort_einfaden_zeuge` (`ZielOrtEinfadenZeuge`, 8-tuple in
  the exact obtained order). `casKosten versuche = versuche + 1`, so the
  `n + 2` cost conclusion follows the `n + 1` length bound honestly.
- Proofs hand-checked: `fehlZaehler_angehaengt` (induction, both premises
  consumed, `show` step definitionally valid), `CasRetryBound_verbindung`
  (all four premises used: shape rewrite, exact charge count, contention
  bound via omega, summary linkage by rfl), `casWiederholung_ausgefuehrt`
  (first conjunct exactly the accepted failure witness; success/read-back/
  inequality by rfl/decide as in the accepted success witness),
  `casLaeuft_ueber_lock` (thin sound wrapper over `decodeLockExt_lock`,
  both premises used, no shadowed pilot row), both `rfl`-based divergence
  witnesses (record update only touches `retryBound`, so `blattSummary`
  facts carry over; `retryBoundOf .unbekannt` is definitionally `none`).
- Witnesses are non-degenerate: the connection witness reuses the
  table-writing fixture with its four-step reached run (`0 -> 5` slot move)
  plus a real memory-changing CAS install (`lockStart` vs `casNach` bytes
  differ). The divergence-refusal witness jointly exhibits unboundedness.
  No premise is discarded; no conclusion restates a premise; no contract is
  quantified away; nothing is called a semantics that cannot change memory.
- No forbidden tokens: scan of the pinned file finds no `sorry`/`admit`/
  `axiom` (outside `#print axioms`)/`native_decide`/`unsafe`, no `MARKE`,
  no `N[0-9]{3}` codes, no gift/example/CLI numbers. Scope is clean: only
  the new module, one import line, and the author's report. No
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files. `CUTS` block is precise and disclaims exactly what is not shown
  (per-site contention proofs, fairness/termination, timing, TSO/W/GX,
  faults). The charging premise (`fehlZaehler bs ≤ n`) is the task-required
  contention input, not a smuggled simulation assumption.
- Axioms per author's final probe output are within
  `[propext, Classical.choice, Quot.sound]` for every theorem (most
  `propext`-only); `gabbro_ziel` re-checked on the standard triple.

## Remark (not a repair)

- `casLaeuft_ueber_lock` is headed "FETCHED grounding" but proves
  decode-level routing (`decodeLockExt` vs `decodeExt`), not the fetch
  layer (rip/permission checks). The theorem statement, docstring, report
  body and CUTS describe exactly what is proved, so the claim boundary is
  honest; a future fetch-level connection stays open with its owner.

## Apparatus blocker (bounds this acceptance)

Independent Lean reproduction was impossible in this clone, for reasons
unrelated to the candidate:

1. `./lean-probe` on the pinned file copy fails at the first import with
   `failed to read file '.../Gabbro/.claude/muse-arbeit/x86/
   adaptive-lean-toolchains/ec4c64eba18eeec7/lib/lean/...'` — this clone's
   lake environment points at a nonexistent toolchain directory for
   out-of-tree files.
2. `./lean-probe` on an accepted in-tree file
   (`grammatik/Grammatik/X86/CostSummary.lean`) fails with
   `failed to create thread` — the known VA-space apparatus issue; a retry
   of the candidate probe hit failure 1 again.

Therefore this ACCEPT rests on exact static verification (above) plus the
author's recorded build evidence (incremental 0-error probes including two
fixed intermediate errors, full `./lean-bau` 485 jobs green, `gabbro_ziel`
axioms re-confirmed), not on a fresh Lean run in this clone. No source file
was touched here; only this report is owned and committed, so no build
state changes.

## Open

- Fresh `./lean-bau` / `./lean-probe` confirmation of candidate 784 in a
  clone with a working Lean apparatus (merge gate will supply it).
- Per-site contention proofs, fairness/termination, TSO-to-W/GX bridge,
  faults and timing remain with their owners per the file's CUTS.
