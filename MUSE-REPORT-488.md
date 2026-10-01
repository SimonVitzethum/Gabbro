# Muse report 488 — independent exact-candidate review of 408

- Clone verified: `/home/simon/Dokumente/gabbro-muse/a488`, branch `muse/488`. Match, proceeded.
- Candidate pinned: `d3ee31df0f396be69a687395ebe03e5bd88852ec` (base `0b3132b7`), files `MUSE-REPORT-408.md`, `dokumente/x86/AUDIT-WEAK-MEMORY.md` per `.tmp/review/SNAPSHOT.json` (`clean: true`). This is a NEW head after repair; the previous verdict on `50e799b6` (REPAIR for truncation) is superseded, not reused.
- Method: read `.tmp/review/author-408/OWNER-TASK.md`, `MUSE-REPORT-408.md`, `BUILD-EVIDENCE.json` (now 9 entries, including the repair commit), `PATCH.diff`, and the full `dokumente/x86/AUDIT-WEAK-MEMORY.md` (346 lines, ends with newline, no truncation marker). Re-checked every previous finding and all new sections against this clone's `grammatik/Grammatik/X86/` tree with scoped `*.lean` searches (no `.lake` build artifacts touched). No other clone read. No candidate files staged; tree stayed clean. No build needed (docs-only candidate); no `lean-bau` run owed.

## What was checked (first review, carried forward)

- Scope/ownership: candidate touches ONLY the two owned files. No Lean, model, goal, checker, emitter, ledger, or number-range change. Matches owner task (`OWN ONLY dokumente/x86/AUDIT-WEAK-MEMORY.md, MUSE-REPORT-408.md`). Pass, unchanged.
- Must-nots: no DRF-SC claim and no word-atomicity-from-bytes claim — verified by inspection. `tso_store_buffering` (TSO.lean:414), `sb_beide_laden_null` (:395), `sb_flush_aendert_speicher` (:406), `einzelbyte_atomar` (:445, width-1 only), `paket_reisst` (:459, two-byte tear), `LockSchritt` empty (:477) with `kein_lock_schritt` (:480) all present at cited lines. `Befehl` (Typen.lean:53-68) confirmed 14 constructors, 64-bit only. Pass, unchanged.
- Findings F1–F8 spot-checked against source and confirmed real consumer gaps, correctly assigned to bridge owners, no invented bugs, no pre-judging of unmerged lanes 344/350, scoped around scheduled lane 421. Pass, unchanged (head sections byte-stable per the repair diff stat: 105 insertions, 2 deletions, all in the tail).
- No vacuity/forgery/safety issue: no theorems added, so no witness or `#print axioms` owed; no benchmark or axiom evidence claimed; no IR duplication, no guarantee weakened. Pass, unchanged.

## Re-review of the repair (new in this head)

- Truncation fixed: the audit file is now 346 lines / 19741 bytes, ends with `...not to this document.\n` (trailing newline present), and contains no `truncated` marker — the only `truncated` occurrences in `PATCH.diff` are legitimate prose in the report's repair section describing the old defect. The F9 task sentence is complete (refusal posture kept, `Spec.lean` fallback marked as decided by the simulation proof, not here). Pass.
- F10 (word atomicity) restored and verified: `einzelbyte_atomar` width-1, `paket_reisst` two-byte tear, `lock_xadd_atomar` (LockedOps.lean:145) under the `ausgerichtet8` guard plus empty-buffer precondition (a profile contract, as the audit states), `paketAtomarMoeglich` (TSO.lean:433) predicate-only. Ownership correctly deferred to scheduled lane 421. Pass.
- F11 (no DRF-SC) restored and verified: no `DRF`/`drf_sc`/`DRF_SC` mention anywhere under `grammatik/Grammatik/X86/*.lean` (scoped search, zero hits); `sb_erlaubt` / `sb_sc_verboten` confirmed at `Speichermodell/Sicht.lean:446/566` exactly as cited (audit writes `Sicht.lean:446/566`, unambiguous by theorem name). The `schwach_ist_gX` per-carrier agreement read as proof obligation, not assumption, matches the source shape (`hlokK` premise, AtomarW.lean:281, checked in the first review). Pass.
- Non-findings (§3), prioritized task list (§4), and CUTS restored. CUTS honestly states the audit proves nothing in Lean and now quotes the F2 probe cases inline (two `none`-by-`decide` negatives plus the `lockStart` empty-buffer positive control) — this answers the first review's minor evidence note. `lockStart` (LockedOps.lean:294, buffers `fun _ => []`) supports the quoted positive control. Pass.
- Report corrected: `MUSE-REPORT-408.md` now carries a "Repair after independent review 488" section that accurately describes the old truncation and the fix; the F1–F11 + non-findings + CUTS claim is now true of the delivered file. BUILD-EVIDENCE entries 8–9 document the repair diff and commit (`d3ee31df`). Pass.
- Previous blocking defect is closed. No new defect found. The bounded claim "docs-only F1–F11 weak-memory audit with non-findings and CUTS" is precisely delivered.

## New definitions/theorems

None. Docs-only review; nothing to witness and no `#print axioms` owed.

## Last build result

No `./lean-bau` run: neither the candidate nor this review touches Lean. No `./cargo-pruef` / `./emission-pruef` run: docs-only. Verification was scoped source reads plus the candidate's quoted 0-error `./lean-probe` run (BUILD-EVIDENCE entry 5).

## What remains open

- The audit's bridge findings F1–F10 remain work for their assigned owners (combined TSO+LOCK machine, drain scheduling, footprint unification, `GetrenntK` rename, alignment lemma, TableLayout C1, NarrowOps A1, binding contracts, lane 421); this review confirms they are consumer gaps, not proved-claim bugs, and takes no position beyond that.
- Nothing open on candidate 408 itself.

## Task correctness

The lane task is sound. The repair cycle worked as designed: the defect (cut-off single write) was found by exact review, fixed in small edits, and re-verified at the new head.

CANDIDATE: 408 d3ee31df0f396be69a687395ebe03e5bd88852ec
VERDICT: ACCEPT
