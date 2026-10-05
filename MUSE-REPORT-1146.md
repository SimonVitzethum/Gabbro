# MUSE-REPORT-1146: Exact review of candidate 1145 (TSO to W bridge: LOCK/RMW steps)

## Candidate identity

CANDIDATE: 1145 798e1e427252dcae33ffe50b9a6dd61f2d914e9a
Pinned head from `.tmp/review/SNAPSHOT.json`; base `f011761c7ab88ff57f9d7e684f0c57a2dd1b2b49`.
- Files in snapshot: `MUSE-REPORT-1145.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/TsoRmwBridge.lean` (`clean: true`).
- Review source inside this clone only: `.tmp/review/author-1145/PATCH.diff`
  (553 lines, read fully), `MUSE-REPORT-1145.md`, `BUILD-EVIDENCE.json`,
  `OWNER-TASK.md`. Author clone never touched (HARD RULES rule 1).
- Reviewer clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a1146`,
  branch `muse/1146` (HEAD `e586d98` at review time).

## What the candidate does

New file `grammatik/Grammatik/X86/TsoRmwBridge.lean` (437 lines) plus one
`import Grammatik.X86.TsoRmwBridge` line in `grammatik/Grammatik.lean`.
Bridge plug `tsoRmwAdapter` reuses accepted `adapterLockRmw` unchanged;
XADD / CMPXCHG-success / CMPXCHG-failure agreement, RMW atomicity
(`tsoRmw_kein_split`, `tsoRmw_kette_ohne_verlust`), four lifted refusals plus
fence-only non-RMW, cost shape without retry promise, and joint two-core
witness `tsoRmw_bruecke_zeuge` (word 10 to 15 to 22).

## Checks (each against the PATCH text and this clone's accepted tree)

1. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: PASS. Grep over
   `PATCH.diff` finds those tokens only in the report prose
   ("no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`"); the new Lean
   code has none, no `axiom` declarations, only `#print axioms` lines.
2. `#print axioms` standard: PASS. BUILD-EVIDENCE final probe lists every
   main theorem at `[propext, Quot.sound]` except `tsoRmw_kein_split` at
   `[propext]` — subset of the goal axioms, no `Classical.choice` needed,
   nothing beyond standard.
3. Existing files untouched except one import line: PASS. PATCH touches only
   the three owned paths; `Grammatik.lean` diff is exactly one added import
   line. Note base drift: snapshot base ends at `HwLockRmw`, this reviewer
   base ends at `HwFpControl` (line 634); integration must re-anchor the
   import at the file end, content unchanged.
4. Every premise used: PASS. Each agreement theorem feeds every guard into
   the cited accepted lemma (`hwLock_xadd_stimmt`,
   `hwLock_cmpxchg_ok_stimmt`, `hwLock_cmpxchg_nein_stimmt`); `tsoRmw_kette_ohne_verlust`
   consumes both guard sets via two obtains, `hstep1`/`hstep2` rewrites and
   `htgt`; `tsoRmw_kosten_gestalt` uses `a`/`delta`/`n` across the
   conjunction; `tsoRmw_kein_split` passes all three flags through.
5. Accepted evaluator lifted, not copied: PASS. `tsoRmwAdapter` is defined
   as `adapterLockRmw`; no new event/instruction type. The task letter asked
   for a new event type, but it already exists as accepted vocabulary
   (`LockAnweisung`, `LockEreignis`); redefining it would violate rule 16.
   Author notes this deviation explicitly. All cited producer names verified
   present in this clone: `adapterLockRmw`, `adapterLockRmw_wf`,
   `hwLockSchrittEv`, `hwLock_xadd_stimmt`, `hwLock_cmpxchg_ok_stimmt`,
   `hwLock_cmpxchg_nein_stimmt`, `hwLock_mfence_stimmt`, refusal lemmas,
   `RmwForm`, `CmpxchgErfolgForm`, `xadd_kosten_eins`,
   `xadd_guenstiger_als_cas`, `cas_schleife_unbeschraenkt`,
   `retryBoundOf_unbekannt`, `hwLockWitStart`/`hwLockWitStart_wf`/
   `hwLockWitBereit2`/`hwLockWitNach1`/`hwLockSicht`/sight and refusal pins.
6. Planted refusals really refuse: PASS. Four `..._bleibt_verweigert`
   theorems lift the matching `hwLock_*` refusals with identical guards;
   `tsoRmw_mfence_kein_rmw` admits the fence but pins `RmwForm [ev] = false`.
   The joint witness carries both plug refusals beside the run
   (`hwLockWit_puffer`, `hwLockWit_unaligned`).
7. Witness non-degenerate: PASS. `tsoRmw_bruecke_zeuge` conjoins
   `decide`-closed pins (ev1 RMW, reads 10, writes 15; ev2 reads 15, writes
   22; `RmwForm`), `HwWf`, owner-only forwarding (owner sees 99, other sees
   0 at the foreign address), and the two refusals. Two cores, two
   memory-changing steps, chained read-after-write. No program-syntax
   premise exists so rule 13 does not trigger mechanically; the `_zeuge`
   demand is met on the reached hardware run.
8. Silicon facts: PASS. No new silicon claim: provenance is the accepted 662
   module rows (LOCK/XADD/CMPXCHG); aligned whole-word atomicity stays a
   profile contract (`ausgerichtet8` + empty own buffer). Nothing to check
   against SDM extracts beyond reuse.
9. CUTS honest, no over-claim: PASS. CUTS lists exactly what is open —
   no per-access target-to-W/GX simulation (timestamp/value link,
   `SchrittW` `rmw` discharge stays with consumer lanes), no hardware
   correspondence beyond self-consistency, no fetched-byte dispatch, narrow
   widths/split-lock open, no source/checker/contract/budget/goal change.
   Report §"What remains open" matches CUTS. No W/GX or hardware-correspondence
   claim made.

## Build evidence

- Author BUILD-EVIDENCE: final `./lean-bau` green
  (`== exit 0; 0 error line(s)`, `Build completed successfully (628 jobs)`);
  two earlier attempts failed environmentally (`failed to create thread`,
  exit 134; `Bitblast.olean.private` read error) with a green retry and no
  file change — credible, documented, not proof content.
- Reviewer base build (this clone, candidate NOT applied):
  `./lean-bau 2>&1 | tail -4` ends with
  `Build completed successfully (631 jobs).` (628 → 631 is base drift: newer
  master modules after `HwLockRmw`). No candidate build run by the reviewer
  (report-only review owns no Lean file); the candidate's own green evidence
  plus 0-error `lean-probe` lines stand uncontradicted.

## Decision

VERDICT: ACCEPT

Author lane 1145 at pinned head `798e1e42` is accepted as reviewed: exact
scope, lifted (not copied) producer API, all premises consumed, standard
axioms, refusals and non-degenerate two-core witness present, CUTS honest
with no W/GX or hardware-correspondence over-claim. Integration note: re-anchor
the single import line at the current end of `grammatik/Grammatik.lean`.
