# Muse report 488 — independent exact-candidate review of 408

- Clone verified: `/home/simon/Dokumente/gabbro-muse/a488`, branch `muse/488`. Match, proceeded.
- Candidate pinned: `50e799b64e7210e62eaa9e261f1a4ebf21158054` (base `0b3132b7`), files `MUSE-REPORT-408.md`, `dokumente/x86/AUDIT-WEAK-MEMORY.md` per `.tmp/review/SNAPSHOT.json` (`clean: true`).
- Method: read `.tmp/review/author-408/OWNER-TASK.md`, `MUSE-REPORT-408.md`, `BUILD-EVIDENCE.json`, `PATCH.diff`, and `dokumente/x86/AUDIT-WEAK-MEMORY.md` in full; spot-checked every load-bearing file:line claim against this clone's `grammatik/Grammatik/X86/` tree (`TSO.lean` 622 lines, `Zugriffe.lean` 696, `AccessList.lean` 280, `LockedOps.lean` 521, `OverlapRefusal.lean` 415, `SpillPrivate.lean` 399 — counts match the report). No other clone read. No candidate files staged; tree stayed clean. No build needed (docs-only candidate); no `lean-bau` run owed.

## What was checked

- Scope/ownership: candidate touches ONLY the two owned files. No Lean, model, goal, checker, emitter, ledger, or number-range change. Matches owner task (`OWN ONLY dokumente/x86/AUDIT-WEAK-MEMORY.md, MUSE-REPORT-408.md`). Pass.
- Must-nots: no DRF-SC claim and no word-atomicity-from-bytes claim — verified by inspection. `tso_store_buffering` (TSO.lean:414), `sb_beide_laden_null` (:395), `sb_flush_aendert_speicher` (:406), `einzelbyte_atomar` (:445, width-1 only), `paket_reisst` (:459, two-byte tear), `LockSchritt` empty (:477) with `kein_lock_schritt` (:480) all present at cited lines. `Befehl` (Typen.lean:53-68) confirmed 14 constructors, 64-bit only. Pass.
- Spot-checked findings against source (this clone, same line numbers as cited):
  - F1 (no combined TSO+LOCK relation): `TSOSchritt` (TSO.lean:92-96) is issue/flush only; `lockSchritt` (LockedOps.lean:57-82) and `casSchritt` (:83-99) are standalone `Option` functions. Confirmed real gap, correctly assigned to bridge owner, not to LockedOps author. Pass.
  - F2 (barrier-as-precondition): `lockSchritt` (LockedOps.lean:60-62,75-78) and `casSchritt` (:85) return `none` unless `(s.puffer c).isEmpty`. Confirmed by reading; the private probe (BUILD-EVIDENCE entry 5: `./lean-probe .tmp/WEAK-PROBE.lean`, 0 errors) is plausible but its source was not supplied, so I reproduce the claim from source text, not from the probe. Pass on substance, minor evidence note below.
  - F3 (no unified footprint for locked forms): `zugriff (d : Decodiert)` (Zugriffe.lean:42) vs `SperrBefehl` (LockedOps.lean:23) + `LockEreignis` (:31). Confirmed separate types. Pass.
  - F4 (three alignment vocabularies): `Ausgerichtet` (TSO.lean:428, Prop), `ausgerichtet8` (LockedOps.lean:44, Bool), `addrAusgerichtet` (OverlapRefusal.lean:27, param Bool). Confirmed. Pass.
  - F5 (GetrenntK clash): source `GetrenntK P K c` (ZielOrtMehrfaden.lean:161) vs `X86.GetrenntK r idx fremd` (SpillPrivate.lean:30). Same short name, different types/meanings. Confirmed real misrouting hazard. Pass.
  - F6 (`accessList` never `luecke`): `accessList_kein_luecke` (AccessList.lean:145) present. Pass.
  - F7 (OverlapRefusal target-only): imports are only `Speicher, Zugriffe, Regionen, Bild` (OverlapRefusal.lean:17-20); no source carrier import. Pass.
  - F8 (narrow unlowerable): `Befehl` 64-bit only confirmed; `NarrowOps.lean`/`TableLayout.lean` absent at audit base (present in this newer checkout, which postdates the base — not a contradiction). Pass.
- No invented bug from an OPEN bridge: audit marks F1-F9 as consumer gaps, declines to pre-judge unmerged lanes 344/350, scopes around scheduled lane 421. Compliant with owner task. Pass.
- No vacuity/forgery/safety issue: no theorems added, so no witness or `#print axioms` owed (report correctly states none); no benchmark or axiom evidence claimed; no IR duplication, no guarantee weakened. Pass.

## Blocking defect (one)

- Truncated deliverable with over-claiming report. The candidate's `dokumente/x86/AUDIT-WEAK-MEMORY.md` ends mid-sentence inside F9 (`**Task:** keep every image exercising gates/s`) followed by the literal line `...[truncated 2085 chars]` with no trailing newline — visible both in the supplied file (offset ~14.6 KiB, last bytes) and in `PATCH.diff` (tail `+...[truncated 2085 chars]\n\ No newline at end of file`). This is the signature of a cut-off single write committed without noticing (HARD RULE 10).
- Consequence: `MUSE-REPORT-408.md` claims "11 prioritized findings F1–F11 ... explicit non-findings, and CUTS", but the file delivers F1–F8 plus a truncated F9. F10, F11, the non-findings section, and the CUTS section are missing. The bounded claim "F1–F11 audit with CUTS" is therefore not precisely delivered. The owner task explicitly demands "proof/CUTS versus claims" — that required section is absent.
- Repair direction: keep all verified sections byte-identical; re-emit the file in small incremental writes; complete the F9 task sentence; restore F10, F11, explicit non-findings, and CUTS; delete the literal truncation-marker line; end the file with a newline; correct `MUSE-REPORT-408.md` to describe exactly what is delivered. Changed candidate needs a fresh substantive review.

## Minor note (not verdict-changing)

- The F2 probe (`.tmp/WEAK-PROBE.lean`, private, 0 errors per BUILD-EVIDENCE) was not supplied, so F2 is verified here by source reading only. On repair, either supply the probe text in the audit or quote the three evaluated cases inline so a reviewer can reproduce without trust.

## New definitions/theorems

None. Docs-only review; nothing to witness and no `#print axioms` owed.

## Last build result

No `./lean-bau` run: neither the candidate nor this review touches Lean. No `./cargo-pruef` / `./emission-pruef` run: docs-only. Source spot-checks were `grep`/`sed` reads, not builds.

## What remains open

- Repair of candidate 408 as above, then a fresh exact-candidate review of the new HEAD.
- The audit's own bridge findings F1–F9 (verified real) remain work for their assigned owners; this review takes no position beyond confirming they are consumer gaps, not proved-claim bugs.

## Task correctness

The lane task is sound. One process suggestion for the coordinator: docs-only lanes writing files over ~8 KiB should be reminded to write in small pieces and to grep the committed diff for `truncated` before committing.

CANDIDATE: 408 50e799b64e7210e62eaa9e261f1a4ebf21158054
VERDICT: REPAIR
