# Muse report 495: independent exact-candidate review of 415 (re-review)

Clone: `/home/simon/Dokumente/gabbro-muse/a495`, branch `muse/495` (verified).
This is a fresh substantive re-review of the NEW pinned snapshot (repair
revision). Previous round (REPAIR on `78d57179`, truncated deliverable) is
kept as history below; nothing in it is re-litigated, every previous
finding was re-inspected against the new files.
Own file only: `MUSE-REPORT-495.md`. Nothing else touched; tree clean
before and after.

## New snapshot reviewed

`.tmp/review/SNAPSHOT.json` pins author 415, head
`5ff40b9a05a75ac9af2eb7eb8df039d1cfa54f0d`, base `0b3132b7`, files
`MUSE-REPORT-415.md` + `dokumente/x86/AUDIT-END-TO-END-TRUST.md`, clean.
BUILD-EVIDENCE.json (16 entries) shows the full chain: first commit
`78d57179`, repair diff (+338/-9 over exactly the two owned files),
repair commit `5ff40b9a` with CLEAN status — the pinned HEAD matches the
evidence trail. PATCH.diff touches only the two owned files. Scope clean.

## What was done in the re-review

- Confirmed the repair: the audit is now 557 lines / ~32.5 KB, ends with
  Appendix C, and contains no tool-truncation artifact (the only two
  "truncated" matches are the technical term "truncated-prefix refusal"
  and the review-response note itself, both legitimate).
- Confirmed all previously dangling references now resolve inside the
  file: §4 (line 289), §7 (431), §8 ledger (459), finding F3 (300),
  P0-P3 task list (§9, 481-515), appendices A-C (517-556).
- Re-verified §§0-3 (claimed unchanged): spot re-reads match the first
  review's verified citations; the three focus modules are still
  byte-identical to candidate base `0b3132b7` in this clone, so all
  line-number citations stand as previously verified.
- Verified the NEW sections' checkable claims by direct read of the
  accepted sources:
  - §3 completion: `InvScope` constructors `ruhe|sich|wechsel` (250-253),
    `slot_read_stabil` with explicit `hidx`/`hinhalt` premises (277-285),
    witness declaration `wD` (303) with writing contract, `wit_schreibt`
    (402), `wit_elim` (410), `wit_step` (417), all `_zeuge` companions
    (428-515), 8 `#print axioms` (counted 8), CUTS at 517.
  - §4 neighbours: `Zugriffe.zugriff` (line 42; "all 14 pilot forms"
    confirmed in the module's own header), TSO byte-buffer vocabulary
    (`TSOZustand`, `issueByte`/`loadByte`/`flushKern`/`zaunBereit`,
    `TSOSchritt`, `fifo_reihenfolge`, `sb_*` witness,
    `zaun_kein_fremd_drain`), `Relokation` open-flag
    (`relAnnahmeEndgueltig := false` + `relAnnahme_offen`),
    `AccessList.accessList` with `LiestG`/`SchreibG` + `luecke_faellt`
    (160), `SpillPrivate.spillPrivatOk` (36), `AufrufOpt.geistPaar` (32)
    + `geistPaar_laenge` + `InlinePflicht`/`vorOk` (127/134) +
    `FolgeLog`, `StaerkeReduktion.sdiv_kein_shift` (121) +
    `shrW_breite` (152), `ControlFlow.direktZielOk` (174),
    `LockedOps` CAS-loop shape cost stated unbounded (99-104),
    `CostSummary.kostenSummeOk` (71) + `expandBound`.
  - §5 weak point is real and honestly stated:
    `slot_read_stabil_zeuge` proves stability by `rfl rfl` on identical
    worlds (read verbatim) — inhabited jointly but not exercised; the
    audit flags exactly this as bounded weakness with discharge assigned
    to the certificate layer (P0.3). Self-critical, correct.
  - §7 naming hygiene matches the tree (`TableLayout.layoutOk` is the
    table predicate; QUELLBRUECKE sketches are commented shapes).
- No new Lean/Rust/emitter content anywhere in the candidate; docs-only
  stands, so no build is owed and none is claimed. No vacuity beyond what
  is flagged, no unused-premise or `forall rho/v` issue in cited
  material, no safety weakening, no trusted-Rust-verdict claim, no
  per-program rules, no forged evidence.

## Non-blocking nits (recorded, not verdict-relevant)

1. Appendix C claims "the DIRECT-COMPILER citation no longer uses
   numbered §§", but §0 line 29 still cites "`DIRECT-COMPILER.md`
   §§27-33". The appendix overstates that half of the repair; the
   citation itself is the same harmless imprecision noted in round one
   (that document's headers are unnumbered).
2. MUSE-REPORT-415.md points to "the prioritized work (§7 of the audit)"
   — the P0-P3 list is §9 (§7 is runtime/link/loader).
3. Appendix B says "eleven neighbouring" modules; §4 lists twelve.
   None of these changes what the candidate delivers.

## Previous round (history)

Round one reviewed `78d57179` and returned REPAIR: the committed audit
ended mid-sentence in §3 with a literal `...[truncated 9113 chars]` as
its final bytes (verified with `od -c`), so promised §§4-9/appendices
were absent and "see §4" / §7 / §8 references dangled while the report
described them. That exact defect is repaired in the new revision:
every previously dangling reference resolves, and the report now
matches the file (modulo nits 1-3 above).

## Exact names of new definitions/theorems

None (review lane; none tasked). No probe files created.

## Last `./lean-bau` result line

No `./lean-bau` run: review-only lane, candidate is docs-only, and all
cited theorems were verified by direct read of `by decide`/`by simp`/
`by rfl`-closed proofs in base-identical files. No queued build was
issued (shared-slot contention; nothing to gain for a docs verdict).

## What remains open

- Root integration of the accepted audit happens separately.
- The substantive end-to-end chain stays OPEN per the audit's own
  section 0 — expected, not a defect.
- The three nits above are left for the author's next touch of the file.

## Anything in the task believed wrong

Nothing wrong.

CANDIDATE: 415 5ff40b9a05a75ac9af2eb7eb8df039d1cfa54f0d
VERDICT: ACCEPT

Co-Authored-By: muse-agent-495 <muse-agent-495@noreply.invalid>
