# MUSE-REPORT-1348: Exact review of candidate 1347 (opcode ledger 0F C0-FF + 0F 38/0F 3A)

## VERDICT: ACCEPT

CANDIDATE: author lane 1347, pinned HEAD
`84a71dee554996fb92638585932dbad26480d13f`
(base `574ac3d75180a53907fa28302e3af11cf2d9f2db`).
Three files, nothing else: `MUSE-REPORT-1347.md`,
`grammatik/Grammatik.lean` (+1 import line),
`grammatik/Grammatik/X86/OpcodeLedger0FC0.lean` (new, 677 lines).

## What I did

Independent exact review from my clone
(`/home/simon/Dokumente/gabbro-muse/a1348`, branch `muse/1348`,
verified, tree clean). The pinned hash was never touched (no
`git show/log/diff` on it); the candidate was checked as delivered
under `.tmp/review/author-1347/` (SNAPSHOT.json, PATCH.diff, file
copies, OWNER-TASK.md, BUILD-EVIDENCE.json). I read the full 677-line
candidate, the owner task, the author report and the build evidence,
then verified every check below in my own clone.

## Evidence per check

- **No forbidden tokens.** Grep over the candidate file for
  `sorry|native_decide|unsafe|axiom |admit`: no matches.
  BUILD-EVIDENCE shows one intermediate probe with 2 `maxRecDepth`
  errors and `sorryAx`; the committed file adds
  `set_option maxRecDepth 100000` / `maxHeartbeats 4000000` and the
  final probe is clean. A raised recursion limit is not a banned
  construct.
- **Independent `./lean-probe` on the candidate file: 0 errors.**
  Axiom footprint exactly as the author claims: `propext` alone for
  all data/coverage/count theorems, `propext + Quot.sound` for every
  theorem that evaluates the decoder chain (same footprint class as
  the accepted `kapW_*`/`kap2_*` theorems; within the goal's
  `propext, Classical.choice, Quot.sound`). No `sorryAx` anywhere.
- **Existing files untouched except one import line.** PATCH.diff
  confirms: `grammatik/Grammatik.lean` gains only
  `+import Grammatik.X86.OpcodeLedger0FC0`. New file uses its own
  namespace `Gabbro.Grammatik.X86.Ledger0FC0`, imports only accepted
  family modules (`HwKapsteinDecoder`, `VectorCodec`,
  `ExtendedExecution`), depends on no other ledger lane.
- **Accepted evaluators lifted, never copied.** All four
  `modelliert` proofs reuse accepted theorems whose statements I
  verified verbatim in my clone: `ledger0FC1_kette` IS
  `kapKette_lock` (`HwKapsteinDecoder.lean:460`, exact RHS match);
  `ledger0FC1_regUd` IS `pin_lock_reg_ud_decodiert`
  (`LockedInstructionExecution.lean:769`, exact match);
  `ledger0FD4_vec` instantiates accepted `roundtrip_paddq`
  (`VectorCodec.lean:180`) with `[]` + `simpa`;
  `ledger0FEF_kette` is `kapDecode_breit _ _ _
  (decodeMulDivWidth_prefers_ext _ _ _ pin_ext_vec_pxor)` with
  signatures matching `HwKapsteinDecoder.lean:77`,
  `HwMulDivWidth.lean:54`, `ExtendedExecution.lean:230`.
- **Refusals are checked facts.** All 8 `verweigert` theorems are
  `kapDecode <closed bytes> = none` closed `by decide`, green in my
  independent probe (not comments).
- **Coverage/counts check out.** 4+8+2+0+125 = 139 rows;
  `ledger_nodup`, `ledger_c0ff_vollstaendig`,
  `ledger_escapes_vorhanden` and all five count theorems are
  `decide`-proved and green.
- **Every premise used; no Prop-typed premises.** All new theorems
  are closed (no premises at all); no vacuous quantification, no
  discarded hypotheses, no contract manipulation.
- **Silicon spot-checks pass** against the in-clone snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`:
  UD0 = `0F FF /r` (l.99231) with UD2 = `0F 0B`, so the author's
  correction stands; MOVBE = `0F 38 F0/F1` (ll.66460-66470), so bare
  `0F F0` is correctly a refused blank; RDRAND = `NFx 0F C7 /6`
  (l.91087), RDSEED = `NFx 0F C7 /7` (l.91170) — the candidate's
  ModRM bytes check out (`F8` = mod 11/reg 6, `FC` = mod 11/reg 7);
  RDPID = `F3 0F C7 /7` (l.90863), SENDUIPI = `F3 0F C7 /6`
  (l.94060). No AMD manual in the clone; no AMD provenance claimed;
  vendor differences stay FREE (rule 17).
- **CUTS honest, no oversized claim.** The file ends with a CUTS
  block plus `#print axioms` for all 17 theorems. Map
  transcription is a NAMED assumption, VEX/EVEX and
  supervisor/system forms are named-not-modeled, RDRAND/RDSEED are
  `zurueckgestellt` with the Spec NOT CLAIMED reason, the 125
  `fehlt` rows are findings for future family lanes. No
  hardware-correspondence and no W/GX bridge claim.
- **No `_zeuge` owed.** No new theorem has a premise quantifying
  over program syntax and the TASK paragraph names no ZEUGE target.
  The ledger rows are data; every decoder claim links an accepted
  pin or round trip.

## On the task-text contradiction (author's finding: confirmed)

The OWNER-TASK's TASK paragraph (statics-only ledger, ONE new file,
self-contained schema, decide/refuse/count checks) and its
CONTEXT/MECHANISM paragraphs (`HwAdapter` embedding, two-core
memory-changing witness) describe two different lane kinds. The
owned filename, region and one-file instruction all agree with the
ledger task, so implementing the ledger and ignoring the adapter
mechanism is the correct call, and the author flagged it plainly in
the report instead of faking a connection. The review criterion
"non-degenerate witness where relevant" is not relevant here: there
is no syntax premise to witness and no connection to demonstrate.
This is not a defect of the candidate.

## Builds

- `./lean-probe` (candidate file, in place): 0 errors; full axiom
  list in the transcript above.
- `./lean-bau` (my clean tree): exit 0,
  `Build completed successfully (697 jobs).`

## Honest partial / limitation

Full-tree integration of the candidate (file + import line through
`./lean-bau`) was NOT re-run in my clone: the permission layer
refused my `cp` of the candidate file into `grammatik/` (one
rejected call; retried via in-place probe instead), and I own only
this report, so no staged copy remains in my tree. Coverage for that
leg: the author's committed BUILD-EVIDENCE (final probe 0 errors,
`./lean-bau` green at 694 jobs on its base) plus my independent
0-error probe with the exact claimed axiom footprint. Residual risk
is minimal: every module the candidate imports exists in my clone
(verified by grep), and the only tree change is one appended import
line. Note my clone is newer than the author's base
(`Grammatik.lean` here ends with `HwKapsteinZwei`, 4 imports ahead),
so the merge appends the import after `HwKapsteinZwei` — trivially
non-conflicting.

## Open / not claimed (carried from the candidate)

125 `fehlt` rows (SSE2 integer ALU incl. PSUBB/PADDB families,
BSWAP, CMPcc, PMOVMSKB, SHUF, POR/PAND, lock-less/8-bit XADD,
CMPXCHG8B/16B, converts, non-temporal stores, full 0F 38/0F 3A
space) stay findings for future family lanes. `ungueltig64` is
empty by measurement, captured instead by the 8 `verweigert` rows.
Map transcription remains a named assumption no guardian
machine-reads.

## Names added by the candidate (for the record)

`LStatus`, `LEintrag`, `ledgerTeilC/D/E/F`, `ledger0FC0`,
`ledgerSchluessel`, `istModelliert`, `istZurueckgestellt`,
`istVerweigert`, `istUngueltig64`, `istFehlt`, `ledger_nodup`,
`ledger_c0ff_vollstaendig`, `ledger_escapes_vorhanden`,
`ledger_anz_modelliert/verweigert/zurueckgestellt/ungueltig64/fehlt`,
`ledger0FC1_kette/regUd`, `ledger0FD4_vec`, `ledger0FEF_kette`,
`ledger_weist_c7r0/c7r2/d0/d6/e6/f0/ff/c1ohneRex_zurueck`.
