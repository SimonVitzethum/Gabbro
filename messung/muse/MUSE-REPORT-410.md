# Muse report 410 — Adversarial implementation audit: CALL-ABI

- Clone: `/home/simon/Dokumente/gabbro-muse/a410`, branch `muse/410` (verified at start; no mismatch).
- Owned files only: `dokumente/x86/AUDIT-CALL-ABI.md` (new audit), `MUSE-REPORT-410.md` (this report).
- No Lean files added or modified; no Rust/emitter/checker/Spec/goal files touched; friend paths untouched.

## What was done

Read the accepted implementations and their CUTS at exact lines: `X86/Stapel.lean`
(frame/ABI obligations), `X86/AufrufOpt.lean` (ghost call-log reconstruction),
`X86/Ausfuehrung.lean` (`call32`/`ret`/`push`/`pop` steps), `X86/Zugriffe.lean`
(footprint extraction incl. call rows), `X86/ControlFlow.lean` (`direktZiel` +
admission), `X86/SpillPrivate.lean` (TSO-side spill half), plus read-only
consumer ground (`Typen`, `Byteschritt`, `Bild`, `Syscall`, `FremdRuf`,
`Folge`, `IMAGE-ABI` secs. 5–8/11, `DIRECT-COMPILER-DESIGN`, `WORK-ALLOCATION`,
`EMITTER-INVENTAR` gate rows). Produced `dokumente/x86/AUDIT-CALL-ABI.md`:
per-module claim tables, seven audited dimensions (stack/private spills,
register aliases, faults/costs, call logs/order, indirect entry provenance,
return + generic gates without OS assumptions), file/theorem/line evidence for
every finding, in-tree positive/negative probes, and a prioritized P0/P1/P2
repair/bridge list naming the owning follow-up work (GateStub C2, EntryState
C4, TableLayout C1, ValidatorSkeleton C5, narrow/cost/indirect follow-ups).

## Exact names of new definitions/theorems

None. This lane is an audit lane: no Lean definitions or theorems were added,
and no existing theorem was modified, weakened, or renamed.

## Last `./lean-bau` result line

Not run — no Lean file was created or changed, so no proof gate is affected.
(`./lean-bau` / `./lean-probe` apply to Lean changes; this commit is
documentation-only: one new audit document plus this report.)

## What remains open

- All P0 bridges in the audit sec. 8: `rsp`↔`Rahmen` linkage with call-boundary
  alignment enforcement; indirect-target certificates + `entry fn` provenance;
  `ret`/terminal provenance with live-caller/call-save tracking; indirect-call
  ghost coverage (or explicit lowering refusal) + `nachOk` derivation; x86 stub
  correspondence per gate form + per-site callee obligation (c) including
  `child`/trampoline/`-> never` paths.
- P1/P2 follow-ups: `SysReg`↔`Register` mapping and `argReg`-vs-clobber
  disjointness; fault→`FortschrittG` stop mapping; call/stack/gate cost rules;
  red-zone/guard policy; narrow width-alias rules at boundaries.
- Sibling audit lanes (404–409, 411–415) cover the non-call dimensions; exact
  independent review of this audit (lane 490) happens separately.

## Anything in the task believed wrong

Nothing wrong. Two clarifications recorded in the audit: (1) "reproduced
probes" are the merged in-tree `decide` probes cited with file/line evidence,
not re-executed builds, since an audit lane adds no Lean code; (2) pending
lanes 345–349 are correctly treated as OPEN consumers, not as defects in the
accepted helpers — the audit distinguishes false semantics (none found) from
legitimately incomplete deliverables throughout.
