# MUSE-REPORT-414

*Lane 414 — adversarial implementation audit: SOURCE-FOOTPRINT.
Clone `/home/simon/Dokumente/gabbro-muse/a414`, branch `muse/414` —
verified (`git rev-parse --abbrev-ref HEAD` = `muse/414`).*

## What was done

Read the accepted target modules (`X86/Zugriffe.lean`,
`X86/AccessList.lean`, `X86/TSO.lean`, `X86/OverlapRefusal.lean`,
`X86/LockedOps.lean`, `X86/SpillPrivate.lean` in part) and the actual
source definitions (`Semantik.lean` `Ereignis`/`World.lese`/`schreib*`/
`execStmt`/`execBlock`/`Orakel`/`axiomAntwort`, `RennfreiG.lean`
`zugriffVon`/`zugriffe`, `RennfreiVoll.lean` `ereignisse`/`ZugriffG`/
`SchreibG`/`LiestG`, `RufMaschineG.lean` `RufSchrittG` — 75
constructors counted at HEAD, `ZielOrt.lean` footprint extraction,
`ZielOrtGeraetSem.lean` `.regs` extraction, `SperreFuss.lean` `FussS`,
`AtomarReplay.lean` `FussSX`, `Satz.lean` `axiomSpur`/`GutO`,
`Syntax.lean` `D.Ax` fields, `RMW.lean` `exchange_liest_schreibt`),
plus `TSO-GX-BRUECKE.md` D-access/L-access requirements and
`WORK-ALLOCATION.md` owner rows. Audited every `Stmt`/`Block`
footprint arm against its executing arm. Wrote the owned audit
`dokumente/x86/AUDIT-SOURCE-FOOTPRINT.md` (only other file touched).

## Findings (see audit §7 for detail)

- P0 F4: `accessList` never returns `luecke`
  (`AccessList.lean:64-65`, proved `:145`); the B1 refusal policy is
  vacuous on the producer side. Needs a per-rule classifier or a
  downgraded claim.
- P1 F1: `Stmt.regs` catch-all `_ => []` misses the `transition`
  mirror read (`ZielOrtGeraetSem.lean` vs `Semantik.lean:772-775`);
  mirror device carriers absent from `fussOrteG`/`FussS`/`FussSX`.
- P1 F2: `callInd` footprint has no callee-contract disjunct
  (`ZielOrt.lean:151`); caller-side stability unstateable.
- P1 F3: gate/oracle reads beyond `args.orte` are trace-invisible
  (no read field on `D.Ax`, `GutO` constrains writes+frame only);
  gate writes confirmed covered via `axiomSpur`.
- P2 F5: no `LockEreignis`↔`Zugriff` overlap adapter; checker
  unowned between two accepted modules.
- P2: per-rule access table for 74/75 `RufSchrittG` rules still OPEN
  (only `exchange` has a lemma); already OPEN in CUTS, kept open.
- Explicitly checked-correct within claim: write-absence from
  `fussOrte` (dynamic trace + `TraegerGleich` disjunct cover it),
  `zugriff` potential/realised split, `zugriffOk` wrap handling,
  per-byte-only atomicity claims, local-only fence.

## Deliverables

- New definitions/theorems: none (doc lane; no Lean added).
- `dokumente/x86/AUDIT-SOURCE-FOOTPRINT.md` (new, owned), this report.
- Last `./lean-bau` result line: not run — `grammatik/` untouched
  (`git status` shows only the two owned documents), so no build
  signal is claimed or needed. No red commit possible from docs.
- `#print axioms`: none (no theorems).
- `ZEUGE:` witnesses: none required (no theorems added).

## Open / possibly wrong in the task

- The task asked for "reproduced positive/negative Lean probes where
  useful": as a doc-only lane (OWN ONLY two `.md` files, no Lean file
  named in the task) I added no probes and instead cited the existing
  `decide` witnesses and planted refusals by file/line (audit §8).
  If probes were meant to be committed, the task needs a named Lean
  file and owner row.
- F3 may close as caller duty rather than model gap if gate-contract
  orte discipline is established elsewhere — I found no read field on
  `D.Ax` and no such link at the three extraction sites; the bridge
  owner should confirm before scheduling a model change.
- Rule count "≈70" in older docs is 75 at HEAD; follow-ups citing the
  count should use 75.
