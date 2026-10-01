# MUSE-REPORT-332: independent organising plan review of lane 329

Lane 332 in clone a332, branch muse/332. Isolation verified (pwd, toplevel,
branch all match). Owns only this file. No source changes, no builds run
(docs-only review), no agent/model/network calls.

## Candidate

CANDIDATE:329 186bb06be4e73a887f8c9681249a46fd2d05a67a
Base: 6a0b028af57bd2e192030c647ba96de9ec837995 (per .tmp/review/SNAPSHOT.json).
Files: `MUSE-REPORT-329.md` + `dokumente/x86/WORK-ALLOCATION.md` (378 lines).
Snapshot reports clean; patch inspected confirms exactly those two new files.

## What was checked

- All 18 file links named in the plan verified present in this clone:
  DIRECT-COMPILER.md, PLAN-UEBERSETZUNGSVALIDIERUNG.md, all 12
  dokumente/x86/*.md files, lanes/287.md, lanes/331.md,
  grammatik/Grammatik/X86/Typen.lean. All OK.
- Dependency/ownership: 16 proposed modules are all new (no collision with the
  20 existing X86 files); `Typen.lean` appears only as an imported dependency,
  not an assigned output. Friend paths `OptimizationRules.lean` /
  `OptimizationWitnesses.lean` appear only in the OFF-LIMITS section, never as
  an author row; optimiser spec stays with owner 331. No second IR: SCFG work
  is marked WAITING on the accepted 287 interface, and 287 is correctly cited
  as task/working, never as an existing accepted file.
- Symbols spot-checked in source and all real: `Breite`/`Speicher`/`Zustand`/
  `Befehl`/`Decodiert`, `ofAdd`/`ofSub`/`cfAdd`/`parityEven`/`sext`,
  `addrOff`/`lesbar8`/`read64`/`write64`/`Fuss`, `regCode`/`codeReg`/
  `leBytes32/64`/`rexByte`/`modrmReg`, `geholt`/`fetchDekodiert`/`byteschritt`,
  `Abschnitt`/`Relok`/`Modus`/`kanonischBereich`/`geladen`,
  `TSOZustand`/`issueByte`/`loadByte`/`flushKern`/`zaunBereit`/
  `fifo_reihenfolge`, `Rahmen`/`ausgerichtet16`/`sichereWort`/`Belegung`,
  `Region`/`Vorrat`/`reserviere`/`initialisiere`, `mxcsrGueltig`/`FPKontext`/
  `muster64`/`bites64`, `Zugriff`/`zugriff`, `declOf`, `Op.cost`/`totalCost`,
  `AkzeptiertSpecX`/`FussSX`/`GeteiltV`/`GeteiltA`. `accessList` is genuinely
  ownerless (REVIEW-TSO recommendation); B1 assigns the single owner.
- Slot arithmetic: 16 authors (335-350) + 16 reviewers (373-388) + 6 fixed
  (329, 332, 330, 333, 331, 334) = 38 <= 40, 2 spare for repairs. Matches
  AGENTS.md ledger (workers from 335, reviewers from 373; 269-334 reserved).
  16 authors is within both the owner-task bound (16-18) and this lane's
  "at most 18" bound. Draining-slot assumption (287/303/328 free as they
  complete; admit only against actually free slots) is stated explicitly.
- No silent second IR, no program-specific vacuity (every row: generic target
  direction, joint non-degenerate memory-changing witness, planted refusal),
  no cost/contract weakening (A2 traps to the named `hardware` stop class;
  A5 claims no W/GX refinement; C3 schema states `budget_simulation` OPEN;
  CAS-loop unbounded shape claims no constant bound; costly profiles
  deferred per lane-327 safety-first). Full source-to-final-bytes validation
  stays OPEN throughout; IR-dependent halves marked WAITING.
- Manual bridge, not assumed: C1 recomputes layout from source (`declOf`)
  and re-decides Rust hints; C5 re-reads backend bytes; status of helpers
  (pilot=14, LOCK/fence missing, atomics duty vacuous, SCFG waits on 287) is
  truthful. Merge/publish sequence (author -> peer -> merge rehearsal ->
  merge peer -> changed-source check -> doc reuse -> origin/key-grep ->
  publish; no force/push/remote lane branches) is complete.
- English filenames; final patch has zero box-drawing lines (verified: 0).
  Remaining non-ASCII is 16 em-dashes + 11 section signs, matching existing
  merged-doc convention. Minor process note: the author's BUILD-EVIDENCE
  link-check ran while box-drawing was still present, so the evidence output
  shows it but the final committed bytes do not; content, not a defect.
  One typo: "grammmatik/OPTIMIZER.md" in the 331-row context (double m);
  the correct `grammatik/OPTIMIZER.md` path is used in the owner-task
  reference and §0. Not verdict-changing.
- Next steps feasible: B1 first priority is justified (B3/C5 and both
  consumers cite `accessList`); ISA batch (A1-A6, no SCFG needed) can start
  now; SCFG consumers correctly gated. Interface dependencies are real
  files, not invented names.

## Checks run

- `git status` / branch / log inspection only. No `./lean-bau`,
  `./cargo-pruef`, `./emission-pruef` owed (no `grammatik/`, `crates/`,
  `instrumente/`, ledger file touched by candidate or by this review).
- Last lean-bau result line: not run (documentation review, no source changed).

## Verdict

VERDICT:ACCEPT for CANDIDATE 186bb06be4e73a887f8c9681249a46fd2d05a67a.

Bounded plan only: no Lean module, no validator, no refinement, no cost
transfer and no image acceptance is proved by the candidate; integration
still needs the standard serial publication gates (full changed-source Lean
build, Rust suite, emission check, `gabbro_ziel` axiom probe, secret-pattern
grep, origin-ancestry check).

## Open

- 287 IR interface still working; SCFG-consuming halves stay WAITING.
- Coordinator must enforce admission against actually free slots (cap 40
  today, 20 afterwards).
- Line numbers cited as-read may drift; plan states this.
- Nothing in the reviewed task believed materially wrong.
