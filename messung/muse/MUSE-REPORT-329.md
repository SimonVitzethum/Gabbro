# MUSE-REPORT-329: organisation owner — dependencies, allocation, parallel work

Lane 329 in clone a329, branch muse/329. Isolation verified before any edit
(pwd, toplevel, branch all match). Documentation task: no Lean/Rust edits,
no gratuitous build, no agent/model/network calls.

## What was delivered

- `dokumente/x86/WORK-ALLOCATION.md` (378 lines): stable foundations,
  outstanding dependency graph, which work can start now vs waits for the
  accepted 287 IR interface (no second IR), 16 disjoint authors (lanes
  335-350) with 16 paired exact-candidate reviewers (373-388), slot
  arithmetic (16+16+6 fixed = 38 <= 40, 2 spare), no-force/no-push lane
  policy with the full author -> peer -> merge rehearsal -> merge peer ->
  changed-source check -> doc reuse -> origin/key-grep -> publish sequence.
- Each of the 16 rows names: exact new ENGLISH module path (all new, none
  an existing central file), accepted imported dependency (symbols
  inspected in source: `Typen`, `Wort`, `Speicher`, `Ausfuehrung`, `Codec`,
  `Byteschritt`, `Bild`, `TSO`, `Zugriffe`, `Stapel`, `Regionen`,
  `Gleitprofil`, front-end `declOf`, `Budget`/`KostenG`, `Spec` atomics),
  target-statement direction without assuming the conclusion, non-degenerate
  memory-changing joint witness, planted refusal/negative case, safe
  compile-time policy, profile status (ESSENTIAL vs DEFERRED), closed proof
  gap, HARD rules and paired reviewer.
- Friend paths `Grammatik/X86/OptimizationRules.lean` and
  `OptimizationWitnesses.lean` OFF LIMITS; optimiser spec stays owner 331;
  friend stack/source-TSO/final-image pipelines not assigned. SCFG-consuming
  halves marked WAITING (B3 consumer, C5 proof). Costly profiles (AVX2 tier
  retained as goal with gates; AVX-512/AMX/APX/crypto/FMA-as-form/
  gather/NT-strings) deferred per lane-327 safety-first priority; no last-10%
  universal guarantee claimed. Full source-to-final-bytes validation OPEN.
- All file links in the plan verified present at write time (DIRECT-COMPILER,
  PLAN-UEBERSETZUNGSVALIDIERUNG, all x86 docs incl. the four reviews,
  lanes/287, lanes/331, X86/Typen.lean). Box-drawing arrows replaced with
  ASCII; `§` and em-dash usage follows existing merged-doc convention.

## Checks run

- `git status`: only the two owned files new/modified; nothing else touched.
- No `./lean-bau` / `./cargo-pruef` / `./emission-pruef` owed (docs-only;
  no `grammatik/`, `crates/`, `instrumente/` or ledger file changed).
- Last lean-bau result line: not run (documentation task, no source changed).

## Open / unknowns reported honestly

- 287 (IR) still working; SCFG-dependent halves cannot start until its
  interface is accepted. B1 (single-owner `accessList`) is the recommended
  first scheduling priority since B3/C5 and both consumers cite it.
- Slot arithmetic assumes draining lanes (287/303/328) free their slots;
  the coordinator must admit new authors only against actually free slots.
- Line numbers cited from inspection may drift; plan states as-read.
- Anything in the task believed wrong: nothing material. The "at most 16-18
  authors" bound with paired reviewers plus 6 fixed roles forces exactly
  16+16 (17+17 would total 40 with zero repair spare); the plan picks 16+16
  and books the 2 spare for repairs.
