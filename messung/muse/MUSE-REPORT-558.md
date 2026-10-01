# MUSE-REPORT-558: Connection plan and integration ownership

## What was done

Wrote `dokumente/x86/CONNECTION-PLAN.md` (only owned path besides this
report). It assigns concrete producer/consumer interfaces, ownership,
prerequisite hashes and measurable closure criteria for connection lanes
559-575, based on reading lanes 559-577, `DIRECT-COMPILER.md`,
`DIRECT-COMPILER-DESIGN.md` requirements, `dokumente/x86/QUELLBRUECKE.md`,
`dokumente/x86/TSO-GX-BRUECKE.md`, the audit docs, and the actual accepted
modules in this snapshot (`Codec`, `Byteschritt`, `Ausfuehrung`, `Bild`,
`Relokation`, `TSO`, `Zugriffe`, `NarrowOps`, `TableLayout`, `GateStub`,
`EntryState`, `ValidatorSkeleton`, source bridge `bruecke/Bruecke/Quelle.lean`).

Key contents: a closure rule (new fact from byte evidence + reuse + joint
nondegenerate witness + planted refusal + standard axioms + CUTS);
a derived-vs-trusted-vs-cuts separation; one row per lane 559-575 with
exact consumed/produced definition names and closure criteria; seven
concrete mismatches M1-M7 with assigned follow-up edits (notably M1:
`valX86` binds `(Profil, Bild)` while the schema needs `valX86 E bild`;
M3: `kein_lock_schritt`, no LOCK execution exists; M4: `IR.lean` absent
in this snapshot); a dependency order with 573/574/575 gated on accepted
dependencies; five small backfill tasks with no overlapping owners.

## New definitions/theorems

None. Docs-only lane; no Lean file added or changed.

## Last build result

No `./lean-bau` run: this lane touches zero Lean files (`git status`
shows only the two owned docs as new/modified), so the baseline build at
`8596f83e` is unaffected. No Lean claim is made that would require a build.

## What remains open

Everything the plan lists as OPEN: `valX86_sound`/`schluss_x86`,
per-access TSO->W/GX simulation, extension byte rows, LOCK/fence
execution, the single IR (IR287 still uncommitted elsewhere), OBS-5,
O-cas-cost, and the M1 validator adapter (proposed next wave). Reviewer
576 decides ACCEPT/REPAIR on the exact candidate.

## Task feedback

The task is sound as written. One note: the "preserved IR287 draft"
named in the task is not present in this clone (no `IR.lean` on disk);
the plan records this as M4 and instructs 572/573/574 to carry an
explicit representation interface and track only the accepted IR287
candidate, never a draft.
