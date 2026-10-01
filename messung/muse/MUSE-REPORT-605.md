# Muse Report 605: concurrency bridge integration and producer adequacy audit

- Branch: `muse/605`, clone `/home/simon/Dokumente/gabbro-muse/a605` (verified: `git rev-parse --abbrev-ref HEAD` = `muse/605`).
- Owned paths only: `dokumente/x86/CONCURRENCY-CLOSURE-PLAN.md` (new), `MUSE-REPORT-605.md` (this file). No Lean file touched, no umbrella import added, no other path written.

## What was done

Wrote the report-only closure plan `dokumente/x86/CONCURRENCY-CLOSURE-PLAN.md`:
audited accepted `TSOHistory` (567), canonical `TSO`, `AccessExecution` (568),
`LockedOps` + `WordAtomicity`, `AtomicPayload`, source W/GX/`Sicht` reuse points
and `TSO-GX-BRUECKE.md`; distinguished snapshot `fresh2` facts from a real
preserved source W run (§2, the load-bearing gate rule); specified the exact
relation / access grouping / rely / forwarding / views / RMW-cost / carrier
representation interfaces 573/574 need (§3); prioritised gaps G1–G7 (§4);
proposed bounded disjoint tasks T1–T5 on the existing architecture with exact
consumer names and proof/witness/refusal criteria (§5); restated non-goals (§6).

## Exact names

- New definitions/theorems: none (docs-only lane; nothing to witness under rule 13).
- New files: `dokumente/x86/CONCURRENCY-CLOSURE-PLAN.md`, `MUSE-REPORT-605.md`.
- Key reused names cited (all verified by read/grep in this clone):
  `histVon`, `sichtVon`, `spülen_baut_frische_nachricht`, `weiterleitung_ist_jüngste`,
  `fremd_weiterleitung_unsichtbar`, `hist_zeuge_gelenk`, `paket_reisst`,
  `realisiert_fuss_abdeckung`, `byte_realisiert_fuss`, `realisiert_fuss_abdeckung_zeuge`,
  `lockSchritt`, `casSchritt`, `lock_xadd_atomar`, `cas_schleife_unbeschraenkt`,
  `rmw_nur_mit_lock`, `WortGuard`, `wort_fuss_reisst`, `WortNachW`/`LockNachW` (empty),
  `atomarFussB`, `GeteiltV`, `GeteiltA`, `audit_pflicht_deckt_aufgenommen`,
  `SchrittW` (`MaschineW.lean:150`), `Lesbar`/`Frisch` (`Sicht.lean:133/139`),
  `schwach_ist_gX` (`AtomarW.lean:279`).

## Build / check evidence

- `git status --porcelain` shows only the two owned files (plus pre-existing
  `lanes/605.md` untracked? No: `lanes/605.md` is committed; only the two owned
  files are new/modified). No Lean change, so no `./lean-bau` claim is made
  (per lane instruction: docs work adds no Lean imports and claims no new Lean
  build). Last full-project state untouched by this lane.
- No `./lean-probe`, `./cargo-pruef` or `./emission-pruef` run: nothing they
  measure was changed. Stating this plainly rather than borrowing a stale green.

## What remains open

- Everything in plan §§4–5: G1 (TSOTrace596 growing history), G2 (SourceMemory570
  representation), G3/G4 (BridgeWrite573/BridgeRead574 per-access construction),
  G5 (per-rule access completeness), G6 (group assembly + run induction),
  G7 (OBS-5, O-ord, O-cas-cost, O-time, O-mmio, O-enable).
- 570's interface is pending; §3.7/T2–T4 must be re-audited if it lands with a
  different shape (recorded in the plan's CUTS).

## What I believe is wrong or risky in the task setup

- The task mentions a "supplied snapshot" but no snapshot file exists in this
  clone (no `.claude/muse-arbeit/x86/`, no `CONCURRENCY*` file before this lane).
  I audited the live accepted modules instead and marked 570-derived claims as
  pending-interface; a reviewer should confirm this matches the intended snapshot.
- Nothing else: the ownership, no-filler, and no-new-semantics constraints are
  satisfiable as a report-only lane and were kept.

Co-Authored-By: muse-agent-605 <muse-agent-605@noreply.invalid>
