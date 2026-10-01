# Muse Report 405 — Adversarial implementation audit: MEMORY-RANGES

Clone `/home/simon/Dokumente/gabbro-muse/a405`, branch `muse/405` verified
(`git branch --show-current`). Clean tree at start: no prior lane work existed
(`git status` empty, owned files absent). Read-only audit plus private probes;
no `grammatik/`, checker, emitter, or ledger file touched.

## What was done

- Read fully: `grammatik/Grammatik/X86/Speicher.lean` (761 lines),
  `Regionen.lean` (631 lines), `SpeicherKommutation.lean` (342 lines).
- Read as consumed definitions: `X86/Typen.lean` (Speicher/Zustand/Befehl),
  `X86/Ausfuehrung.lean` `schritt`/`effAddr`/`stapelOben` shape (ll. 1–120 plus
  targeted grep), `X86/Zugriffe.lean` (extraction + potential/realised
  discipline), `X86/Stapel.lean` (frames, slots, layout), `X86/OverlapRefusal.lean`
  (checker + consumer witnesses); plus `dokumente/x86/WORK-ALLOCATION.md` and
  `DIRECT-COMPILER.md` for consumer context.
- Wrote private probes `.tmp/probe405/P1.lean` (uncommitted, stays private):
  six theorems, all `decide`/`rfl` over actual definitions, `./lean-probe`
  reports **0 errors**. No Lean file in the tree was added or modified, so no
  `./lean-bau` was required (nothing to keep green; no red commit possible).
- Produced the owned deliverable `dokumente/x86/AUDIT-MEMORY-RANGES.md`.

## Deliverable

- `dokumente/x86/AUDIT-MEMORY-RANGES.md` (new file): verdicts with file/line
  evidence, six reproduced probes, prioritised repairs F1–F6, consumer-gap
  table, and an explicit non-findings section distinguishing sound modules and
  legitimately OPEN bridges from real gaps. No new definitions or theorems in
  the tree (audit lane; nothing to give `_zeuge` names to).

## Findings in brief

- No false theorem and no broken model semantic found. All three modules are
  correct within their stated claims (wraparound base, last-byte bounds,
  permission preservation, allocation freshness, commutation honesty,
  classifier conservativity — each verified against the code, probes P2/P3).
- F1 (cosmetic): `Regionen.lean` l. 50 doc "empty regions touch nothing" is
  false for interior empty regions (probe P1: `regionDisjunkt = false`).
- F2 (consumer pitfall): `sichereWort` checks index + permissions but not the
  frame bound; a wrapped frame stores at address zero (probes P4a/P4b/P5) with
  no `none`. Repair: bound-checked wrapper or named obligation (P2).
- F3 (missing bridge): nothing links `rsp`/`stapelOben` to `Rahmen` slots;
  push underflow is permission-gated only (P2, layout/ABI work).
- F4 (missing bridge): region admission ⇒ memory success exists only at the
  region base; no interior-offset version (P2, AccessList/IR consumer).
- F5 (missing lemma): `freiReserviere` has no freshness/disjointness theorem
  (P3, tiny).
- F6 (tracked incomplete): narrow + cross-width commutation absent, already in
  CUTS; recorded with the extra precision that cross-width frame facts are
  missing too (P3).

## What remains open / believed-wrong

- Nothing in the task looks wrong; the "no invented bug for an OPEN bridge"
  rule was load-bearing twice (wrapped `Speicher` accesses, TSO granularity)
  and both are recorded as non-findings rather than findings.
- The audit does not re-verify the TSO bridge, the 287 IR interface, or image
  loading beyond what the memory modules consume; F3/F4 assume those consumers
  arrive as planned in WORK-ALLOCATION.
- Suggested next lanes (not claimed): F2 wrapper + F4 interior bridge are the
  two highest-value small Lean tasks; each is shaped so a `_zeuge` over a
  reached memory-changing run is straightforward.

## Build / commit state

- `./lean-probe .tmp/probe405/P1.lean`: 0 errors (last line verified).
- `./lean-bau`: not run — no tree Lean file changed; nothing to regress.
- Committing only the two owned files; `.tmp/probe405/` stays uncommitted.
