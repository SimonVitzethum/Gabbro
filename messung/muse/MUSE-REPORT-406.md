# MUSE-REPORT-406: Adversarial implementation audit, DECODE-BOUNDARY

- Clone: `/home/simon/Dokumente/gabbro-muse/a406`, branch `muse/406` — verified.
- Owned files only: `dokumente/x86/AUDIT-DECODE-BOUNDARY.md` (new audit),
  `MUSE-REPORT-406.md` (this report). No `grammatik/`, Rust, or other files touched.
- `git status` before commit shows exactly these two new files (plus the report).

## What was done

Read the accepted `X86/Codec.lean` (806 lines, lane 279) and
`X86/Byteschritt.lean` (510 lines, lane 319) in full, plus
`X86/Typen.lean`, `X86/Ausfuehrung.lean` (`schritt`, `laengeOk`),
`BYTE-PILOT.md`, `WORK-ALLOCATION.md`, and the decode-related claims in
`DIRECT-COMPILER.md` / `DIRECT-COMPILER-DESIGN.md`. Checked decoder
consumers by grep (only `Byteschritt` imports `Codec`) and the Rust tree
(Rust codec lane 280 stays stopped; no Rust decoder to audit).

Verified by reading (not assumed): per-path literal decode lengths equal
consumed byte counts on all 10 success shapes; first-byte dispatch
disjointness; `movImm64` vs ModRM opcode disjointness; mod-3 vs mod-2
split with opcode-139 fall-through to `none`; `rest`-is-suffix structure
on every path; fail-closed extension (new `Befehl` constructor breaks
`encode`/`roundtrip` exhaustiveness at compile time).

Reproduced 8 concrete Lean probes in `.tmp/probe406_decode.lean`
(private scratch, NOT committed): 2 positives (suffix intact, incl. an
`encode`-computed prefix) and 6 negatives (mod=1, REX-75, LOCK prefix,
`0F 05`, truncated 9-byte `movImm`, plus a concrete length-accounting
evaluation). `./lean-probe`: **0 errors**.

## Deliverable

`dokumente/x86/AUDIT-DECODE-BOUNDARY.md`: per-path length table with
file/line evidence, suffix-handling ledger, refusal inventory (pinned +
newly probed), the provenance finding (§5: `Decodiert` is evidence-free;
`byteschritt` gates, `schritt` trusts — contained today, P1 discipline
proposed), the exact open-lemma ledger (§6: general length soundness,
arbitrary-byte encoder soundness, encode injectivity — all already in the
files' own CUTS, owner lane 435, no duplication), P0-P3 prioritized tasks,
and a proofs-vs-CUTS-vs-claims verdict (all honest; no bug invented).

## Lean build result

Full `./lean-bau`: **Build completed successfully (392 jobs)**,
2026-10-01. No Lean changes made, so no new theorems, no new axioms, no
`_zeuge` obligations, no `gabbro_ziel` impact. The audit proposes no Lean
or Rust change.

## What remains open

- P0 lemmas (§6) belong to scheduled lane 435 (DecodingCoverage); P1 to
  the validator skeleton (lane 349); P3 pins are optional for the codec
  file owner. Nothing here blocks them.
- The `.tmp` probes are intentionally uncommitted scratch; promoting the
  P3 pins into `Codec.lean` is the file owner's call, not this lane's.

## Task feedback

The task is sound as written; the "do not invent a bug because an
explicitly OPEN bridge is OPEN" clause was load-bearing — the two most
tempting findings (arbitrary-input length soundness, decoded-image
coverage) are both already owned OPEN items, and the audit records them
as such. No premise of the task was weakened; no second IR, toy machine,
or vacuous theorem was built.
