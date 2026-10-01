# MUSE-REPORT-281: Independent foundation and byte-contract review

Lane 281 (wave B review). Branch `muse/281`. Model:
opencode-go/muse-spark-1.3-contributor. No delegation, no model calls.

## What was done

Reviewed `grammatik/Grammatik/X86/{Typen,Wort,Speicher}.lean`,
`crates/gabbro-check/src/x86/{mod,typen}.rs`, `dokumente/x86/BYTE-PILOT.md`
against `dokumente/x86/WELLE-A.md` plus reports 270/271/273. Owned files
only: `dokumente/x86/REVIEW-GRUNDLAGEN.md` (new) and this report. No code
modified, no numbers allocated, no builds run (docs-only claim checks).

## Findings

Verdict (exact strength): no error found in the inspected
equations/encodings. Verified by manual comparison plus independent
`python3` replay: CF/OF/AF/parity/SF/ZF equations with boundary replay
(`FF..FF+1` carry-only, `7F..FF+1` overflow-only, `1-2` gives
`l`+`b`/not `g`/`a`); `sext`/`maske`/LE-coefficient replay byte-exact;
unconditional footprint injectivity confirmed; per-byte independent
permissions with read-after-write needing readability besides
writability; whole-store refusal on partial permission; Rust
register/condition/width tables, `Disp32` signed edges, follow-address
relative targets, absence-is-`None`/no-rights by construction,
`lege_ab(false)` revocation fix; all 14 BYTE-PILOT rows with issue
bytes (`4D 01 C7`, `4D 8B 8C 24 F8 FF FF FF`, `41 51`, `41 5C`,
`0F 8C-8F`, `E9/E8/C3`). One doc nit: the REX byte value is implied by
field assignment, not spelled out. This is NOT machine-checked
hardware correctness and establishes no hardware correspondence.
Full detail in REVIEW-GRUNDLAGEN.md sections 1-6.

Claim-strength corrections applied after coordinator review (this
commit): (a) the sparse-Rust/total-Lean relation is UNPROVED, so only
absence-is-`None`/no-rights by construction is stated, never a generic
safe-direction refinement; (b) the round-trip-catches-divergence
assertion is removed — two matching bugs preserve round-trip and two
parallel implementations can agree on a bug, so independently pinned
architecture bytes plus independent review are needed and generic
codec/hardware correspondence stays OPEN; (c) architecture rechecks
are disclosed as trained-knowledge comparison (no primary manual
available locally, none fetched), with exact replay commands/results
in REVIEW-GRUNDLAGEN.md section 6.

## Checks

- `python3` boundary/encoding probes: all match the sources; exact
  commands and verbatim results in REVIEW-GRUNDLAGEN.md section 6.
- No Lean/Rust files touched: `git status` shows only the two owned files.
- No full builds per task (`No gratuitous full builds, docs-only claim
  checks`); last green builds are recorded in reports 270/271/273 and
  WELLE-A.md (Lean 366-367 jobs, Rust 1468 passed).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` added (no code).
- Generic/no-weakening check passed; stronger claims (execution,
  codec round-trip AND codec/hardware correspondence, TSO, source
  chain, ABI, float/time) correctly open.

## Open / assessment

Nothing in the reviewed tasks appears wrong. The full source-to-bytes
chain remains OPEN, as the task states. No follow-up numbers needed.
