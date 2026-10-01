# MUSE-REPORT-412: Adversarial implementation audit FLOAT-SIMD

Clone: `/home/simon/Dokumente/gabbro-muse/a412`, branch `muse/412` — verified
before any edit (`pwd` + toplevel + branch). No Lean, Rust, checker, Spec,
goal, emitter, Typen/execution/codec or friend file touched.

## What was done

Read in full: `grammatik/Grammatik/X86/Gleitprofil.lean` (653 lines),
`grammatik/Grammatik/X86/Vektor.lean` (651 lines), source float surface
(`Typen.lean`, `Semantik.lean`, `Gleitkomma.lean` defs by grep + section
reads), pilot `Befehl` (`Typen.lean:53-67`), `X86/Speicher.lean` write64/
no-wrap treatment, plus `DIRECT-COMPILER.md`, `WORK-ALLOCATION.md`,
`FLOAT-ZEIT.md` and the three prior reviews for obligation context (cited,
not duplicated). Wrote the owned deliverable
`dokumente/x86/AUDIT-FLOAT-SIMD.md`: actionable audit with
file/theorem/line evidence, reproduced probes, proof-vs-CUTS verdicts per
area (binary64 source, control/context, SNaN, exceptions/FMA rounding, SIMD
alias/tail bounds, feature admission) and prioritized bridge tasks P0-P3
with consumer owners (A6/340, C4/348, reserves 424/425/426, C3/347).

New definitions/theorems: none (docs-only audit task; no new Lean module).
Reproduced probes (private scratch, not corpus files):
`.tmp/probe412-float-simd.lean` (reset-word accept, FTZ refuse, f32
conflation vs f64 separation, NaN-payload openness, `simdFreigabe = false`,
`#check @vecWrite_teilt` / `@SSEAdd32Entspricht`) and
`.tmp/probe412-snan.lean` (SNaN-shaped payload classifies `.nan` with silent
bit propagation; sticky flags verdict-neutral both directions).

## Findings (summary; evidence in the audit)

No false theorem or false model semantics found — both modules are correct
within their stated claims and their CUTS honestly list what is OPEN. Do not
read this as closure: the audit records one ordering constraint (P0: A6 must
keep f32/FMA/packed refusals syntactic and premise every scalar op on checked
`mxcsrGueltig` establishes/preserves) and three consumer-owned bridge gaps
(P1: class-level NaN relation + `nan_payload_unbeobachtbar` + sticky-flag
joint premise for SNaN quieting, A6 + 425; P2: entry-establishes / writer-
preserves / handler save-restore / CPUID-gated profile, 348 + A6 + 424; P3:
vector footprints incl. `OhneUmbruch16` discharge via B2, tearing
correspondence, two-chunk budget accounting, 426 + 347 + bridge). Two
precision notes future consumers must respect: `vecWrite` inherits (not
strengthens) scalar wrap behaviour — discharge `hno` at the validator, do
not fork a second refusal register; and `SSEAdd32Entspricht` is a named
unproved `def`, so citing model `add` as executed-SSE behaviour without the
non-observability lemma would be the defect, which no one commits today.

## Checks

- `./lean-probe .tmp/probe412-float-simd.lean`: 0 error(s), exit 0.
- `./lean-probe .tmp/probe412-snan.lean`: 0 error(s), exit 0.
- `./lean-bau` (full): not run — docs-only lane, no `grammatik/` change
  (nothing to rebuild; `git status` shows only the two owned files).
  Standard `gabbro_ziel` axioms untouched (no Lean change at all).

## What remains open / what I believe is wrong

Nothing in the task looks wrong; the owned-files restriction and the
no-duplicate-review instruction were satisfiable as written. Open by design:
consumer lanes P0-P3 (340 working, 348 committed candidate, 424/425/426
scheduled, 347 committed candidate) — their obligations stay OPEN until
reviewed integration, tracked in the audit's CUTS, not claimed here.

Co-Authored-By: muse-agent-412 <muse-agent-412@noreply.invalid>
