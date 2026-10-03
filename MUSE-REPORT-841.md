# MUSE-REPORT-841: Composition closing — width-ledger closing

## What was done

New file `grammatik/Grammatik/X86/ComposeWidthLedger.lean` (plus the one-line
`import Grammatik.X86.ComposeWidthLedger` at the end of `grammatik/Grammatik.lean`)
closes every width conversion of the accepted narrow rows to its exactness lemma.
Producer/consumer interface: producer is the accepted `NarrowCodec` decoder coverage
shape (`narrowDecktAb`, proved decoder-side) executed by the accepted `stepNarrow`
on the same `Zustand`; consumer is the new ledger (`convApply`) with its exactness
lemmas. No accepted internal is re-proved and no interpreter/executor is duplicated:
every step, memory, flag and coverage fact is reused by name from
`Wort` / `NarrowOps` / `NarrowCodec` / `Ausfuehrung` / `Speicher`.

Definitions:
- `WidthConv` (ledger rows: `zeroExt`, `signExt`, `truncTo`, `mergeTo`, each with an
  explicit `Breite`; `unknown Nat` for unknown widths, loud fallback),
- `convApply` (known rows reuse canonical `trunc`/`sext` and accepted `mergeRegNarrow`;
  unknown rows answer `none`),
- `ledgerAdmitted` (known `true`, unknown `false`),
- `convNeedsGuard` (unknown `true`, known `false`).

Theorems (every premise is used by its proof; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`):
- `convApply_unknown`, `ledger_unknown_verweigert`, `convNeedsGuard_unknown`,
  `ledger_zero_admitted` (loud-fallback legs),
- `convApply_zero_exact` (reuses `extendNarrow_zero`), `convApply_sign_exact`
  (reuses `extendNarrow_sign`), `convApply_trunc_exact`, `convApply_merge_exact`,
  `convApply_merge_b64` (reuses `mergeRegNarrow_b64`: 64-bit is identity, no
  truncation lie), `convApply_merge_b32` (reuses `mergeRegNarrow_b32`: upper half
  cleared), `convApply_zero_b64` (reuses `trunc_b64`),
- `ComposeWidthLedger_verbindung` (TARGET): for arbitrary `d s s'` with checked
  length, coverage shape and `stepNarrow d s = some s'`, the successor lands in the
  ledger at its exactness value — 32-bit move lands the architectural merge (= the
  truncation), both extensions land the source-extended merge with the source
  conversion exact, the store carries exactly the truncated word into the canonical
  width-indexed write; flags MOV-preserved, RIP advanced. Four-way disjunction, one
  arm per accepted row, proved via the accepted per-form `rahmen`/`erfolg` lemmas.
- Pins: `pin_conv_zero`, `pin_conv_sign`, `pin_conv_merge32`, `pin_conv_unknown`,
  `pin_ledger_unknown_admission`.
- Planted step refusals reused by name in the witness: `narrow_schritt_laenge_null`,
  `narrow_schritt_speicher_verweigert`.
- `ComposeWidthLedger_verbindung_zeuge` (companion): joint witness on
  `d = store32 rbx rax 0 / 7`, `s = narrowWitState` — length, coverage and step
  premises proved jointly; data cell 8192 changes `0 -> 4` (reached,
  memory-changing, non-degenerate run through the composed step); ledger truncation
  exact; unknown width valueless; both step refusals hold.

## Last build result

- `./lean-probe grammatik/Grammatik/X86/ComposeWidthLedger.lean`: 0 errors.
- `./lean-bau`: `exit 0; 0 error line(s)`; `Build completed successfully (509 jobs)`.
- `#print axioms`: every new theorem depends only on a subset of
  `[propext, Classical.choice, Quot.sound]` (standard `gabbro_ziel` set).

## What remains open (explicit CUTS, owners elsewhere)

- 16-bit extension rows (opcodes 183/191 refuse in NarrowCodec, lane 562), narrow
  loads, narrow ALU flag snapshots (MOV discipline only).
- Fetch wiring (`Byteschritt` still pilots `decode` only).
- TSO/GX bridge, source correspondence, ABI/image/entry/relocation/cost claims.
- Hardware verification of masks/extensions/admission (stated semantics only).
- Missing producer legs owned by lanes 562-566 (wider rows), 567-569 (fetched
  execution), 570 (source memory); none assumed here.

## Anything in the task believed wrong

Nothing. One literal in my own first pin draft was wrong (`0xFFFFFF80` instead of
the full-word `0xFFFFFFFFFFFFFF80`); `decide` caught it before commit. The task's
"unknown widths fall back loudly" is realised as `none` + refused admission + loud
guard, not as a default extension — that reading matches `SignKind.unknown` in
`NarrowOps` and I kept it.
