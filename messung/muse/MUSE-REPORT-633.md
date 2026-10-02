# MUSE-REPORT-633: Independent review of Lane 632 (SourceValidatorConnection)

Lane 633, branch `muse/633`, clone `/home/simon/Dokumente/gabbro-muse/a633`.
Review-only lane: no source/Spec/clone edits; this report is the sole owned file.

## Verdict

CANDIDATE: 632 feb1e4bef5971e99cda8b12439907a8524fcbba3
VERDICT: ACCEPT

## What was reviewed

Exact author snapshot `.tmp/review/SNAPSHOT.json` (head `feb1e4b…`, base
`7bf2582…`, 3 files), owner task, `PATCH.diff`, report `MUSE-REPORT-632.md`,
build evidence, and the real producer interfaces in this clone.

## Independent checks performed

- `./lean-probe` on the exact snapshot module
  (`.tmp/review/author-632/grammatik/Grammatik/X86/SourceValidatorConnection.lean`,
  read-only, no tree edit): `0 error(s)`, exit 0. Axiom lines reproduced
  exactly: decide-theorems `[propext, Quot.sound]`, execution theorems
  `[propext, Classical.choice, Quot.sound]` — standard goal set.
- Token scan: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in code,
  no `Prop`-sorted premise, no `intro _` / `have _ :=` discard.
- Producer reality: every consumed name exists in accepted master modules —
  `SourceMemory` (`witD`, `witI/E/Hw/HL/O/R/Sigma/HT/SL`, `witVal = 42`,
  `repOk`, `slotAddr`, `RepSlot`, `zahlWort`/`wortZahl`,
  `rep_schritt_bleibt`), `ValidatorExecution` (`valEintrittStark`,
  `valStark_wohlgeformt`, `valStark_eintrag`), `LoadedExecution`
  (`bildStore`, `bildStoreMutiert`, `bildStoreWx`, `bildZustand`,
  `storeReg`, `storeFlags`), `Byteschritt`/`Codec`
  (`fetchDekodiert`, `byteschritt`, `ausgangByte`, `natByte`),
  `AccessExecution` (`byte_aus_weiter`, `realisiert_store64_gefunden`,
  `realisiert_store64_fuss`, `zugriff`, `Fuss`), `Ausfuehrung`
  (`effAddr`, `schritt_store64_erfolg`), `Speicher` (`lesbar8`,
  `read64`/`write64`, `read64_nach_write64`). `srcStmt` matches the
  `SourceMemory` witness statement shape; `certStart srcCert` matches the
  `bildStoreStart` shape.
- All 8 `srcCertOk` legs are consumed in `srcCert_sound` (rep, profile pin,
  entry admission, fetch shape, register value, address agreement,
  readability, observed byte — the `verweigert` branch is eliminated via
  the byte leg). Conclusion derives genuinely new joint facts
  (representation at post-states, source slot 42, target word read-back
  plus parse, mapping/entry legs, realised footprint exactly the slot),
  not a restatement of a premise.
- Witness `srcCert_sound_zeuge` is joint and nondegenerate: table-writing
  source (`witD`, slot 0 → 42, zero before) plus memory-changing target
  step (lowest byte 0 → 42, pre-state by `decide`) plus all four planted
  refusals (bytes/profile/map/certificate base), each by `decide`.
- `.p57` scope-pin honesty independently confirmed via `$TMPDIR` scratch
  probe: `wohlgeformt .p57 bildStore` evaluates to `true`, so the profile
  refusal is carried by the explicit scope leg as the file and CUTS state.
- No self-invented semantics (goal's own `execStmt`, accepted image/byte
  vocabulary), no desired-simulation premise (`SrcByteCert` pure data,
  `srcCertOk` recomputed Bool), no signed/modular/FP/fault or
  byte/word-atomicity conflation, no silicon claim, no universal validator
  claim. CUTS honestly leave `valX86_sound` and full source-to-bytes OPEN.
- Patch scope is exactly the 3 owned files; no source/Spec/checker/emitter
  or friend-reserved optimiser edits.

## Integration note (not a defect)

`git apply --check` of the candidate patch fails only on the
`Grammatik.lean` import hunk: this clone has moved past the snapshot base
(`ExpressionLowering` import added since). The candidate change is one
additive import line — merge via the standard `Grammatik.lean` import
union, then rebuild.

## Open items

Single-fragment connection only (one `.int` slot, one `assignSlot` form,
one store image). Generic closing proof, concurrency bridge, other
widths/forms, relocation re-decode, cost/time remain OPEN per the file CUTS.
