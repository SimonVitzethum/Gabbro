# MUSE-REPORT-679: Exact review of author 678 hardware-model completion matrix

CANDIDATE: 678 0f87c00f2402df2ac719f6ced755d8ecbea3d276
VERDICT: ACCEPT

## What was done

- Verified clone `/home/simon/Dokumente/gabbro-muse/a679`, branch `muse/679` (match; proceeded).
- Reviewed the coordinator-pinned exact snapshot `.tmp/review/author-678/`
  (SNAPSHOT.json: author 678, head `0f87c00f2402df2ac719f6ced755d8ecbea3d276`,
  base `aefa9ed2`, files `MUSE-REPORT-678.md` +
  `dokumente/x86/HARDWARE-MODEL-COMPLETION.md`, clean), comprising the matrix
  (555 lines), the author report, PATCH.diff (642 lines) and BUILD-EVIDENCE.json.
  No other clone, no control dir, no network was touched.
- Checked PATCH.diff adds exactly the two owned files; BUILD-EVIDENCE shows the
  author committed via `commit.sh` with the correct co-author line and a clean
  tree. Ownership respected.
- Re-verified every load-bearing factual claim against the actual tree in THIS
  clone (master `3601dabc`; author's base `aefa9ed2` is one docs generation
  older, so line numbers were treated as approximate and names/counts as exact).
  This review is not approval from link checks alone.

## Verification results (all pass)

- File/line evidence: `ExtendedExecution.lean` 828 lines with `ExtInstr` at :38
  (inductive), `decodeExt` :64, `stepExt` :305, `fetchExt` :576,
  `extByteschritt` :616; `LockedOps.lean` 521 lines with
  `cas_fehlschlag_stottert`; `ScalarFloat.lean` 1508 lines with class-level NaN
  agreement and sticky-MXCSR OPEN in CUTS; `ScalarFloatCodec.lean` 710 lines;
  `NarrowCodec` 959 lines; `Typen.lean` 87 lines with `af : Option Bool`;
  `DecodeFault.lean` 276 lines; `EntryState.lean` 553 lines;
  `EntryExecution.lean` 375 lines; `Bild.lean` `kanonischBereich` :43 with
  48/57 profile theorems :99-115; `OhneUmbruch` in `Speicher.lean` ~:160;
  `Ausfuehrung.lean` struct-update note :845-846; `BridgeRead.lean` CUTS
  device/MMIO/DMA cut ~:450; `TSO.lean` `paket_reisst`; `OverlapRefusal`
  `zugriffOk`/`aliasZulassen`; `AccessExecution` `realisiert_fuss_abdeckung`;
  `FloatExceptions` `guard_sticky_offen`.
- Omission greps rerun here: no XCR0/OSXSAVE/CPUID model exists anywhere under
  `grammatik/Grammatik/X86/` (only `osXmm : Bool` in `FeatureProfile.lean`
  :42-63 with `hat`-lemmas ~:112-138). The matrix's "proved obstruction" for
  enabled state is substantiated, not asserted.
- Scope/provenance: `DIRECT-COMPILER-DESIGN.md` §2D deferred scope is real
  (:239-275), so DONE items 1/3 deferral paths cite agreed design scope, not
  invented shrink; `.tmp/HARDWARE-REFERENCES/REFERENCES.json` confirms Intel
  SDM edition 325462-093US September 2026 with no AMD snapshot; all nine
  hardware prompts `lanes/660.md`-`lanes/676.md` exist; `EMITTER-INVENTAR.md`
  §12 item 7 gaps check out (`bibliothek/linux/linux.gab:54`
  `assume os_bindung_null`; `-4095` fence in `emit.rs` `syscall_stumpf`;
  `GENERATOR_KENNUNG` is `treiber-gen-10`).
- No percentages, ETAs, or proof closure from declarations/round trips/Bool
  bits (only explicit "no percentage, no ETA" statements). No row claims
  `complete`; rows are `partial (proved)`, `unimplemented`, or carry a named
  proved obstruction with file evidence. No in-flight candidate is called
  merged, accepted, or hardware-correspondent (§0 states prompt-level
  visibility only). Codec self-consistency is never presented as silicon
  fidelity; `osXmm : Bool` is never cited as completion evidence.
- DONE condition (§6, 8 items) is finite and auditable: each item names
  files/theorems/probes, deferral requires a dated entry plus a refusing gate,
  and item 7 demands per-producer joint memory-changing fetched runs, planted
  refusals, poison+positive probes, independent review ACCEPT, and green
  build/test/emission/key-scan gates. No hidden scope shrink found.
- Follow-ups F1-F8 name exact NEW paths, stable producer dependencies, target
  sketches, negative witnesses and rejection criteria; none replans existing
  source owners or touches reserved/protected files.
- English prose throughout (German tokens are existing Lean identifiers only).

## Exact names of new definitions/theorems

None. Report-only review lane: no Lean/Rust/doc-source changes. Owned file is
this report only.

## Last build result line

No build run: nothing in this lane affects any build input (single new
Markdown report). Tree status is clean apart from this untracked report file.

## What remains open

- All producer work (660-676 candidates, independent reviews, integration,
  publication) and the F1-F8 follow-ups. The matrix is organisation, not proof;
  full typed-carrier TSO-to-W/GX and source-to-final-bytes validation stay OPEN,
  as the matrix itself records.
- Observation (not a finding): the matrix cites "62 X86 modules at the handoff
  snapshot"; this newer clone holds 97 `.lean` files under
  `grammatik/Grammatik/X86/`. The count is explicitly not completion evidence
  and the snapshot is dated, so no correction is required; future matrix
  updates should re-pin the count to the merge commit they read.

## Anything believed wrong in the task/setup

Nothing. The owner task, the snapshot contents and the evidence rule are
consistent; the author obeyed the docs-only constraint and reported no
fictitious build.
