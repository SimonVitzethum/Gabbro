# MUSE-REPORT-679: Exact re-review of author 678 hardware-model completion matrix

CANDIDATE: 678 a4276ebf58308cb262b5b2396759ab03e72d1663
VERDICT: ACCEPT

## What was done

- Verified clone `/home/simon/Dokumente/gabbro-muse/a679`, branch `muse/679` (match; proceeded).
- This is a FRESH review of the NEW pinned snapshot `.tmp/review/SNAPSHOT.json`
  (author 678, head `a4276ebf58308cb262b5b2396759ab03e72d1663`, base
  `aefa9ed2`, files `MUSE-REPORT-678.md` +
  `dokumente/x86/HARDWARE-MODEL-COMPLETION.md`, clean). The previous verdict on
  `0f87c00f` is superseded and was NOT carried over: every finding below was
  re-checked against the new candidate files (matrix 658 lines, report 94
  lines, PATCH.diff 764 lines, BUILD-EVIDENCE.json).
- BUILD-EVIDENCE confirms the chain in the author clone: branch `muse/678`,
  rev1 commit `0f87c00f`, repair commit `a4276ebf` via `commit.sh` with correct
  co-author line, clean tree afterwards. PATCH.diff adds exactly the two owned
  files. No other clone, no control dir, no network touched.
- Re-verified all load-bearing claims against the actual tree in THIS clone
  (master `3601dabc`; author base `aefa9ed2` is slightly older, so line numbers
  were treated as approximate, names/counts as exact). Not approval from link
  checks alone.

## The three repairs (all verified, none removes evidence)

1. **Non-demotion rule (§5) + DONE 6A.1/6A.3 rewritten.** Agreed essential
   families (design §2D list, verified real at `DIRECT-COMPILER-DESIGN.md`
   :239-275) with all observable/fault/TSO/async/control obligations can never
   complete by refusal, CUTS move or unilateral deferral; only already-agreed
   deferred families (or a later explicit Simon change) may stay deferred. The
   old "move to §5 with a dated refusal" escape hatch is closed. Genuine
   strengthening; consistent with design §2D; no new proof claim.
2. **DONE split into 6A (hardware model) vs mandatory 6B (follow-on).** 6A
   items 1-8 name files/theorems/probes, finite and auditable; 6B items 1-3
   keep the per-access TSO→W→GX bridge, image/ABI/entry/budget connection,
   `valX86_sound` + closing theorem, and full publication + Rust backend as
   mandatory OPEN requirements. The atomicity classification rule (6A item 4
   owns target facts: single-copy table, LOCK unit, fence drain, tearing,
   fault-vs-observer order; 6B item 1 owns the simulation mapping) is explicit
   and prevents re-abstraction by bridge consumers. Rows J/K annotated with
   their 6B homes; F1–F6 → 6A, F7 (depends on 6A-4 facts + TSO-wave
   interfaces) and F8 (depends on 6A DONE + F7) → 6B. No obligation dropped.
3. **Exact reviewer pairs replace "author + 18".** 661→660, 663→662, 665→664,
   667→666, 669→668, 671→670, 673→672, 675→674, 677→676 — each re-read VERBATIM
   in `lanes/661.md`–`lanes/677.md` of this clone; all nine match. The 677
   anomaly (reviews 676, parenthetical title repeats the 660 title) is real and
   is recorded verbatim without inference, exactly as the author states. No
   verdict on any pair is claimed; 6A.7 requires each reviewer's committed
   VERDICT on its exact candidate.

## Verification results (all pass)

- All rev1 evidence re-confirmed on the new files: `ExtendedExecution.lean`
  828 lines (`ExtInstr` :38 inductive, `decodeExt` :64, `stepExt` :305,
  `fetchExt` :576, `extByteschritt` :616); `LockedOps.lean` 521 lines with
  `cas_fehlschlag_stottert`; `ScalarFloat.lean` 1508 lines (class-level NaN,
  sticky OPEN in CUTS); `ScalarFloatCodec` 710 / `NarrowCodec` 959 lines;
  `Typen.lean` 87 lines (`af : Option Bool`); `DecodeFault` 276 /
  `EntryState` 553 / `EntryExecution` 375 lines; `kanonischBereich`
  (`Bild.lean` :43, 48/57 theorems :99-115); `OhneUmbruch` (`Speicher.lean`
  ~:160); `Ausfuehrung.lean` struct note :845-846; `BridgeRead.lean` CUTS
  device/MMIO/DMA cut ~:450; `paket_reisst`; `zugriffOk`/`aliasZulassen`;
  `realisiert_fuss_abdeckung`; `guard_sticky_offen`.
- Omission grep rerun here: no XCR0/OSXSAVE/CPUID model anywhere under
  `grammatik/Grammatik/X86/` (only `osXmm : Bool`, `FeatureProfile.lean`
  :42-63). Both "proved obstructions" substantiated.
- Scope/provenance re-confirmed: REFERENCES.json (Intel SDM 325462-093US,
  September 2026, no AMD snapshot); all nine author prompts 660-676 plus all
  nine reviewer prompts 661-677 present; `linux.gab:54`
  `assume os_bindung_null`; `-4095` fence in `emit.rs`; `GENERATOR_KENNUNG`
  `treiber-gen-10`.
- Counts resolved: matrix now says "94 X86 modules, 50,368 physical lines,
  measured in this clone". `git ls-tree aefa9ed2 --name-only
  grammatik/Grammatik/X86/ | wc -l` in THIS clone returns exactly 94 —
  consistent with the author's base (this master's 97 files / 52,130 lines
  include three files from later merges). My rev1 staleness observation is
  repaired and closed.
- Rows A–K preserved (A–I byte-identical in substance to rev1; J/K gained only
  the 6B annotations). No row claims `complete`; no in-flight candidate called
  merged/accepted/hardware-correspondent; codec ≠ silicon fidelity throughout;
  §8/CUTS honestly state this matrix is UNREVIEWED here and no 679 verdict
  exists in the author clone. No percentages/ETAs. English prose (German
  tokens are existing Lean identifiers only).

## Exact names of new definitions/theorems

None. Report-only review lane: no Lean/Rust/doc-source changes. Owned file is
this report only.

## Last build result line

No build run: nothing in this lane affects any build input (single Markdown
report). Tree clean apart from the staged report update.

## What remains open

- All producer work (660–676 candidates, their reviewers, integration,
  publication), the F1–F8 follow-ups, and the full 6B follow-on. The matrix is
  organisation, not proof — as it states itself.
- Minor observation (not verdict-changing, recorded for the next matrix
  update): F6 reads "depends on 676, TSO bridge", but under the new
  classification rule the model-side facts it needs are 6A item 4, while "the
  TSO bridge" (full per-access simulation) is 6B item 1. Suggest "depends on
  676 and the 6A item 4 atomicity facts". Imprecise dependency wording in a
  future-task sketch; no guarantee weakened, no false closure.

## Anything believed wrong in the task/setup

Nothing. The repair instruction, the new snapshot and the evidence rule are
consistent.
