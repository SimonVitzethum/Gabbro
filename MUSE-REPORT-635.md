# MUSE-REPORT-635: Independent review of candidate 634 (SourceCodeFrame)

Lane 635, clone `/home/simon/Dokumente/gabbro-muse/a635`, branch `muse/635`.
Owns ONLY this report. No source, Spec, checker, emitter or other clone edits.

CANDIDATE: 634 5c1397e22189aee7c3aad819c3a9ce4e331b7645
VERDICT: ACCEPT

## What was reviewed

Exact snapshot `.tmp/review/SNAPSHOT.json` (author 634, base
`a71b7e638d008cab47f352326a09e37980cff314`, files `MUSE-REPORT-634.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/SourceCodeFrame.lean`),
the owner task (lane 634), the full `PATCH.diff` (702 lines) and every real
producer/consumer interface named by the candidate. The candidate was NOT
merged into this tree; verification ran read-only plus a queued
`./lean-probe` on the exact snapshot copy.

## Independent reproduction

- `./lean-probe .tmp/review/author-634/grammatik/Grammatik/X86/SourceCodeFrame.lean`:
  `== 0 error(s) in the COMPLETE output` (reproduced twice; full axiom
  printout matches the author's BUILD-EVIDENCE claim line for line).
- Axioms: `quellDaten_schritt_laesst_code` and
  `quellDaten_schritt_laesst_code_zeuge` depend on exactly
  `[propext, Classical.choice, Quot.sound]`; all narrow/frame lemmas on
  `[propext, Quot.sound]` or less. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` (exact-token grep clean; the only substring hits
  are English words "admitted"/"admits" in comments). CUTS block present,
  `#print axioms` for every main theorem present.
- `PATCH.diff` adds one new file plus exactly one additive umbrella import
  plus the author report. It does not apply verbatim onto this reviewer's
  newer HEAD only because master moved on (`ValidatorExecution` import added
  after the candidate base) — context drift, not a candidate defect; the
  import itself is a clean union with no conflict. No existing theorem
  touched, no friend-reserved optimiser file touched, no source/Spec/
  checker/emitter edit.

## Interface and semantics checks (all pass)

- Every external name resolves to a real accepted producer in the current
  tree: `repOk`/`RepSlot`/`rep_schritt_bleibt`/`zahlWort`/`wortZahl`/
  `slotAddr`/`witD`/`witV`/`witO`/`witR`/`witI`/`witE`/`witSigma`/`witSL`/
  `witVal`/`witHw`/`witHL`/`witHT` (SourceMemory), `codeFremd_von_abbildung`/
  `geholt_nach_erlaubtem_schreiben`/`fetchDekodiert_nach_erlaubtem_schreiben`/
  `codeBytes_nach_erlaubtem_schreiben`/`an_rip_nicht_fremd`/`rahmenBild`/
  `rahmenStart`/`rahmenCode`/`rahmenDaten`/`rahmen_paar`/`rahmen_reg_ungleich`/
  `rahmen_rip_summe`/`rahmen_code_code`/`rahmen_daten_daten`/
  `rahmen_code_schreiben_verweigert`/`rahmenBild_wohlgeformt` (ImageStoreFrame),
  `ketteStart`/`ketteSpeicher` (Byteschritt), `probe_unversetzt_8196`
  (OverlapRefusal), plus `geladen`/`abteilFinden`/`paarweise`/`virtReich`/
  `wxOk`/`istCodeAbschnitt`/`istDatenAbschnitt` and the real
  `write8/16/32/64` with their permission checks and store frames. Nothing
  is self-invented; the source leg is the real `execStmt` table write and
  the target leg is the real decoded fetch (`geholt`, `fetchDekodiert`).
- No assumed-unchanged premise: foreignness is DERIVED from the checked
  mapping in the main theorem (`codeFremd_von_abbildung`) and from the
  Nat-interval bridge with explicit no-wrap bounds in the unaligned probe;
  every unchanged byte comes from an actual successful store frame. The
  `hsMem : s.speicher = m` premise is memory identity between the two legs
  (the explicit minimal connection, disclosed in the author report), not an
  unchanged-memory conclusion — legitimate and honestly documented.
- No conflation of any rejected kind: values are generic `Zahl lo hi` with
  the producer round-trip; addresses are Nat with explicit no-wrap bounds
  (wrap is refused, not argued away); no FP, no signedness claim, no fault
  handling, no concurrency/atomicity claim (sequential `Speicher` steps,
  TSO/GX explicitly left open in CUTS).
- Not a wrapper: the width-generic `CodeFremdN` infrastructure (§1), the
  1/2/4-byte fetch/decode frames (§2) and the source-to-target main frame
  (§3) are new connections consumed by direct statement lowering; producer
  theorems are called, never restated.
- Every main-theorem premise is used (`rep_schritt_bleibt` consumes the
  source premises, the mapping premises feed the derived foreignness,
  `hsMem` transports the store, the shapes feed both `wxOk` verdicts).

## Witness and refusals (all pass)

- `quellDaten_schritt_laesst_code_zeuge` is joint and non-degenerate on
  both sides: one table the witness function writes (`witV.schreibt`),
  reached `execStmt` step with source slot `0 → 42`
  (`cases hExec; rfl` on the real execution result, not a fixture),
  real target word write moving the byte `0 → 42`, preserved fetch/decode,
  all mapping premises discharged jointly inside the `hMain` application.
- Planted refusals are concrete and `decide`-proved: SM-WX (generic
  writable+executable section), SM-SPAN at both section ends, SM-SCHUTZ
  (guard), SM-UMBRUCH (wrap, no interval verdict at the address-space top),
  SM-UEBERLAPP via the generic producer `an_rip_nicht_fremd`; the witness
  additionally carries the code-store and span refusals plus wellformedness.
- CUTS is honest: one `assignSlot` shape on one `.int` slot, narrow §2 is
  target-only, no `valX86_sound`, no closing theorem, no silicon/OS-loader
  claim. Full source-to-final-loaded-bytes correctly stays OPEN.

## Task coverage

Bounds, end-spanning intervals, guard, unaligned and multi-byte stores,
invalid overlap refusals, generic values/layout/code intervals — every item
of the owner task is present and checked. No scope defect found in either
the task or the candidate.

## Remaining work (not this candidate's debt)

Consumer-side closing theorem (`valX86_sound`, whole-unit lowering),
narrow-store source correspondence, per-access TSO/GX bridge — all named in
CUTS and belonging to follow-up lanes.
