# MUSE-REPORT-836: Composition closing — time-bound closing

Lane 836, clone `/home/simon/Dokumente/gabbro-muse/a836`, branch `muse/836`
(verified: `.git/HEAD` = `ref: refs/heads/muse/836`; no pre-existing
`Compose*` file). Owned files only:
`grammatik/Grammatik/X86/ComposeTimeBound.lean`,
`grammatik/Grammatik.lean` (one appended import line),
`MUSE-REPORT-836.md`.

## What was done

New file `grammatik/Grammatik/X86/ComposeTimeBound.lean` closes the
fuel-bounded validation acceptance to the proved work/time transfer over
the SAME decoded list. Producer/consumer interface (stated in the file
header and in `ComposeTimeBound_verbindung` doc):

- PRODUCER (`ValidationBudget`, accepted): `decodeFuel` traversal of
  canonical bytes yields decoded prefix `xs` with no rest; derived legs
  are `validAllFuel_some_empty` (full acceptance) and
  `decodeFuel_ins_le_fuel` (count bound `xs.length ≤ fuel`).
- CONSUMER (`BudgetExecution`/`TimeTransfer`, accepted):
  `budgetAusfuehrung_transfer` over `Deckung` work coverage plus the
  named per-form hardware bound, with admission split by
  `zeitTransferZulaessig_braucht_ok`.
- No internals re-proved, no new interpreter/executor/cost model, no new
  semantics. Tuning tables never enter: `expand` maxima stay
  backend-declared data checked by admission Bools.

Exact new names:

- `ComposeTimeBound_verbindung` (TARGET): generic over arbitrary
  admitted `(s p fuel bs xs src B t)`; all five premises used; yields
  validation acceptance, both admission halves, the count bound and
  `∀ k, expandBound s src = some k → t ≤ B * k`.
- `ComposeTimeBound_verweigert_timeout`: fuel 1 admits no decoded prefix
  of `[natByte 195]` (reuses `wit_timeout_refuses`).
- `ComposeTimeBound_verweigert_ret`: lone `ret` admits no aggregation
  (reuses `laufKosten_zeuge_verweigert`; axiom-free).
- `ComposeTimeBound_verweigert_retry`: unbounded retry behind a constant
  kills the admission premise (reuses `zeitTransfer_verweigert_retry`).
- `zeugePushStart`: canonical state with `rax = 42`.
- `zeugePush_aendert`: the composed single-`push` step reaches a state
  whose stack byte observably differs (real memory-changing run of
  exactly the decoded/aggregated/bounded step).
- `ComposeTimeBound_verbindung_zeuge` (TARGET companion): all premises
  jointly inhabited on admitted data (`blattSummary`, `profilZeuge`,
  fuel 2, `[natByte 80]`, single `push64 rax`, src 1, B 2, t 2), with
  the derived bound, the table-writing source fixture's reached entry
  run (`ziel_ort_einfaden_zeuge`: slot 0 at start, 5 at entry,
  `eSetze` writes) and the composed memory-changing run.

Axioms (from `./lean-probe`, 0 errors):
`ComposeTimeBound_verbindung` [propext, Quot.sound],
`_timeout` [propext], `_ret` none, `_retry` [propext],
`zeugePush_aendert` [propext, Quot.sound],
`ComposeTimeBound_verbindung_zeuge` [propext, Classical.choice, Quot.sound].

## Checks

- `./lean-probe grammatik/Grammatik/X86/ComposeTimeBound.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (whole `grammatik/`): `Build completed successfully
  (509 jobs).` including `Built Grammatik.X86.ComposeTimeBound` and
  `Built Grammatik`.
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`:
  `== 0 error(s)`; `gabbro_ziel` depends on axioms
  `[propext, Classical.choice, Quot.sound]` (standard, unchanged).
- One elaboration snag met and repaired: flat anonymous-constructor
  assembly of the joint witness mis-split at the nested source-run
  existential; fixed by building the source-run witness as a separate
  `have hSrc` first. No premise weakened, no conclusion weakened.
- Untouched as required: no diagnostic/gift/example/CLI numbers, no
  MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files.

## What remains open (explicit CUTS in the file)

- `Deckung` stays carried data: which source step lowers to which target
  segment with which multiplicity comes from the lowering/IR producer
  (`DerivedWorkBound` derives it for its fragment; generic
  validator-soundness is phase-B work with the decoder/bridge lanes).
- No per-site waiting-exclusion proofs, no cycle bounds, no
  constant-time/CAS-progress promises, no full hardware model (caches,
  TLBs, interrupts, faults, concurrency interleavings stay with their
  owners; the per-access target-to-W/GX simulation is the open bridge).

## Task assessment

Nothing in the task statement appears wrong. The ZEUGE target
(`ComposeTimeBound_verbindung` + `_zeuge`, jointly inhabited,
non-degenerate, memory-changing reached run) is met as stated.
