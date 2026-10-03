# MUSE-REPORT-890: Optimiser rule — SETcc selection rule

## What was done

Proved the SETcc selection rule lemma as a generic layer-A local rewrite rule
(DESIGN §7 register shape: rule lemma over arbitrary values + validator-decided
side conditions), in the new file `grammatik/Grammatik/X86/OptSetccSel.lean`
(~400 lines), plus one import line in `grammatik/Grammatik.lean`. No accepted IR
exists (no `IR*.lean` in `X86/`), so the source fragment is the real
`Syntax`/`Semantik` `Endblock.bind` window, as the task permits. Reused without
redefinition: `Typen`, `Syntax`, `Semantik`, `ReferenzB` (incl. the `refD`/`MB`
fixtures), `X86.Typen`, `X86.Wort` (`bedingung`), `X86.ControlFlow`
(`setCCByte`, `setCCAnwenden`, `setLowByte_*`, `witTrue`/`witFalse`),
`X86.ControlCodec` (`setccSchrittBytes`, `_wert`, `_rahmen`). Read as required:
`TableLayout`, `CostSummary`, `InvariantenOpt`, and DESIGN §§3/3A/4/7/7A.

## Exact new names

- `SetccSelCert` (fields `massGeeignet`, `keinFlagLeck`, `reinesFenster`,
  `nurRegister`, `fpBereinigt`), `setccZulassen` (admission Bool).
- Refusals: `setccVerweigert_messung`, `setccVerweigert_flagleck`,
  `setccVerweigert_fenster`, `setccVerweigert_speicher`, `setccVerweigert_fp`.
- Probes: `probe_setccZulassen_ok`, `probe_setccZulassen_flagleck`,
  `probe_setccZulassen_messung`, `probe_setccZulassen_fp`,
  `probe_setccByte_true`, `probe_setccByte_false`.
- Value/frame: `setccByte_wahl`, `setccByte_nat`, `setccAnwenden_tief`,
  `setccKomplement_wahl`.
- Window/float: `setccByteSchritt_verbindung`, `setccGleit_behält`.
- Connection + witness: `OptSetccSel_verbindung`,
  `OptSetccSel_verbindung_zeuge`.

Certificate shape (named in §1 doc): local rewrite record (site, condition,
destination, expected 0/1) plus recomputed analysis citations
(flag-production fact, flag-liveness fact, measured-suitability class,
token-order fact). Refusal cases where the rule must NOT fire: predictable or
unmeasured branch (falls back to the branched spelling), live flag consumer
across the compare+SETcc window, token op in the pure window, memory (r/m8)
destination (register-only first), float-derived condition without its
unordered JP row or outside one MXCSR scope.

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptSetccSel.lean`: 0 errors. All
  `#print axioms` within `[propext, Classical.choice, Quot.sound]`
  (connection + witness use the full standard three; refusals/value/float use
  subsets; three probes depend on no axioms).
- `./lean-bau`: `Build completed successfully (511 jobs).` Whole project green.
- Goal axioms re-verified after integration via scratch probe:
  `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — unchanged, standard.
- `OptSetccSel_verbindung_zeuge` instantiates ALL premises jointly
  (`b := true`, admitted cert, `c := .e` over `witTrue.flags`, `leave`
  continuation) on non-degenerate `refD` (`refEin_schreibt`) beside the reached
  memory-changing run (`refB_erreicht`, `refB_schreibt`).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise is used.
  No new diagnostic/gift/example/CLI numbers, no MARKE changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved files touched.

## What remains open (CUTS in file)

No lowering correspondence (source `Stmt.ite` to CMP+SETcc bytes: lowering
lane); no formal machine-work transfer (OPEN per IR-VALIDIERUNG, `CostSummary`
reused untouched); no memory-destination SETcc (concurrency lane); no UCOMISD
byte correspondence (lowering lane); no new `Befehl` evaluation, checker
change, silicon/ABI/loader claim.

## Task notes (believed wrong or imprecise)

1. There is no SETcc-specific row in DESIGN §7. The applicable premises are
   spread over four rows: §3 SETcc row, §3A selection rule, §4 float row, and
   the §7 flags-aware-peephole row. The file cites all four; nothing was
   invented.
2. "Invariant/effect exports" do not exist as modules (no `*Export*.lean` in
   `X86/`; top-level `Export104/108/Sperre` are translation-validation
   exporters). I read `InvariantenOpt`, `TableLayout`, `CostSummary` instead.
3. Minor apparatus: a `bash`+`grep` read of the DESIGN doc was refused by the
   permission classifier (worked around with Read/Grep tools), and a chained
   `rm` was refused, so one 3-line scratch note remains in the git-ignored
   `.tmp/` (neutralized, not committed). Nothing pending.
