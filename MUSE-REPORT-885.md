# MUSE-REPORT-885: Optimiser rule: zero-idiom selection rule

## What was done

New file `grammatik/Grammatik/X86/OptZeroIdiomSel.lean` (plus one import
line at the end of `grammatik/Grammatik.lean`), proving the DESIGN
section 7 "Flags-aware peepholes" row for XOR-zero selection: the
zero idiom `XOR r, r` (3 bytes, flags clobbered) is selected only with
a validator-decided flag-liveness proof at the site; survivor-flag
sites keep the wide form `MOV r, 0` (10 bytes, flags preserved).

All work reuses accepted vocabulary (`ZeroIdiomXor`, `Ausfuehrung`,
`Codec`, `ExtendedExecution.stepExt`, `CostSummary.targetWork`,
`ReferenzB`); no new machine, decoder, arithmetic, source/checker/
Spec/goal/emitter change, no friend-reserved file touched.

Definitions: `ZeroSelCert` (liveness + disp + pure-window side
conditions), `zeroSelZulassen`, `waehleNull`, `weitSchritt`,
`ZeroSelNachweis` (local rewrite record + recomputed analysis
citations), `nachweisOk`, `zeroSelZeugeCert`.

Theorems: `zeroSelZulassen_tot`, `zeroSelVerweigert_lebendig`
(the DESIGN failure case), `zeroSelVerweigert_disp`,
`zeroSelVerweigert_fenster`, `waehleNull_behaelt_weit`,
`waehleNull_nimmt_idiom`, probes `probe_zeroSelZulassen_ok/_lebt`,
`weitLaenge_zehn`, `weitSchritt_laenge_ok/wert/flags/speicher/rip/
fremd`, `nullSpart_gegen_weit` (3 + 7 = 10),
`weitSchritt_laufAlt/stepExt`, `nullSchritt_stepExt` (IEEE leg: XMM/FP
untouched on both sides), `nachweisOk_tot/waehlt`,
`waehleNull_arbeit` (one retired instruction either way),
`nullGleichtWeit_register` (identical full register files),
`OptZeroIdiomSel_verbindung` (15-conjunct site connection: pilot
bytes, zero on both sides, identical registers/memories, zero flag
snapshot with `LogikGueltig`, preserved wide flags, dead demand,
admitted replacement, taken idiom, RIP past 3 vs 10),
`OptZeroIdiomSel_verbindung_zeuge` (joint witness: every premise
instantiated on `rax`/all-dead cert, store-changing reached run
byte 0 to 7, plus non-degenerate `refD` table write with
memory-changing reached F-machine run).

## Last build result

`./lean-probe grammatik/Grammatik/X86/OptZeroIdiomSel.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs)`.
Axioms: every theorem within `[propext, Classical.choice,
Quot.sound]` (the `verbindung` pair uses all three; most use fewer;
probes/`decide` facts use none). No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`; every premise is used.

## What remains open

Per CUTS: no silicon correspondence, no liveness-analysis
implementation (demand is cited site data), no source refinement or
TSO/GX bridge (both steps register-only), no cost/time claim beyond
one-for-one work and 7 saved bytes, no checker/Spec/goal claim.

## Task feedback

The task asks for preservation "including IEEE, contracts, call logs,
concurrency and budget" at a peephole rule. This is covered at the
target-step level the rule lives at: IEEE via both `stepExt` lifts
(FP/XMM untouched either way), contracts via identical full register
files, call logs/concurrency via untouched memories and succeeding
register-only steps (no event, no shared access, no fault change),
budget via unchanged `targetWork` plus the 3-vs-10 RIP accounting.
A source-level `execEnd` equality (as in OptFoldConst) would need the
lowering map, which belongs to the lowering lane, not to this rule
lemma; the layered split is stated in CUTS rather than bridged here.
