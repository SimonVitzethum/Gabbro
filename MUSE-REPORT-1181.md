# MUSE-REPORT-1181: Nested interrupt delivery, #DF and handler entry

Lane 1181, clone /home/simon/Dokumente/gabbro-muse/a1181, branch muse/1181.
Owned files only: `grammatik/Grammatik/X86/HwNestedInterrupts.lean`,
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

Follow-up of lane 1125 (`HwInterrupts.lean`): closed all four of its
CUTS gaps -- nested delivery, #DF escalation, handler-entry state,
and a concrete maskable-success witness (with TWO maskable gates,
not one). New file `grammatik/Grammatik/X86/HwNestedInterrupts.lean`
(~1700 lines), lifting the accepted `asyncSchritt`/`liefere` delivery
and the accepted buffered word effects unchanged (never copied).

Definitions: `dfVektor`, `dfCode`, `verschachteltSchritt`,
`DfErgebnis`, `dfVektorVon`, `dfCodeVon`, `liefereMitDf`,
`puffereRahmen`, `rahmenByte_ausgabe`-family, `HwStern_verkettet`,
`hwWortAusgabe_stern`, `iretLese`, `iretIf`, `iretHwNeu`,
`iretSteuerNeu`, `iretFertig`, `iretSchritt`, `intWf1181`,
`nullSelektor`, `adapterVerschachtelt`, `NestEreignis`,
`HwNestSchritt`, two-gate witness memory (`nestMem`, `nestSteuer`,
`loWit32`, `loWit33`, `evMask32`, `evMask33`, `evMaskiert32`,
`evNmi2`, `nestStart`, `nestD1`, `nestVerschachtelt`, `dfQ1`,
`dfQ2`, TSO/frame/IRET observation defs).

Theorems (selection): `verschachtelt_verweigert_erster`,
`verschachtelt_verweigert_abbild`, `verschachtelt_erfolg`,
`verschachtelt_maskiert_verweigert`, `asyncSchritt_wf_allgemein`,
`verschachteltSchritt_wf`, `liefereMitDf_erste_fehlschlaegt`,
`liefereMitDf_doppelt`, `liefereMitDf_zugestellt`,
`verschachtelt_vereinbarung` (nested wechseln/wechseln agreement
with both accepted `liefere` legs over the descended-RSP link),
`hwWortAusgabe_wf`, `puffereRahmen_wf`,
`puffereRahmen_kein_speicher`, `puffereRahmen_zaehlt`,
`rahmenByte_ausgabe`, `HwStern_verkettet`, `hwWortAusgabe_stern`,
`puffereRahmen_stern`, `rahmenEcho_schreiben`,
`iretSchritt_wf`, `iretSchritt_erfolg`,
`iretSchritt_verweigert_lesung/_nichtkanonisch/_cs/_ss/_code`,
`adapterVerschachtelt_verweigert_erster/_maskiert`,
`adapterVerschachtelt_wf`, `hwNestSchritt_sync_einbetten`,
`hwNestSchritt_sync_nur` (exact two-way embedding),
`hwNestSchritt_wf`, ~50 decide-witness facts, `nestH1ex`,
`verschachtelt_zeuge` (joint, 33 conjuncts: trap delivery with IF
kept, nested interrupt with IF cleared, masked refusal, NMI bypass,
#DF vector 8 / code 0 with leg statuses, owner-only forwarding with
memory-changing drain, 40-entry buffered frame, IRET restoration,
wf, reached machine nest, reached relation step).

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwNestedInterrupts.lean`:
  `== 0 error(s) in the COMPLETE output`, zero warnings.
- `./lean-bau` last line: `Build completed successfully (618 jobs).`
- `#print axioms` per main theorem: only `propext`, `Quot.sound`,
  or none -- within the standard set. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` in the file (checked by search; the only
  "admit" hits are English prose "admitted").
- One real collision found by the full build and repaired:
  `nestBytes` already existed in `StackExecution.lean`; mine is now
  `nestIntBytes`. All other names verified unique by tree search.

## What remains open (also in the file CUTS)

No hardware correspondence (S1-S6 are provenance); no APIC/SMI/
timing; no W/GX bridge; DF witnessed observationally (memory has no
`DecidableEq`, so no concrete `liefereMitDf_doppelt` application --
abstract theorem plus projection/leg-status facts); IRET covers the
five-word same-frame return only; nested agreement for the
wechseln/wechseln path only; no handler execution downstream.

## Task feedback (rule 12 does not apply -- no TARGET statement)

Nothing in the task is wrong. Two remarks: (1) the "stack frame
push through the TSO buffer" has no accepted byte-level frame model
to lift, so it is built as a `hwWortAusgabe` fold at the accepted
`schiebeRahmen` slots with byte-echo agreement instead -- stated
honestly in CUTS. (2) `simp` normalises `(w == 0) = true`
conditions via `beq_iff_eq` into Props and then splits if-chains
instead of selecting branches; the NULL-selector check is therefore
wrapped in the opaque Bool def `nullSelektor` (same standing as
`istKanonisch`) -- no proof shape was bent around it, the def is
the honest interface.
