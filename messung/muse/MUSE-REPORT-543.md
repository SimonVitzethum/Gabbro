# MUSE-REPORT-543: N16 DecodeFault

## What was done

New owned module `grammatik/Grammatik/X86/DecodeFault.lean` (plus the one
additive umbrella import in `grammatik/Grammatik.lean`), implementing row N16
of `dokumente/x86/NEXT-PROOF-WAVE.md`: a fault preservation catalogue over
the accepted pilot vocabulary only.

- Reused (never redefined): `Ausfuehrung.schritt` shapes (`laengeOk`,
  `effAddr`, `read64`), `MulDiv` trapping checks (`divWeitU`/`divWeitS`,
  `md_div_halt`/`md_idiv_halt`, `zugelassen`/`rein`, `mdZustandDiv`,
  `mdZustandNull`, `muldiv_speicher_sonde`, `probe_*`), `ControlFlow`
  (`cmovMemSchritt`, `cmovMem_feheler_bleibt`, `witFalse`, `witDunkel`,
  `cmov_speicher_zeuge`, `cmovAnwenden`, `witTrue`, `witSpeicher`),
  `NarrowOps` (`narrowAdmitted`, `readBreite`, `probe_fallback_unaligned`),
  witness memory `zeugenSpeicher`.
- New definitions: `istArchitekturFehler` (architectural-fault predicate:
  only `MulDivErgebnis.hardwareHalt`), `dfZustandUeberlauf` (`2^64 / 1`
  witness state), `dfZustandIdivMin` (`INT_MIN / -1` witness state).
- New theorems:
  - `fehler_div_null_haelt` (unsigned div-by-zero traps),
  - `fehler_div_ueberlauf_haelt` (unsigned quotient overflow traps),
  - `fehler_idiv_null_haelt` (signed div-by-zero traps),
  - `fehler_idiv_oben_haelt` (signed quotient overflow above the range traps),
  - `fehler_cmov_mem_untaken_haelt` (faulting CMOV-memory refuses on the
    untaken path too; exact reuse of `cmovMem_feheler_bleibt`),
  - `bewegung_verweigert_fuer_falle` (trapping divisions never pure;
    planted motion/DCE refusal),
  - `dekodierverweigerung_ist_kein_hardwarehalt` (bad length misses, never
    a hardware halt),
  - `profilverweigerung_ist_kein_fehler` (refused narrow admission still
    answers the scalar read; exact reuse of `probe_fallback_unaligned`),
  - `bewegen_aendert_beobachtung` (same division halts under a zero divisor
    and answers `17/5 = 3 r 2` under a defined one: hoisting across a
    divisor-defining store is observable),
  - joint `_zeuge` witnesses for all five generic trapping theorems, each
    pairing the concrete instance with the quotient/remainder memory run
    (`muldiv_speicher_sonde.2`: store, readback, observable byte change)
    or the selected-word memory run (`cmov_speicher_zeuge`).
- Every premise of every theorem is used; no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`; no Prop-typed premise; no source
  Spec/checker/emitter or friend-reserved file touched.

## Build result

- `./lean-probe grammatik/Grammatik/X86/DecodeFault.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (416 jobs).`
- `#print axioms`: `propext` alone, `[propext, Quot.sound]`, or no axioms;
  all within the standard `propext, Classical.choice, Quot.sound` set.

## What remains open (see CUTS in the file)

- No extended decoding (which bytes encode DIV/IDIV) and no source
  stop-class (`hardware` in `FortschrittG`) guard/fault/channel/order
  transfer; `hardwareHalt` only names the stop class.
- No TSO/concurrency bridge, no hardware verification against silicon,
  no cost/time transfer.

## Believed-wrong items in the task

None. The suggested names (`Ausfuehrung.schritt`, MulDiv trapping checks)
all resolved to real definitions in this clone; NarrowOps and
ConditionalMove/ControlFlow were present and used as permitted.
`TARGET-PORTABILITY.md`, `IMAGE-ABI.md`, `QUELLBRUECKE.md` and
`DIRECT-COMPILER.md` were read as context; nothing in them contradicted
this module, which adds no OS/kernel trust and no ABI claim.
