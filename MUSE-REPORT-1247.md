# MUSE-REPORT-1247: Extended context state across interrupts and context switches

Lane 1247, clone `/home/simon/Dokumente/gabbro-muse/a1247`, branch `muse/1247`.
Owned files only: `grammatik/Grammatik/X86/HwContextState.lean` (new, ~1590 lines),
one import line in `grammatik/Grammatik.lean`, this report.

## What was done

Modeled FXSAVE/FXRSTOR (legacy 512-byte area, modeled footprint: MXCSR at
bytes 24-27, XMM0-15 at bytes 160-415) and XSAVE/XRSTOR for the XCR0-enabled
SSE component as footprint-checked memory accesses on the coherent machine
(`HwMaschine`/`HwSchritt`/`HwWf`/`HwAdapter`), reusing unchanged: TSO
`issueByte`/`loadByte`/`flushKern`/`issueListe`, `mxcsrReserviertFrei`/
`ldmxcsrArchOk`, `xcr0SseBereit`/`Xcr0Bild`, `asyncMasch`/`asyncSchritt`,
`bytesWort_wortByte`, `vecJoin_split`, `addrOff_inj8` (idea). Silicon facts
checked against the clone-local Intel SDM 325462-093US text extract
(`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`): FXSAVE64 map
Table 1-42 (offsets 56665-56698), 16-byte alignment #GP (56533), FXRSTOR
reserved-MXCSR-bit #GP (56379-56380, exception tables 56400-56403 ff.),
LDMXCSR reserved-bit #GP (62467), XSAVE RFBM = XCR0 AND request with
MXCSR in component 1 (13928, 13956), XSAVE 64-byte alignment #GP (13950).

Sections in the file: (1) layout/image/decode/pure identity; (2) footprint
(260 offsets), entries, TSO forwarding bridge lemmas; (3) machine save with
TSO-buffer theorems; (4) machine restore with save/restore identity;
(5) XSAVE/XRSTOR XCR0 gate on the shared paths; (6) handler/switch
preservation over HwInterrupts; (7) `CtxSchritt` relation, TSO embedding,
`adapterContext` plug; (8) two-core joint witness; CUTS; `#print axioms`.

Main theorems: `mxcsr_rundlauf`, `ctxRundlauf_pur`, `neuestens_append`,
`neuestens_nicht_enthalten`, `neuestens_einmal`, `ctxLade_geladen`,
`fxDekodiere_kongr`, `ctxSpeichern_erfolg/puffer/kein_speicher/wf`,
`ctxSpeichern_fehlerGP_falsch_ausgerichtet`,
`ctxSpeichern_verweigert_ohne_schreibrecht`, `ctxWiederherstellen_erfolg/wf`,
`ctxWiederherstellen_fehlerGP_falsch_ausgerichtet/verweigert_ohne_leserecht/
fehlerGP_reserviert`, `ctxRestore_stimmt_ldmxcsr_ueberein`,
`ctxRundlauf_maschine` (save-then-restore identity), `ctxXSave/ctxXRstor`
(+`weiter` extraction, shared-layout agreement, UD/GP/refusal outcomes,
Wf, buffer, `ctxXRundlauf_maschine`), `asyncMasch_fp_still/xmm_still`,
`handlerErhaeltKontext`, `wechselStelltHer`, `CtxSchritt` + `ctxSchritt_wf`,
`ctxLade_ist_hw/gibAus_ist_hw/spüle_ist_hw`, `adapterContext` (+ core
agreement, observation refusal, Wf projections), and the joint witness
`ctxWit_zeuge` (two 260-entry buffered saves, owner-only forwarding of
`0x80`/`7` vs foreign zeros, drain changing memory 0 to `0x80`, machine
round trip `0x1F80`, four planted refusals, reserved-bit #GP, NMI
control-word preservation, well-formedness, pure round trip).

## Checks

- `./lean-probe grammatik/Grammatik/X86/HwContextState.lean`: 0 errors
  (only harmless unused-variable linter warnings in nil branches).
- `./lean-bau` (full project): `Build completed successfully (642 jobs).`
- `#print axioms`: `[propext]` or `[propext, Quot.sound]` throughout
  (subset of the `gabbro_ziel` standard; `funext` used once leaves no trace).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (two `admit`
  substrings are inside the English word "admitted" in doc comments).
- Every premise is used; no conclusion restates a premise; no `Prop`-typed
  premise; no theorem quantifies over program syntax (nothing falls under
  rule 13's per-theorem `_zeuge` duty; the joint `ctxWit_zeuge` covers the
  mechanism's witness demand).

## What remains open (see CUTS)

No x87 state (bytes 0-23, 32-159 outside footprint), no MXCSR_MASK field,
no XSAVE header/extended/supervisor regions, no AVX/YMM/ZMM, no
#NM/#UD-CPUID/#SS/#PF/#AC/CPL/canonical faults, no FINIT semantics, handler
bodies between save and restore are user logic, no timing claim, no W/GX
bridge, no hardware correspondence beyond self-consistency.

## Task remarks

Nothing in the task looked wrong. Two deviations worth recording: (a) the
save footprint is 260 sparse bytes (24-27, 160-415), not a contiguous
512-byte image, because x87/MASK/reserved/available regions have no model
in this tree — documented in CUTS; (b) `cases h : e` generalizes the goal
over `e`, which forced stating success-shape proofs accordingly (noted
in-file at both sites). No diagnostic/gift/example numbers were needed
(no new checker rule; Lean-only lane).
