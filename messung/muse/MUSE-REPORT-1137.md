# MUSE-REPORT-1137: Coherent machine fetching from the loaded image

## What was done

NEW FILE `grammatik/Grammatik/X86/HwLoadedImage.lean` (plus one import line
appended to `grammatik/Grammatik.lean`), connecting the coherent multi-core
machine (`HwMaschine`/`HwSchritt`, lane 660) to the loaded-image fetch path
(`Byteschritt`, `LoadedExecution`, `ComposeImageFetch`). Every accepted
definition is reused unchanged; nothing is redefined.

Projection/embedding: memory coincidence (`hwBildSpeicherGleich`) plus
core/fetch-input agreement (`hwBildKernGleich`) make the core projection IS
the loaded image state (`hwBild_zustand_gleich`), hence identical fetched
bytes, fetch-and-decode outcomes and byte steps (`hwBild_geholt_gleich`,
`hwBild_fetchDekodiert_gleich`, `hwBild_byteschritt_gleich`).

Main connection: a Hw register step of a fetched pilot instruction is a
`Byteschritt` step on the core projection with the same successor core data
(`hwBild_reg_pilot_ist_byteschritt`, via `hwBild_fetchExt_pilot` and the
dispatch inversion `decodeExt_pilot_zeigt_decode`). The checked mapping yields
the fetched file-byte prefix on the machine (`hwBild_geholt_aus_datei`, via
`ComposeImageFetch_verbindung`). The stated obstruction: a fetched narrow
extension row refuses `fetchDekodiert` while the Hw machine steps it
(`hwBild_erweitert_ohne_pilot`, via `decodeExt_narrow_zeigt_decode_none`).

Adapter: `adapterBild` reuses the accepted register-path plug
`adapterInteger666` by name (no duplication), with admission, refusal and
halt-has-no-successor agreement (`adapterBild_vereinbarung`,
`adapterBild_verweigert`, `adapterBild_halt_verweigert`).

Preservation/refusals: `hwBild_schritt_wf` (lifts `hwSchritt_wf`),
`hwBild_ohne_exec_verweigert` (non-executable head byte refuses),
`hwBildWx_verweigert` (W^X image refused by the mapping check).

Joint witness `hwBild_zeuge`: accepted image (`hwBild_wohlgeformt`, profile
48, bias 0x100000, execute-only code with the 7 accepted narrow+scalar bytes,
writable data), two Hw register steps from real file bytes, owner-only
forwarding of byte 42, drain changing shared loaded memory 0 to 42 observed
from both cores, data-section refusal beside it. Non-degenerate: two cores,
memory-changing reached run.

## Exact names of new definitions/theorems

Defs: `hwBildSpeicherGleich`, `hwBildKernGleich`, `adapterBild`,
`hwBildDatei`, `hwBildCode`, `hwBildDaten`, `hwBild`, `hwBildKern`,
`hwBildStart`, `hwBildO1`, `hwBildO2`, `hwBildAdr`, `hwBildM2`,
`hwBildTso1`, `hwBildLoadEigen`, `hwBildLoadFremd`, `hwBildTso2`,
`hwBildNachFlush`, `hwBildFremdNachFlush`, `hwBildWx`.
Theorems: `hwBild_zustand_gleich`, `hwBild_geholt_gleich`,
`hwBild_fetchDekodiert_gleich`, `hwBild_byteschritt_gleich`,
`decodeExt_pilot_zeigt_decode`, `decodeExt_narrow_zeigt_decode_none`,
`hwBild_fetchExt_pilot`, `hwBild_reg_pilot_ist_byteschritt`,
`hwBild_erweitert_ohne_pilot`, `hwBild_geholt_aus_datei`,
`hwBild_schritt_wf`, `hwBild_ohne_exec_verweigert`,
`adapterBild_vereinbarung`, `adapterBild_verweigert`,
`adapterBild_halt_verweigert`, `hwBild_wohlgeformt`, `hwBildStart_wf`,
`hwBild_o1_rip`, `hwBild_o1_rax`, `hwBild_o2_rip`, `hwBild_o2_xmm`,
`hwBild_anfang_null`, `hwBild_datei_vorne`, `hwBild_weiterleitung`,
`hwBild_fremd_alt`, `hwBild_spuelung_aendert_speicher`, `hwBild_fremd_neu`,
`hwBild_kern1_verweigert`, `hwBildWx_verweigert`, `hwBild_zeuge`.

## Last build result

`./lean-probe grammatik/Grammatik/X86/HwLoadedImage.lean`: 0 errors; all 30
`#print axioms` within standard (`propext`, `Quot.sound`).
`./lean-bau`: Build completed successfully (601 jobs).
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grep clean; two
"admit" substring hits are the English word "admits" in comments).

## What remains open

- Per-family obstruction lemmas for the other six extension families
  (muldiv, shift, setcc, cmov, fp, vec) share the dispatch shape but are not
  stated; only narrow is pinned.
- No per-access target-to-W/GX simulation, no whole-word atomicity beyond
  the reused guard, no source/IR/ABI/entry/budget link, no LOCK path.
- No hardware correspondence beyond self-consistency is claimed.

## Task remarks

The MECHANISM paragraph asks for a family event type plus adapter with a
two-core memory-touching witness; this lane's "family" is the loaded-image
fetch itself, so the adapter reuses the accepted ext-instruction plug and the
memory-touching witness runs through the TSO issue/drain path rather than a
new event type. I believe this is the honest reading; a separate event type
would duplicate `adapterInteger666`. The INHABITATION rule's syntax-premise
clause does not trigger (no premise quantifies over `Vertrag`/`Stmt`/etc.,
no `ZEUGE:` targets in the task), but `hwBild_zeuge` joins all premises
jointly on a non-degenerate run anyway.
