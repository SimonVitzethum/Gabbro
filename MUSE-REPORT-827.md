# MUSE-REPORT-827: Composition closing — entry-to-mapping closing

## Task
Close entry predicates with the actual loaded mapping: entry RIP is a decoded
start with checked permissions; otherwise refuse. Compose already-accepted
modules, never re-prove their internals, never duplicate an interpreter or
executor. Target: `ComposeEntryMap_verbindung` with companion
`ComposeEntryMap_verbindung_zeuge` (jointly inhabited, non-degenerate,
memory-changing reached run).

## What was done
New file `grammatik/Grammatik/X86/ComposeEntryMap.lean` (+1 import line in
`grammatik/Grammatik.lean`), reusing accepted definitions by name only:
`EntryExecution.eintrittZulassung` (+ witnesses `zeugenEintrittAusf`,
`zulassungSpeicher`, facts `zulassung_rip_ausfuehrbar`,
`zulassung_verweigert_unlisted/tor`, `zulassung_fetch_ret`,
`zulassung_schritt_ret`), `ValidatorSkeleton.valX86` (+ `valZeuge`,
`valWx`, `valX86_wohlgeformt`), `Byteschritt.fetchDekodiert`/`byteschritt`/
`byteschritt_weiter`, `Ausfuehrung.schritt`/`schritt_ret_erfolg`,
`ContractSites.vertragStandort_lauf_zeuge`, `Speicher.write_read_zeuge`.

Closed producer/consumer interface: producers `Bild.wohlgeformt`/`geladen`
(checked loaded mapping), `EntryState.eintrittOk` (listed executable entry,
stack, guard, MXCSR, IF), `valX86` (mapping AND whole-image decode coverage)
with `valTore`, `fetchDekodiert` (entry RIP as actual decoded start in
executable memory); consumer `byteschritt` (the composed step runs).

### New definitions/theorems (exact names)
- `composeEntryMap` — closed admission: `eintrittZulassung && valX86 &&
  (fetchDekodiert ..).isSome` (Bool, never a fault claim)
- `composeEntryMap_zulassung`, `composeEntryMap_skelett`,
  `composeEntryMap_startDekodiert`, `composeEntryMap_wohlgeformt`,
  `composeEntryMap_rip_ausfuehrbar` (RIP executable through CHECKED
  `geladen` mapping)
- `ComposeEntryMap_verbindung` (TARGET): from closed admission + fetched
  `(d, rest)` + successful `schritt`: checked-mapping executability AND
  `byteschritt = .weiter s'`, generic over arbitrary admitted inputs
- `composeEntryMap_verweigert_unlisted`, `composeEntryMap_verweigert_tor`,
  `composeEntryMap_verweigert_ohne_start` (generic refusals, each premise used)
- `composeEntryMap_zeuge_ok` (acceptance, `decide`)
- `composeEntryMap_fremd_verweigert`, `composeEntryMap_abi_verweigert`,
  `composeEntryMap_wx_verweigert` (planted `decide` refusals)
- `zeugenEintrittOhneAusfuehrbar` + `zeugenOhneAusfuehrbar_zulassung` +
  `zeugenOhneAusfuehrbar_ohne_start` + `composeEntryMap_start_verweigert`:
  mapping+entry+skeleton+gate hold, yet closed entry refuses (RIP no
  decoded start in fetched memory)
- `ComposeEntryMap_verbindung_zeuge` (companion): all TARGET premises
  jointly instantiated on concrete values (`.p48`, `valZeuge`, bias 0,
  `.hostedMain`, `zeugenEintrittAusf`, `[schreibTor]`, `⟨.ret,1⟩`, `[]`,
  `schrittRet`-successor via `schritt_ret_erfolg`), TARGET conclusion
  derived through `ComposeEntryMap_verbindung` itself, plus reached
  non-degenerate run (`RufErreichbarG`, `(eD.signatur eSetze).schreibt () =
  true`, `ReqAmEintritt` at actual place), executed `ret` to RIP 0, and a
  real eight-byte memory change (`write_read_zeuge`).

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeEntryMap.lean`: 0 errors.
- `./lean-bau`: exit 0, 0 errors, `Build completed successfully (509 jobs)`.
- `#print axioms`: all `[propext]`, two with `+ Quot.sound`, the joint
  witness `[propext, Classical.choice, Quot.sound]` — all subsets of the
  standard `gabbro_ziel` set; no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe`. No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes,
  no source/checker/Spec/goal/emitter edits, no friend-reserved files.

## Open (explicit CUTS in file, owners named)
Source-to-entry lowering (shared IR lane 287, QUELLBRUECKE bridge),
per-access TSO/GX simulation (lanes 567/573-574), multi-step/relocation/
callee-template legs with their owners; no hardware, cost/time, or
termination claims.

## Task assessment
Nothing in the task appears wrong. One note: the "no second loader" and
"conjunction is not execution" requirements are met by keeping state memory
and image mapping as distinct legs — the `zeugenEintrittOhneAusfuehrbar`
refusal pins exactly their meeting point at the RIP.
