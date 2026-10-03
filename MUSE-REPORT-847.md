# MUSE-REPORT-847: Composition closing — mapping-permission closing

## Task
Close the final loaded mapping to per-address R/W/X bits for every executed
byte; permission-checked access composed end to end. Compose already-accepted
modules into one checked closing step; never re-prove their internals and
never duplicate an interpreter or executor. Target:
`ComposeMapPerms_verbindung` with companion
`ComposeMapPerms_verbindung_zeuge` (jointly inhabited, non-degenerate,
memory-changing reached run).

## What was done
New file `grammatik/Grammatik/X86/ComposeMapPerms.lean` (owned), plus the
one-line register import in `grammatik/Grammatik.lean` (owned). No other
file touched. No diagnostic/gift/example/CLI numbers, no MARKE changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

Producer/consumer interface closed: producers `valX86` (mapping AND decode
coverage admission), `geladen` with `ladenLesbar`/`ladenSchreibbar`/
`ladenAusfuehrbar` (loaded bytes and permissions), `fetchDekodiert`
(X-gated fetch from actual memory), `zugriff` (potential footprint) and
`schritt` (realised step) — all reused by name. Consumer: the single
checked closing step `ComposeMapPerms_verbindung`. A conjunction of checks
is not execution here: the companion shows a reached memory-changing store
step through the composed step, and three planted refusal cases are proved.

### New definitions
- `zugriffLesbar`, `zugriffSchreibbar`: per-access R/W permission checks
  over one extracted `Zugriff` (`lesen.all lesbar`, `schreiben.all schreibbar`).
- Witness vocabulary: `zeugenCode847` (canonical encoding of
  `store [rsp], rax`), `zeugenDatei847`, `zeugenCodeAbs847` (R+X),
  `zeugenDatenAbs847` (R+W, nonzero byte 9 at base), `zeugenBild847`,
  `zeugenReg847` (`rax` = 42, `rsp` = data base), `zeugenFlags847`,
  `zeugenZustand847` (entry `rip`, canonically loaded memory),
  `zeugenCodeZustand847` (`rbx` aimed at code for the refusal case).

### New theorems
- `read64_lesbar8`, `write64_schreibbar8`: successful 64-bit access
  carries its eight-byte permission check (from `read64`/`write64` defs).
- `fuss_all_lesbar`, `fuss_all_schreibbar`: eight-byte check implies the
  footprint-wide `List.all` permission.
- `ComposeMapPerms_verbindung`: for arbitrary admitted image, bias, state,
  fetch and step — mapping admission, executed prefix executable in the
  loaded mapping, extracted read/write footprints permission-checked, all
  three permission maps preserved, changed bytes inside the write footprint.
  Proved by case analysis over all 14 pilot forms reusing the accepted
  `erfolg_*`, `zugriff_*_versagt_kein_erfolg`, `schritt_pop64_speicher` and
  `fetchDekodiert_entspricht` facts; every premise is used
  (`hval` via `valX86_wohlgeformt`, `hmem` for the loaded-mapping X fact,
  `hf` for fetch correspondence, `hs` for the case analysis).
- `ComposeMapPerms_verbindung_zeuge`: joint companion — acceptance, loaded
  memory, fetch, successful step and an observable byte change (9 to 42 at
  the data base) on the non-degenerate two-section witness, plus changed
  byte membership in the extracted write footprint via the main theorem.
- Observations: `zeugenBild847_akzeptiert`, `zeugenFetch847`,
  `zeugenSchritt847`, `zeugenAlt847` (all `by decide`).
- Planted refusals: `zeugenSpeicherCode847_verweigert` (store into code has
  no transition), `zeugenFetchDaten847_verweigert` (fetch from
  non-executable data refuses), `zeugenWx847_verweigert` (W^X image refused).

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeMapPerms.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: whole project green; last result line:
  `Build completed successfully (509 jobs).`
- Axioms: `ComposeMapPerms_verbindung` and `_zeuge` depend on
  `[propext, Quot.sound]` only (subset of standard; no `sorry`/`admit`/
  `axiom`/`native_decide`/`unsafe` anywhere in the file). `grammatik/`
  otherwise untouched, so `gabbro_ziel` axioms are unaffected.

## What remains open (explicit CUTS in the file)
Source correspondence, the per-access target-to-W/GX simulation, any
silicon/hardware claim, extended forms beyond the 14 pilot constructors,
standalone arbitrary-input decoder length soundness, and entry/budget-stop
connections stay with their wave owners; they are listed as CUTS, never
assumed. Only the connection-wave producer legs actually consumed here
(mapping, X-gated fetch, footprints, validator skeleton) are composed.

## Remarks on the task
Nothing in the task was wrong. Two elaboration notes for future lanes:
`cases h : e with` is rejected by this toolchain (used `generalize` +
plain `cases`), and tactic blocks after a tuple `refine` apply to the
first goal only (each branch proves its full conjunction with one
`exact`). A bare `?` is not hole syntax; `?_` is.
