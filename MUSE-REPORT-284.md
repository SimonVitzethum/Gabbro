# MUSE-REPORT-284: Executable target TSO over real byte memory

Lane 284, `grammatik/Grammatik/X86/TSO.lean` (new, ~640 lines) plus one
additive umbrella import (`import Grammatik.X86.TSO` at the end of
`grammatik/Grammatik.lean`). Nothing else touched: no canonical
Typen/Speicher/goal/Spec edits, no Rust, no diagnostic/gift/example/CLI
numbers, no MARKE_EMIT. Model: opencode-go/muse-spark-1.3-contributor,
no delegation.

## What was built

Byte-granularity x86-TSO over the SAME canonical `Speicher` of
`Grammatik.X86.Typen` (not a second memory model):

- State `TSOZustand`: canonical `mem : Speicher` plus `puffer :
  Nat -> List TSOEintrag` (one FIFO per core, oldest-first; entry =
  address + byte).
- Ops: `issueByte` (needs `schreibbar`, appends youngest-last, memory
  unchanged; `none` = refused), `neuestens`/`loadByte` (youngest
  own-buffer entry wins, else canonical memory; `none` = unreadable),
  `flushKern` (oldest entry writes its byte into canonical memory;
  `none` = empty), `zaunBereit` (fence ready iff own buffer empty;
  gates only, changes no state).
- Steps `TSOSchritt` (issue | flush of any core) and `TSOErreichbar`.

## Proved (all `./lean-probe` green per increment, full `./lean-bau` green)

- Preservation/frame/isolation: `issue_erhaelt_berechtigungen`,
  `flush_erhaelt_berechtigungen`, `issue_anderer_kern`,
  `flush_anderer_kern`, `issue_kein_speicher`, `flush_schreibt_kopf`,
  `flush_rahmen`.
- Refusals: `issue_verweigert`, `load_verweigert`, `flush_leer`.
- Forwarding/FIFO: `neuestens_angehaengt`,
  `neuestens_angehaengt_anders`, `load_nach_issue`,
  `load_ohne_eintrag`, `issue_haengt_an`, `flush_entfernt_kopf`,
  `fifo_reihenfolge`.
- Drain/fence locality: `zaunBereit_iff_leer`, `zaun_nach_flush`,
  `zaun_fremd_issue`, `zaun_fremd_flush`, and `zaun_kein_fremd_drain`
  (core 0 fence-ready while core 1 holds a store: a local fence never
  drains foreign buffers).
- Reached memory-changing witness `tso_store_buffering`: from `sbStart`
  (zeroed `zeugenSpeicher`, empty buffers) two issue steps reach
  `sbNach2` where both cores load `0` for the other's address
  (`sb_beide_laden_null`, both sides `decide`), and `flushKern` on core 0
  observably changes the canonical byte (`sb_flush_aendert_speicher`).
  Step equations (`sb_schritt1`, `sb_schritt2`, `sb_flush_schritt`) hold
  by `rfl`.
- Packet scope: `paketAtomarMoeglich` predicate (widths 1/2/4/8, aligned),
  `paket_ein_byte`, `einzelbyte_atomar` (one-byte flush touches exactly
  one address), `paket_reisst` (two-byte issue + one flush leaves a mixed
  state: NO multi-byte atomicity at this layer, even aligned).
  `LockSchritt` is an empty inductive with `kein_lock_schritt`: LOCK RMW
  has no transition here (refused/OPEN).
- View-model link at bytes (no source carrier mapping invented):
  `tso_last_lesbar` (every byte `loadByte` returns is a `Lesbar` option
  of the existing `Sicht` model at `Ort := Adresse, Wert := Byte`, via
  singleton history `tsoEineHist` and `tsoEineHist_mem/_lesbar`) and
  `tso_frisch_beispiel` (the `Frisch` shape is inhabited).

Axioms: every theorem depends on nothing or on `[propext]` only (see
per-theorem `#print axioms` at the file end); no `sorry`/`admit`/
`axiom`/`native_decide`/`unsafe`; no `Prop`-typed premise; every
premise is used. No theorem quantifies over source syntax, so no
`_zeuge` obligation arises; the concrete SB witness is the boundary and
memory probe.

## Last full build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (369 jobs).` (7 lane commits on branch
`muse/284`, latest `fd5d3788`.)

## What remains open (also in the file's CUTS block)

1. Aligned 2/4/8-byte single-copy atomicity and LOCK RMW lowering
   (incl. the `rmw`-field correspondence) -- wave-B bridge work.
2. The cross-granularity refinement byte-TSO to carrier W (`SchrittW`
   `wahl`/`neu` per G-step access list, O-access) -- stated OPEN, not
   assumed; `tso_last_lesbar` is target-side only.
3. Run induction x86 traces to W runs, lowering map, per-access
   linearisation, OBS-5 publication/foreign-footprint sorting,
   handler-entry drains, MMIO/DMA exclusion, fairness/progress/timing
   transfer -- all OPEN, none claimed.

## Task remarks

Nothing in the task turned out to be wrong. One scoping note: the task
asks to "show generic forwarding/FIFO/drain facts plus concrete reached
memory-changing store-buffering witness" -- all present (`load_nach_issue`,
`fifo_reihenfolge`, `zaun_nach_flush`, `tso_store_buffering`). The "one
actual link to Sicht/W" is `tso_last_lesbar`/`tso_frisch_beispiel`
(deliberately byte-instantiated, not carrier-mapped); the precise OPEN
cross-granularity obligation is recorded in CUTS rather than simulated.
