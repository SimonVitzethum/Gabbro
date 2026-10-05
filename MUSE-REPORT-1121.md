# MUSE-REPORT-1121: Addressed loads/stores of all widths through TSO

## Task
Lane 1121: connect the addressed (base+index*scale+disp, SIB) family to the
coherent machine (`HwMaschine`/`HwSchritt`), reusing the accepted definitions
unchanged. Events for loads/stores of 1/2/4/8 bytes with SIB addresses through
`issueByte`/`loadByte` with forwarding, partial overlap with pending stores,
and the existing tearing refusals.

## What was done
NEW FILE `grammatik/Grammatik/X86/HwAddressed.lean` (+ one import line appended
to `grammatik/Grammatik.lean`). Lifts, never redefines:

- Addresses: `hwAddrOf` = accepted `adrEff` on the acting core's pre-state
  registers plus the next-RIP base (`hwAddrOf_basisForm`: on `basisForm` it IS
  the accepted pilot `effAddr`).
- Stores: `hwAddrStore` issues the pre-state source register's low bytes
  width-selected (`entriesOf`/`concIssue` on the shared TSO view, never the SC
  word effect); RIP advances, flags/registers/memory discipline proved
  (`hwAddrStore_flags/rip/puffer/kein_speicher/wf`).
- Loads: `hwAddrLoad` reads through accepted `concLoad` (youngest-own
  forwarding) and merges with `mergeRegNarrow` (`hwAddrLoad_dst/wf`).
- Agreement: `hwAddrStore_basisForm` / `hwAddrLoad_basisForm` — on
  base-plus-disp32 forms the addressed steps ARE the accepted
  `concStoreMaschine`/`concLoadMaschine`; `hwAddrWeiterleitung` — whole-access
  forwarding is the accepted read-after-write value at every width.
- Adapter: `HwAddrEreignis` (store/load/verweigert) with `adapterAddr :
  HwAdapter HwAddrEreignis` reusing the addressed evaluators;
  `adapterAddr_verweigert/store`.
- Refusals: bad length (both directions), refused gate (both directions),
  tearing (`hwAddrTeil_keine_gruppe` via `hwTeilwort_keine_gruppe`) and overlap
  (`hwAddrOverlap_keine_gruppe` via `hwGruppe_verweigert_bei_fremdeintrag`).
- Witness `hwAddrWit_zeuge`: reached two-core run — 32-bit store through the
  SIB form `rbx + rcx*8 + disp8(0) = 8200`, 4 buffer entries, RIP 4096 -> 4103,
  owner-only forwarding (core 0 reads the value, core 1 reads 0), 4-flush drain
  (byte 0 becomes `0x04`, both cores observe the value), beside tearing (4 of 8
  bytes) and overlap refusals and `HwWf`. Non-degenerate: the drain observably
  changes shared memory; the buffered store is visible to the owner only.

## Verification
- `./lean-probe grammatik/Grammatik/X86/HwAddressed.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (601 jobs)`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. `#print axioms` per main
  theorem: `[propext, Quot.sound]` throughout (subset of the standard
  `propext, Classical.choice, Quot.sound`; two guard-lift theorems depend on no
  axioms at all). No premise has type `Prop`; every premise is used.
- Inhabitation: no theorem quantifies over program syntax
  (`Vertrag`/`Stmt`/etc.), so rule 13 needs no syntax witnesses; the joint
  reached non-degenerate witness is `hwAddrWit_zeuge` (two cores, SIB address,
  memory-changing drain, owner-only forwarding).

## Open / not claimed
- No silicon correspondence: addresses and byte shapes are the accepted
  canonical subsets with self-consistency only; no SDM heading is cited as
  proof (earlier MUSE-REPORT-660 provenance is not re-claimed here).
- No byte-codec round trip for addressed forms here: fetch/decode stays with
  the accepted producers (`decodeLockAdr`, `decodeLea`, `decodeStoreIdx`,
  `concDecode`); this module takes decoded `AdrForm` values.
- No LOCK/RMW path, no faults beyond the carried gate refusals, no
  per-access target-to-W/GX simulation, no whole-word atomicity beyond
  `WortGruppe`-guarded byte drains, no source/ABI/loader/entry/budget claim.
  See the file's CUTS block.
- Note for the merger: the file uses `decide` for closed witness pins in the
  style of the accepted family modules; build cost is small (module builds in
  seconds inside the 601-job build).

## Owned files touched
- `grammatik/Grammatik/X86/HwAddressed.lean` (new)
- `grammatik/Grammatik.lean` (one import line appended)
- `MUSE-REPORT-1121.md` (this file)
