# MUSE-REPORT-1307: FP store forms — drain equals the 32-bit write

Clone: `/home/simon/Dokumente/gabbro-muse/a1307`, branch `muse/1307`
(base `234f2728`; task named master `a0a8c5fe` — base moved since, no
stale-base work: all cited lemmas re-checked at the current tree).

## What was done

NEW FILE `grammatik/Grammatik/X86/HwFpStoreDrain.lean` (~1360 lines)
plus one `import Grammatik.X86.HwFpStoreDrain` line in
`grammatik/Grammatik.lean`. No existing file touched otherwise; no
model redefined — every family evaluator is lifted, never redefined.

This closes the lane-1211 (`HwFpDispatch.lean`) open item: the
drain/write32 byte correspondence for STMXCSR and MOVSS-store was
pinned at issue level only. Now proved, generically over the TSO
model and the `FpFremdFrei32` guard:

- **§1 events + adapter**: `FpStoreEreignis`
  (`speichere32`/`eigenSpuele`/`fremdSpuele`/`fremdAusgabe`/`beobachte`)
  and the `HwAdapter` plug `fpStoreAdapter` (32-bit stores buffer
  via the accepted `fpCtrlAusgabe32`, drains flush, observations are
  silent).
- **§2 adapter duties**: `fpStoreAdapter_wf` (wf preserved);
  `fpStoreSpeichere_puffer` (exactly the four canonical entries),
  `fpStoreSpeichere_kein_speicher` (no canonical byte moves),
  `fpStoreEigen_ist_flush` / `fpStoreEigen_ist_schritt` (own drain
  IS the accepted flush / a `HwSchritt.spuele` event),
  `fpStoreBeobachte_still`; refusals `fpStoreEigen_leer_verweigert`
  (via `flush_leer`), `fpStoreSpeichere_wache` (via
  `issueListe_cons_none`), `fpStoreBeobachte_dunkel` (via
  `load_verweigert`).
- **§3 4-byte drain induction** (the `HwDrainGeneric` technique for
  8 bytes, specialised to 4; `DrainSchritt`/`DrainSpur`/permission
  framing reused unchanged): `fp32Eintraege_kopf`,
  `fpFuss32_mem_offset`, `fp32_drain_installiert_aux`,
  `fp32_drain_uninstalliert_aux`, `fp32_drain_voll`,
  `fp32_lesbarN_gleich`, `fp32_drain_lesbarN_aux`,
  `fp32DrainFuss_gleich_schreibbytesN`,
  `fp32_gruppe_liest_zurueck`, and the main
  `fp32DrainGleichWrite32` (exclusion-checked four-drain agrees
  with the successful `write32` on the whole footprint and reads
  back the low 32 bits). Corollaries `fp32StDrain_gleich` (stored
  word IS lane 1211's `mxcsrSpeicherWort`, group via
  `fpDispSt_gruppe`) and `fp32MovssDrain_gleich` (stored word IS
  lane 1211's `setWidth 64 (xmmTief32 f src)`, group via the
  accepted `fpCtrlAusgabe32_gruppe`).
- **§4 forwarding**: `fp32Weiterleitung_eigen` (owner observes all
  four stored bytes; lifts the accepted `fpCtrlWeiterleitung32`
  through the adapter), `fp32Leer_liest_speicher` (empty buffer
  reads canonical memory — no foreign forwarding).
- **§5 tearing refusals**: partial buffers stay refused (accepted
  `fpGruppe32_teilwort`), foreign entries stay refused (accepted
  `fpGruppe32_fremd`), plus the NEW `fp32KreuztGruppe_kein_gruppe`:
  a 4-byte store sharing a byte with an in-flight foreign 8-byte
  `WortGruppe` crosses that group's boundary and tears (structural
  overlap, not an alignment gate — the byte drain never consults
  alignment, recorded in CUTS).
- **§§6–8 joint witness** `fp32StoreDrain_zeuge` (non-degenerate,
  two cores): adapter push of `3.0f32` (`0x40400000`) buffers
  exactly 4 entries with owner-only forwarding over unchanged
  memory; `fp32Wit_push_gleich_start` proves the TSO drain starts
  exactly where the machine push ends (buffer + bytes, via the
  generic §2 facts); the four-drain installs the accepted
  `write32` footprint with read-back (`fp32Wit_feuer` fires the
  generic induction); core 1 observes the new byte; one byte
  observably changes (`0` to `0x40`); the drain is a reached TSO
  run (`drain_spur_erreichbar`); beside it a partial-buffer
  refusal, a concrete misaligned straddle at 8198 over the
  in-flight 8-byte group at 8192, and guard/dark/empty refusals.

## Checks

- `./lean-probe grammatik/Grammatik/X86/HwFpStoreDrain.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (only linter
  style warnings on induction `leer`-branch binders, same pattern
  as the accepted `drain_installiert_aux`).
- `./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed
  successfully (677 jobs)`.
- `#print axioms` for every main theorem (38 prints at file end):
  all within `[propext, Quot.sound]` — inside the standard goal
  set, no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- No `Prop`-typed premises; every theorem premise is used by its
  proof (one linter-driven cleanup: dropped an unused core
  parameter from `fp32Leer_liest_speicher`).

## What remains open / findings

- Two proof-shape findings for future lanes (both worked around,
  no weakening): (1) multi-line `{ s with f :=\n expr }` layout
  fails to parse — keep structure updates on one line; (2) `rw`
  needs syntactic (not just definitional) match for
  `tsoAnsicht`-projections — precede with `show`.
- Per the task, the full bridge to W/GX is NOT claimed (see
  CUTS); no silicon correspondence beyond self-consistency; no
  4-byte no-wrap statement (`OhneUmbruch` is 8-byte).
- Nothing in the task statement looks wrong; the "misaligned
  store crossing a group boundary" requirement is met as
  structural footprint overlap (byte drain is alignment-free by
  accepted design), documented in §5/CUTS.

## Commits on muse/1307

- `e1bb309b` skeleton; `65c86331` §2; `5fcef7b5` §3;
  `24ce9fd0` §§4–8. This report follows as the next commit.
