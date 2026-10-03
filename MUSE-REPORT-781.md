# Muse Report 781 — SFENCE store narrowness

Lane 781, clone `/home/simon/Dokumente/gabbro-muse/a781`, branch `muse/781`.
Owned files only: `grammatik/Grammatik/X86/SfenceStoreNarrow.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

Proved the narrower SFENCE store-ordering fence, distinct from MFENCE, as a new
Lean module `Grammatik.X86.SfenceStoreNarrow` (~670 lines), grounded in the
official local snapshot (Intel SDM 325462-093US Sep 2026,
`.tmp/HARDWARE-REFERENCES/REFERENCES.json`):
SFENCE entry Vol. 2B 4-628 (txt lines 94415–94451: opcode `NP 0F AE F8`,
Op/En ZO, r/m field ignored so `0F AE Fx, x in 8-F`, Operation
`Wait_On_Following_Stores_Until`, #UD iff CPUID.01H:EDX.SSE[25] = 0 or LOCK
prefix) and Vol. 1 §10.4.6.4 (txt lines 15087–15092, store-only fence).

- §1 codec: `decodeSfence` takes the bare `0F AE F8..FF` row (`ok`, len 3)
  and LOCK before it (`ud .lockAufZaun`, len 4, disjoint from the accepted
  LOCK-fence arm which needs reg field 6). Proved: `roundtrip_sfence`,
  `decodeSfence_ignoriert_rm` (all of F9..FF; F8 by the roundtrip),
  `pin_sfence_lock_ud`, `pin_sfence_verweigert_nachbarn` (MFENCE row,
  LFENCE row, CLFLUSH memory shape, LOCK+MFENCE, truncations, wrong opcode),
  `pin_sfence_ext_verweigert` (`decodeExt` refuses the SFENCE bytes).
- §2 ordering vocabulary: `sfenceOrdnet` orders exactly store→store
  (`sfence_ordnet_schreibe`); no load pair is ordered
  (`sfence_ordnet_last_nicht`) — the clause MFENCE does not share.
- §3 execution over the reused `LockMaschine`: `sfenceSchritt` with the named
  silicon SSE premise (`sse : Bool`). Proved: `sfence_erfolg` (fence-only,
  RIP+3), `sfence_ohne_sse` (manual #UD), `sfence_puffer_verweigert` (the
  exact admitted elimination premise: non-empty own buffer refuses, never
  silently skips), `sfence_ud`, `sfence_erfolg_form` (success inversion),
  `sfence_behaelt_tso` (TSO-observably the identity), register/flags/load
  frames, `sfence_mfence_gleiches_tor` (adapter to accepted `lockSchritt`).
- §4 fetched layer: `decodeSfenceExt` (accepted `decodeExt` first, never
  shadowed; `decodeSfenceExt_aelter`/`_sfence`), `sfenceFetch` (canonical
  `geholt` window, 3-byte length, `ausfuehrbarN`), `sfenceByteschritt` with
  fetch-to-step laws, and the proved gate narrowness
  `sfence_schmaler_als_mfence_gate` (SSE present, SSE2 absent: SFENCE
  succeeds where accepted `lockSchrittVoll_mfence_ohne_sse2` raises #UD).
- §5/§6 witnesses + TARGET: `tsoErreichbar_trans`,
  `drainKernN_erreichbar`, fetched pins (`sfZeug_ok`, `sfZeug_ohne_sse_ud`,
  `sfZeug_puffer_verweigert`, `sfZeug_mfence_ohne_sse2_ud`), TARGET
  `SfenceStoreNarrow_verbindung` with companion
  `SfenceStoreNarrow_verbindung_zeuge` (jointly inhabited on the
  non-degenerate two-core run fdS2→fdS3: reached, memory-changing drain,
  fence machine over the drained state, silicon SSE).

## Verification

- `./lean-probe grammatik/Grammatik/X86/SfenceStoreNarrow.lean`:
  `== 0 error(s)`, axioms per theorem are `[propext]`, `[propext,
  Quot.sound]`, or none — all within the standard set, no
  `sorry/admit/axiom/native_decide/unsafe`.
- `./lean-bau`: `Build completed successfully (485 jobs)` — whole project green.
- Scratch probe `#print axioms gabbro_ziel`: exactly
  `[propext, Classical.choice, Quot.sound]` — standard, unchanged.
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

## What remains open (see CUTS in the file)

WC/NT non-temporal store paths (canonical TSO has none), serializing
instructions as ordering partners, interrupts/devices/timing/fairness, and any
source W/GX transfer — all explicitly refused or marked OPEN, none claimed.
The SSE premise is a named silicon assumption, never probed.

## Task remarks

Nothing in the task was wrong. The elimination premise the task asked for is
`sfence_puffer_verweigert`/`sfence_behaelt_tso`: elimination admitted exactly
over an empty own buffer, refused otherwise.
