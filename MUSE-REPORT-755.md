# Muse Report 755: Hardware completion — pure LEA address arithmetic

## Clone / branch

- Clone: `/home/simon/Dokumente/gabbro-muse/a755`, branch `muse/755` (verified).
- Owned files only: `grammatik/Grammatik/X86/LeaPureForm.lean` (new),
  `grammatik/Grammatik.lean` (one import line appended),
  `MUSE-REPORT-755.md` (this file).

## What was done

New module `Grammatik.X86.LeaPureForm` (thin connection, nothing redefined):
reuses canonical `Zustand`/`AdrForm`/`adrEff`/`decodeLea`/`leaFormSchritt`/
`leaGeholtSchritt`/`leaWitZustand`/`storeWitZustand`/`storeWit_zeuge`/
`leaWit_rechnet` from accepted `AddressEncoding`, `dispWort` pins from
accepted `EffectiveAddress`, `geholt` from `Byteschritt`, and the common
dispatcher `decodeExt` from accepted `ExtendedExecution`.

Definitions:

- `leaDispOk (neg : Bool) (m : Nat) : Bool` — source-level
  displacement-fits-i32 side condition (signed 32-bit range).
- `leaDispWert (neg : Bool) (m : Nat) : Option (BitVec 32)` — admitted
  two's-complement word, `none` out of range.

Theorems:

- Admission pins: `leaDisp_negEins`, `leaDisp_maxPos`, `leaDisp_minNeg`.
- Refusals: `leaDisp_zuGross`, `leaDisp_negZuGross`, `leaDisp_negNull`.
- Bridges to canonical sign extension: `leaDispWort_negEins`,
  `leaDispWort_maxPos`, `leaDispWort_minNeg` (reuse `EffectiveAddress` pins).
- Fetched bytes: `leaGeholt_dekodiert` (witness window decodes as the
  scaled-index LEA form), `leaGeholt_laenge` (five checked bytes).
- Common dispatcher: `leaGemeinsam_verweigert` (`decodeExt` refuses the LEA
  bytes — no shadowing; LEA executes only through the accepted fetched
  LEA step).
- TARGET `LeaPureForm_verbindung`: a LEA decoded from actual executable
  memory runs the pure address write — destination holds `adrEff`, flags
  and memory untouched (no memory event), RIP advanced past consumed bytes.
- Companion `LeaPureForm_verbindung_zeuge`: both premises jointly on
  `leaWitZustand`, reached LEA computing `8205` into `rax`, beside the
  accepted scaled store changing data memory `0 -> 42` at `8200`
  (non-degenerate memory-changing run).

Provenance: Intel SDM combined vols 1-4, ed. 325462-093US, Sept 2026
(clone-local `.tmp/HARDWARE-REFERENCES/REFERENCES.json`, verified
2026-10-02); entry LEA - Load Effective Address (Vol. 2): computes the
effective address into the destination, reads no memory, changes no flags.
Cited by entry name/volume/edition; no line numbers claimed (the 26 MB text
snapshot was not searched), no silicon/vendor claim.

## Verification

- `./lean-probe grammatik/Grammatik/X86/LeaPureForm.lean`:
  `== 0 error(s) in the COMPLETE output` (incremental after every edit).
- `./lean-bau`: `Build completed successfully (483 jobs).`
  `LeaPureForm` built, root `Grammatik` built.
- Axioms (all ⊆ goal standard): pins depend on none; `leaGeholt_dekodiert`
  and `leaGemeinsam_verweigert` on `[propext]`; bridges, `LeaPureForm_verbindung`
  and `_zeuge` on `[propext, Quot.sound]`. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`; every premise used.
- `Zielsatz`/`Spec`/checker/emitter untouched, so `gabbro_ziel` is unaffected;
  no diagnostic/gift/example/CLI numbers, no `MARKE_EMIT` changes.

## Open / not claimed (see CUTS in file)

No silicon correspondence beyond the named manual entry; no new codec rows;
no TSO/GX bridge (LEA has no footprint); no source/ABI/loader/budget claim.

## Task remark

The ZEUGE target asked for a "memory-changing reached run" for an
instruction that is pure by definition (no memory event). The companion
therefore pairs the reached pure LEA with the accepted memory-changing
scaled-store run beside it; if the gate requires the memory change to come
from the LEA step itself, that premise is contradictory and this pairing is
the honest resolution.
