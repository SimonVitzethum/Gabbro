# MUSE-REPORT-562: Narrow operations byte decoder and execution connection

## Task
Lane 562: give accepted NarrowOps forms a real byte-facing connection —
bounded independent extension decoder + canonical encoder with pinned bytes,
generic extension roundtrip, arbitrary-input decode consumption, width-exact
execution/frame facts by reuse of the accepted narrow evaluator, refusals,
pilot reuse unchanged with dispatch disjointness. No full-family claim.

## What was done
New file `grammatik/Grammatik/X86/NarrowCodec.lean` (+1 additive umbrella
import in `grammatik/Grammatik.lean`). Exactly four narrow rows are covered:
`mov32rr` (opcode 89, mod=3, no REX.W), `movzx8`/`movsx8` (0F B6/BE, mod=3,
no REX.W), `store32` (opcode 89, mod=2 + disp32 [+SIB], no REX.W). Every form
carries a canonical REX byte with W=0/X=0 (values 40/41/44/45); REX.W=1 stays
the pilot's domain, REX.X=1 refuses everywhere. Pilot `decode`/`schritt` are
untouched; dispatch is canonical-first mirroring `decodeErw`; execution reuses
`moveNarrow`/`extendNarrow`/`mergeRegNarrow`/`storeNarrow` on the same
`Zustand`. No hardware correspondence is claimed (canonical-subset
self-consistency only).

New definitions: `NarrowOp`, `NarrowDec`, `rexNarrow`, `rexNarrowBits`,
`encodeNarrow`, `narrowLen`, `decodeNarrowStore`, `decodeNarrow89`,
`decodeNarrow0F`, `decodeNarrowTail`, `decodeNarrow`, `decodeCombo`,
`stepNarrow`, `narrowDecktAb`, `narrowWitReg`, `narrowWitState`,
`narrowWitExtReg`, `narrowWitExtState`, `narrowOhneSchreib`,
`narrowWitKeinSchreib`.

New theorems (all green, axioms within propext/Classical.choice/Quot.sound):
encoder/REX: `encodeNarrow_len`, `rexNarrowBits_rexNarrow`;
roundtrip: `roundtrip_mov32rr`, `roundtrip_movzx8`, `roundtrip_movsx8`,
`roundtrip_store32`, `roundtripNarrow`, `roundtripNarrow_len_ok`;
arbitrary-input coverage (decoder side only, mirroring DecodingCoverage):
`decodeNarrowStore_abdeckung`, `decodeNarrow89_abdeckung`,
`decodeNarrow0F_abdeckung`, `decodeNarrowTail_abdeckung`,
`decodeNarrow_abdeckung`, `decodeNarrow_consumes`;
pins: `pin_mov32_eax_ecx`(+dekode), `pin_movzx_eax_cl`(+dekode),
`pin_movsx_eax_cl`, `pin_mov32_r9_r15`(+dekode), `pin_store32_rsp`(+dekode);
refusals: `narrow_nichts_leer/rex_allein/bewegung_kurz/add_opcode/
sechzehn_erweiterung/rex_w/rex_x/modus_null/sib_falsch/speicher_kurz/
erweiterung_speicher`;
dispatch: `narrow_pilot_verweigert` (pilot refuses every covered encoding),
`decodeCombo_kanonisch/erweitert/nichts`;
execution: `stepNarrow_mov32/movzx8/movsx8/store_erfolg/store_verweigert/
laenge_verweigert`, frames `stepNarrow_mov32_rahmen/movzx8_rahmen/
movsx8_rahmen/store_rahmen/store_flags`;
witnesses: `narrow_store_witness` (memory byte 0->4, RIP 4096->4103),
`narrow_movzx_witness`, `narrow_movsx_witness`, `narrow_mov32_witness`,
`narrow_schritt_laenge_null`, `narrow_schritt_speicher_verweigert`.

## Verification
- `./lean-probe grammatik/Grammatik/X86/NarrowCodec.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (428 jobs).`
- No `sorry/admit/axiom/native_decide/unsafe`; every premise is used.
- No INHABITATION `_zeuge` needed: no premise quantifies over program
  syntax and the task names no `ZEUGE:` target.

## Open / not claimed (see CUTS)
16-bit extensions (183/191 refuse loudly), narrow loads, narrow ALU forms;
`Byteschritt` fetch still uses pilot `decode` only; no source/TSO/ABI/image/
entry/cost/termination claim; `none` is absence of transition, never halt.

## Producer/consumer interface and next integration
Producers reused unchanged: Typen, Wort, Speicher, Ausfuehrung, Codec,
DecodingCoverage.parseLe32_suffix, NarrowOps, pilot decode.
Consumers: `decodeCombo`/`decodeNarrow_abdeckung`/`stepNarrow_*` are ready for
(1) the Typen/Bild owner to route `fetchDekodiert` through `decodeCombo`,
(2) validator skeleton `ErwDec.ext := decodeNarrow`-style instantiation
(proved no-shadowing via `narrow_pilot_verweigert`), (3) one row at a time
for 16-bit/load extensions. Measurable next step: a `fetchDekodiert`-over-
`decodeCombo` theorem reusing `kanonisch_schritt_ueberein` shape for the four
rows.

## Task remarks
Nothing in the task was technically wrong. Two findings worth recording:
(1) the toolchain struct-update parser rejects a newline after a field comma
(known Ausfuehrung quirk) — worked around with single-line updates;
(2) the b32 destination merge truncates sign extension to 32 bits
(`movsx8 0x80` yields `0xFFFFFF80`, not the 64-bit sign extension) — the
witness pins the actual composed behaviour, which is the architecturally
correct MOVSX r32 form.
