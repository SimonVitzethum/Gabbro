# Muse Report 664: efficient full selected address encodings

## What was done

New module `grammatik/Grammatik/X86/AddressEncoding.lean` (~1190 lines)
plus one additive umbrella import in `grammatik/Grammatik.lean`.
It implements the §2B address scope of `DIRECT-COMPILER-DESIGN.md`
(disp0/disp8/disp32 smallest-first, base+index*scale+disp with REX high
registers, absent base/index, RIP-relative, LEA purity) over the
canonical `Register`/`Adresse`/`Wort`/`Speicher` vocabulary, reusing the
accepted `Codec` (reg codes, REX shape, LE bytes), `Ausfuehrung`
(`dispWort`, `effAddr`, `schritt` helpers, witness state),
`Byteschritt` (fetched window, execute-only fetch), `Speicher`
(`read64`/`write64`, `OhneUmbruch`, footprints) and `ControlFlow`
(pilot LEA) modules. No existing file was changed except the umbrella
import; no pilot row was re-decided.

Exact deliverables (definitions):
`disp8Wort`, `skalaOk`, `skalaCode`, `codeSkala`, `kanonisch48`,
`DispArt`, `dispLaenge`, `AdrForm`, `u8Nach32`, `adrOk`,
`basisForm`, `basisDisp8Form`, `basisKeinForm`, `skaliertForm`,
`ripForm`, `absolutForm`, `indexForm`, `dispWortArt`, `adrEff`,
`leaFormSchritt` (named to avoid the accepted `ControlFlow.leaSchritt`),
`rexAddr`, `modrmByte`, `sibByte`, `rexFuer`, `encodeAdr`,
`passtIn8`, `kompaktArt`, `sibReg`, `parseAdrTail`, `decodeLea`
(opcode 0x8D), `decodeStoreIdx` (opcode 0x89), `leaGeholtSchritt`,
`adrStoreSchritt`, `fussZugelassen`, plus closed witness states
`leaWitZustand` (LEA `rax <- rbx + rcx*8 + 5 = 8205`) and
`storeWitZustand` (high-register scaled store through `r8 + r9*8`).

Exact deliverables (theorems, selection): sign-extension pins
(`disp8Wort_negEins/maxPos/minNeg`, `dispWortArt_d8`,
`disp8_d32_gleich_negEins`); scale round trip (`codeSkala_skalaCode`);
canonical-address pins (`kanonisch48_8192/hoch/loch`); admission and
refusals (`basisForm_ok`, `ripForm_ok`, `skaliertForm_rsp_verweigert`,
`basisKeinForm_rbp_verweigert`, `encodeAdr_braucht_ok`);
pilot bridge (`adrEff_basisForm`, `leaFormSchritt_basisForm` against
`ControlFlow.leaAnwenden`); prestate/relocation
(`adrEff_skaliert_prestate`, `adrEff_rip_prestate`,
`adrEff_verschiebung`); LEA purity (`leaFormSchritt_flags/speicher/
fremd/dst/laenge_verweigert`); encoder lengths pinned per shape
(2, 3, 4, 6, 7 bytes) with pilot-ownership refusals
(`encodeAdr_pilot_basis/rsp`); compact choice (`kompaktArt_klein/
gross/beispiele`, `kompakt_ersparnis`: 4 vs 7 bytes at the same
address); per-shape codec round trips (`rundweg_skaliertDisp8/
skaliertHoch/basisDisp8/basisKein/rip/absolut/indexForm/basisKein_rsp`);
non-shadowing (`parser_weist_pilot_basis/sib_zurueck`,
`pilot_weist_x/leа_zurueck`, `store_weist_pilot_basis_zurueck`);
planted refusals (`parser_verweigert_leer/mod3/ohne_sib/kurze_disp8`,
`falsche_disp8_aendert_adresse`, `lea_verweigert_vorsatz/ohne_rex`,
`store_verweigert_ohne_rex`, `adrFuss_verweigert_rand`,
`storeWit_dunkel_verweigert`); footprint admission
(`adrFuss_addrs`, `adrLesen/Schreiben_erlaubt`,
`adrStore_berechtigungen`, `bildDisp_trifft/pin_4089`,
`fussZugelassen_beispiele`); joint reached witnesses
(`leaWit_rechnet/flags/speicher_ruht/rip/nachBild_verweigert`,
`storeWit_zeuge`).

## Last build result

`./lean-probe grammatik/Grammatik/X86/AddressEncoding.lean`:
`== 0 error(s) in the COMPLETE output`.
`./lean-bau`: `Build completed successfully (460 jobs).`
`#print axioms` for every main theorem: only `propext`, `Quot.sound`
or fewer; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
Every premise of every theorem is used by its proof.

## What remains open

Documented in the file `CUTS` block: no silicon correspondence (the
clone has no `.tmp/HARDWARE-REFERENCES/REFERENCES.json`, so no manual
heading or page is cited); no generic 256-pair round trip and no
uniform length-bound theorem (each shape class pinned on closed
bytes); no base-only disp0/disp8 pilot rows (pilot keeps mod=10
disp32 per `BYTE-PILOT.md`; needs new pilot rows plus review);
width/branch/immediate forms stay with integer666/locked662/FP668
over the stable API (`adrEff`, `dispWortArt`, `encodeAdr`,
`parseAdrTail`, `decodeLea`, `decodeStoreIdx`, `leaFormSchritt`,
`leaGeholtSchritt`, `adrStoreSchritt`, `kanonisch48`,
`fussZugelassen`); no TSO/GX bridge, no source/ABI/loader claim.

## Task remarks

Two intended readings proved unworkable and were resolved honestly:
(1) the "common API for integer666/locked662/FP668" lanes do not exist
in this clone, so the module exports a named stable API for them
instead of importing it; (2) full disp32 coverage for base-only forms
belongs to the pilot by `BYTE-PILOT.md`, so disp32 in this module
appears only where the pilot has no row (RIP-relative, SIB
base-absent, scaled-index SIB); compact base-only disp0/disp8 is
booked as follow-up work rather than silently changing pilot bytes.
