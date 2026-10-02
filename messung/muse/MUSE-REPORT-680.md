# MUSE-REPORT-680: Indirect and compact control byte forms

## Task

Lane 680 (hardware completion): indirect near CALL/JMP (`FF /2`, `FF /4`,
register + checked memory targets, REX effects) and short branches
(`EB` rel8, `70+cc` rel8) with fetched canonical execution reusing the
accepted constructors; fetched adapter for consumers 660/670; joint
reached witnesses with memory change plus malformed/fault/overlap
refusals. OWN ONLY `grammatik/Grammatik/X86/IndirectControlHardwareForms.lean`,
`grammatik/Grammatik.lean`, `MUSE-REPORT-680.md`. Verified clone
`/home/simon/Dokumente/gabbro-muse/a680`, branch `muse/680`.

## What was done

New module `grammatik/Grammatik/X86/IndirectControlHardwareForms.lean`
(1581 lines), added as additive umbrella import in `grammatik/Grammatik.lean`.
Nothing else touched. Read: `Codec`, `Ausfuehrung`, `Byteschritt`,
`ControlFlow`, `ControlCodec`, `StackExecution`, `BranchLayout`,
`EffectiveAddress`, `ExtendedExecution` (all accepted, none modified),
plus the clone-local Intel snapshot
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`.

Manual provenance recorded in the file (§0, `indirektHandbuch`):
Intel SDM 325462-093US Vol.2A Ch.3 CALL (`FF /2 r/m64`, p.3-121),
JMP (`FF /4 r/m64`, `EB cb`, pp.3-504-3-505), Jcc (`70+cc cb`,
pp.3-499/3-502), Vol.2B RET (`C3`, p.4-569), Vol.1 §6.4.1.

Definitions: `IndForm` (`callReg/callMem/jmpReg/jmpMem/jmpKurz/jccKurz`
with carried lengths), `indLen`, `dispWort8` (rel8 sign extension via
reused `sext .b8`), `kurzZiel`, canonical encoders (`encodeIndReg`,
`encodeIndMem`, `encodeJmpKurz`, `encodeJccKurz`), decoders
(`decodeIndirekt`, `decodeIndRegNach`, `decodeIndMemNach`,
`modrmFelder`), steps reusing accepted constructors
(`callRegSchritt`, `callMemSchritt`, `jmpRegSchritt`,
`jmpMemSchritt`, `jmpKurzSchritt`, `jccKurzSchritt`, `indSchritt`),
fetch/admission (`indZugelassen`, `fetchInd`, `indByteschritt`),
validator admission (`indirektZielOk`), pilot-first adapter
(`IndAdaptiert`, `indAdapterDecode`).

Main theorems: generic round trips (`roundtrip_indReg_call/jmp`,
`roundtrip_indMem_call/jmp`, `roundtrip_jmpKurz/jccKurz`); step
equations with access order (`callRegSchritt_erfolg/verweigert`,
`callMemSchritt_erfolg/lesefehler/schreibfehler`,
`jmpRegSchritt_erfolg`, `jmpMemSchritt_erfolg/verweigert`,
`jmpKurzSchritt_erfolg`, `jccKurzSchritt_genommen/nicht`); fetch
discipline (`indZugelassen_summe/laenge/ausfuehrbar`,
`fetchInd_erfolg`, `indByteschritt_weiter/verweigert`); separation of
provenance from architectural gates
(`indirektZielOk_garantiert`, `zielOhneHerkunft_fuehrt_aus`,
`daten_sprung_aber_fetch_verweigert`); pilot disjointness both ways
(`pilot_verweigert_indReg/indMem/kurz/jccKurz`,
`unser_verweigert_ret/call32/jump32`); adapter agreement
(`indAdapter_pilot/indirekt/callReg_bytes/jccKurz_bytes`); closed-byte
pins (`pin_callReg_rbx/r9(+dekode)`, `pin_jmpMem_rsp`,
`pin_jmpKurz/jccKurz_e`); decode refusals (`far_erweiterung`,
`rexR`, `rexW_auf_register`, `zaehler` (E3), `kurz/mem_abgeschnitten`,
`modus0`, `indirekt_leer`).

Joint witnesses (all from actual executable bytes, with read-back and
observed byte change): `indKette_zeuge` (fetched `CALL rbx` at 4096 →
pilot callee store at 4200 → `ret`; stack slot 0→4098, data cell 0→42,
`rsp` restored, RIP 4098, admitted target); `memCall_zeuge`
(RSP-based `callMem` reading the pre-instruction top, target 4200,
return 4104 stored); `kurz_zeuge` (taken 4114 / untaken 4098 from the
same 2 bytes + memory chain beside). Planted execution refusals:
`wache_ruf_verweigert` (guarded stack), second half of
`daten_sprung_aber_fetch_verweigert` (step executes, next fetch
refuses), `codeSchreib_ueberlappt` (code store changes the window, call
form stops fetching).

## Checks (final)

- `./lean-probe .../IndirectControlHardwareForms.lean`: `0 error(s)`.
- `./lean-bau`: `Build completed successfully (461 jobs)`, exit 0.
- Every `#print axioms` in the file is a subset of
  `[propext, Classical.choice, Quot.sound]` (no sorry/admit/axiom/
  native_decide/unsafe; no Prop-typed premises; every premise used).
- `gabbro_ziel` files untouched (`git status` shows only the two owned
  paths); goal axioms unchanged by construction.

## Open / not claimed (see CUTS)

No hardware correspondence (self-consistency only; `#GP`/`#PF` codes,
timing, caches, CET/shadow-stack unmodelled); far forms, `RET imm16`,
`JCXZ` family, LOCK, non-canonical REX refused by construction;
memory targets beyond base+disp32 (scaled SIB, RIP-relative, mod=0/1)
OPEN for consumer 664 (accepted `EffectiveAddress` used meanwhile);
no source/IR/checker/emitter/contract/ABI/loader/budget/TSO claims.

## Task remarks

- The struct-update layout parser fact (no newline after a field
  comma, noted in `Ausfuehrung.lean` CUTS) bit once; kept updates
  single-line.
- No extra premise was needed for any target-shaped statement; the
  RSP-pre-value and read-before-write orderings are proved, not
  assumed. Nothing in the task looks wrong.
