# MUSE-REPORT-746: compact zero-extending MOV reg, imm32

Lane 746, branch `muse/746`, clone `/home/simon/Dokumente/gabbro-muse/a746`.
Task: cover the no-REX.W `B8+rd imm32-LE` row with upper-half zeroing
semantics, width-exact lemma, destination-dead proof obligation, pinned
bytes, and refusal of values needing imm64.

## What was done

New file `grammatik/Grammatik/X86/CompactImmMov32Zero.lean` (~915 lines,
73 definitions/theorems), plus one import line in
`grammatik/Grammatik.lean`. Nothing else touched: no diagnostic/gift/
example/CLI numbers, no MARKE changes, no source/checker/Spec/goal/
emitter edits, no friend-reserved optimiser files.

The one covered row is `B8+rd id` (MOV r32, imm32): bare opcode for low
registers (5 bytes), one `0x41` REX.B byte for r8-r15 (6 bytes). Value
semantics reuses canonical `Wort.trunc (.b32)`; the step follows the
accepted `NarrowOps.mergeRegNarrow` 32-bit clearing discipline and the
`Ausfuehrung` register-file helpers on the same `Zustand`. Fetch and
byte-step mirror the `fetchDekodiert` discipline over actual executable
memory (`Byteschritt.geholt`/`ausfuehrbarN`); dispatch is pilot-first
with the row taken only where the pilot refuses.

Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`,
Intel SDM 325462-093US): MOV opcode table `B8+ rd id` vs
`REX.W + B8+ rd io` (txt lines 65710-65712); operand-size rule "32-bit
operands generate a 32-bit result, zero-extended to a 64-bit result"
(Vol. 1 Table 3-2 context, txt lines 4375-4382); default 32-bit
operation size with REX.R for R8-R15 and REX.W promoting to 64 bits
(MOV Description); Flags Affected None (MOV entry).

## New definitions

`CompactImmMov32` (`.mov32imm dst imm`), `CompactDec`, `compactWert`,
`compactOpcode`, `encodeCompact`, `compactLen`, `decodeCompactTail`,
`decodeCompact`, `compactDecktAb`, `compactTailAb`, `decodeComboCompact`,
`brauchtImm64`, `stepCompact`, `compactZugelassen`, `fetchCompact`,
`CompactAusgang`, `compactByteschritt`, `kompaktWitReg`,
`kompaktWitState`.

## New theorems (selection; full list in the file's CUTS-adjacent code)

- Encoder: `encodeCompact_len`, `encodeCompact_cap`.
- Width-exact: `compactWert_nat`, `compactWert_fits`,
  `trunc_compactWert`, `compactWert_gleich_merge`,
  `compactWert_gleich_extend`.
- Codec: `roundtrip_compact_low/high`, `roundtripCompact`,
  `roundtripCompact_len_ok`, `compact_pilot_verweigert`,
  `decodeComboCompact_kanonisch/erweitert/nichts`.
- Coverage: `decodeCompactTail_abdeckung`, `compactTail_zu_Ab`,
  `decodeCompact_abdeckung`, `decodeCompact_consumes`.
- imm64 gate: `brauchtImm64_genau`, `keinKompaktFuerGross`,
  `kompaktFuerKlein`.
- Step: `compactLen_ok`, `stepCompact_mov32imm`,
  `stepCompact_laenge_verweigert`, `stepCompact_wert/fremd/flags/
  speicher/rip`, `stepCompact_gleich_merge`, `compact_dst_tot`
  (destination-dead), `stepCompact_ohne_speicher` (no memory access).
- Fetch: `compactZugelassen_summe/laenge/ausfuehrbar`,
  `fetchCompact_erfolg`, `compactByteschritt_weiter/
  schritt_verweigert/hol_verweigert`.
- Target: `CompactImmMov32Zero_verbindung` with companion
  `CompactImmMov32Zero_verbindung_zeuge` (hostile all-ones registers,
  `rax := 0x80000001`, plus the reached `lauf` run taking cell 8192
  from 0 to 42; all four premises instantiated jointly).
- Pins/refusals: `pin_mov32imm_eax_eins(_dekode)`,
  `pin_mov32imm_r15(_dekode)`, `kompakt_nichts_leer/
  abgeschnitten/rex_w/rex_leer/rex_x/unbekannt`,
  `kompakt_narrow_verweigert`, `kompakt_gross_verweigert_pin`.

Axioms: every `#print axioms` line is within
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/
`axiom`/`native_decide`/`unsafe`.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed
successfully (483 jobs)`, ending `Built Grammatik`. Whole project
green including the new module.

## What remains open (see CUTS in the file)

No hardware correspondence (self-consistency only); no other MOV rows
(`66 B8`, `C7 /0`, segment, `moffs`); shared `byteschritt`/
`extByteschritt` not rewired to this row (dispatcher owners'
integration); no #UD membership for refused neighbours; no TSO/W/GX
bridge; no source/ABI/image/entry/relocation/cost claims.

## Task feedback

Two readings of "no-REX.W" were possible (always-REX like NarrowCodec
vs bare-for-low-regs). I chose bare low + `0x41`-only high because a
`0x40` prefix is never emitted by compilers for `B8+rd` and the row is
named "compact"; the redundant-REX refusal is pinned
(`kompakt_nichts_rex_leer`). If the coordinator wants the always-REX
convention instead, that is a small decoder/encoder change with the
proofs carrying over. Nothing else in the task looked wrong.
