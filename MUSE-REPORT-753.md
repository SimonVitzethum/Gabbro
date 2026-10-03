# MUSE-REPORT-753: accumulator short ALU forms (05/2D/3D)

## Task
Lane 753: cover the RAX short opcodes (05 ADD / 2D SUB / 3D CMP) with flag
identity and the validator-decided short-vs-ModRM choice, pinned bytes,
through the accepted `ExtendedExecution` dispatcher. Target theorems:
`CompactArithRax_verbindung` + companion
`CompactArithRax_verbindung_zeuge` (jointly inhabited, non-degenerate,
memory-changing reached run).

## What was done
New file `grammatik/Grammatik/X86/CompactArithRax.lean` (~990 lines) plus
one import line in `grammatik/Grammatik.lean`. No other file touched; no
diagnostic/gift/example/CLI numbers, no MARKE changes, no source/checker/
Spec/goal/emitter edits, no friend-reserved optimiser files.

Provenance (local manuals only): Intel SDM combined volumes 1-4, edition
325462-093US September 2026 (`.tmp/HARDWARE-REFERENCES/REFERENCES.json`,
sha256-pinned): ADD table "REX.W + 05 id, ADD RAX, imm32, Add imm32
sign-extended to 64-bits to RAX"; SUB table "REX.W + 2D id";
CMP table "REX.W + 3D id". Only canonical REX 0x48 admitted.

Definitions: `RaxOp` (addRaxImm/subRaxImm/cmpRaxImm over `BitVec 32`),
`RaxDec`, `raxOpcode`, `encodeRax` (6 bytes), `decodeRax`, `stepRax`
(reuses `Wort.add64`/`sub64`, `Ausfuehrung.dispWort`/`schrittRegister`;
CMP mirrors the `cmpReg64` arm), `stepRaxFp`, `decodeRaxCombo`
(`decodeExt` first, short rows only on refusal), `raxComboLen`,
`raxZugelassen`, `fetchRax` (`fetchDekodiert` discipline),
`raxByteschritt`, `raxSchritt2`, `wahlSchritt` (validator Bool: short
form vs ModRM mov+add route through a scratch register), witness
memory/state defs (`raxWitBild/Bytes/Code/Daten/Speicher/Reg/Kern/
Start/Bereit/S1/M`).

Theorems (all premises used; `#print axioms` for each — all within
propext/Classical.choice/Quot.sound, no sorry/axiom/native_decide):
encoding/decoding — `encodeRax_len`, `roundtripRax`, pins
`pin_add_rax_eins(_dekode)`, `pin_sub_rax_bytes/dekode`,
`pin_cmp_rax_bytes/dekode`, refusals `rax_nichts_leer/kurz/ohne_rex/
achtbit_add/sub/cmp`, `rax_nichts_rex_anders/modrm_opcode`;
execution — `stepRax_add/sub/cmp`, `stepRax_laenge_verweigert`,
`stepRax_braucht_laenge`, flag identities `rax_add/sub/cmp_flag_identitaet`
(short step sets exactly the flags and RAX value the ModRM
addReg64/subReg64/cmpReg64 sets with the sign-extended immediate in rcx),
`stepRax_speicher_bleibt` (no load/store, no permission gate, no TSO
footprint); dispatch — `pilot_weist_raxkurz_zurueck`,
`narrow_weist_raxkurz_zurueck` (both general over op and suffix),
`decodeRax_ohne_rex`, `decodeRax_verweigert_pilot` (general over all 14
pilot forms), `decodeRaxCombo_kanonisch/erweitert/nichts`,
`ext_weist_add/sub/cmp_zurueck` (whole-chain closed pins),
`pin_combo_add/sub/cmp`, `pin_combo_pilot_ret`; choice —
`wahlStimmtUeberein` (same RAX, flags, memory on both routes);
byte-facing — `stepRaxFp_weiter/verweigert`,
`stepRaxCombo_pilot/rax/rax_verweigert`, `raxZugelassen_summe/laenge/
ausfuehrbar`, `fetchRax_erfolg`, `raxByteschritt_weiter/verweigert`;
connection — `CompactArithRax_verbindung` (fetched short ADD + pilot
spilling store reaches incremented RAX, spilled word, ModRM-identical
flags, RIP past both, xmm/fp kept) and `CompactArithRax_verbindung_zeuge`
(41 + 1 = 42 in RAX from fetched bytes, cell 0 -> 42, all premises
jointly discharged on closed values).

## Verification
- `./lean-probe grammatik/Grammatik/X86/CompactArithRax.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (483 jobs)`. Goal files untouched, so
  `gabbro_ziel` is unaffected (first `./lean-bau` attempt hit a
  transient queued-slot toolchain read error on the aggregate root
  target, unrelated to this module; retry passed clean).

## What remains open (see CUTS in the file)
No SUB/CMP fetched runs (run pins ADD; step/identity proved for all
three); whole-chain refusal of short windows pinned per closed form,
not generally over all immediates; no per-access TSO bridge content
(short steps touch no memory; store leg is the accepted pilot step);
no source/ABI/entry/budget/cost claims; hardware correspondence is the
stated canonical subset grounded in the cited SDM tables, not silicon
verification.

## Notes on the task / findings
- Lean parser quirk found: multi-line `{ ... }` structure
  instance/update terms nested in defs or tactic `have` statements
  failed with "unexpected identifier; expected '}'"; single-line forms
  and the proven multi-line top-level pattern compile. Restructured
  accordingly (witness defs + two statements).
- `decide` cannot prove whole-state (`Option Zustand`) equations
  (functions block DecidableEq); the witness therefore shapes `raxWitS1`
  / `raxWitM` exactly as the step/write equations conclude and proves
  those premises by rewrite, with `decide` reserved for first-order
  facts (fetches, permissions, byte/word values). No witness weakening.
- One `./lean-probe` call hit the 120s timeout from queue wait, not
  proof cost; retry with a larger budget passed.
