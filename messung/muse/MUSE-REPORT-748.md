# MUSE-REPORT-748: Hardware completion — compact ADD with imm8

Lane 748, clone /home/simon/Dokumente/gabbro-muse/a748, branch muse/748.
Owned files only: `grammatik/Grammatik/X86/CompactImm8Add.lean`,
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

New module `grammatik/Grammatik/X86/CompactImm8Add.lean` (~660 lines)
covers exactly one row: `REX.W + 83 /0 ib`, ADD r64, imm8,
register-direct (ModRM mod = 3, extension digit /0).

Provenance (all local, no intuition): Intel SDM combined volumes 1-4,
edition 325462-093US (September 2026),
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`, Vol. 2A 3-14
"ADD-Add": opcode table line "REX.W + 83 /0 ib  ADD r/m64, imm8 ... Add
sign-extended imm8 to r/m64"; Description "When an immediate value is
used as an operand, it is sign-extended to the length of the destination
operand format"; Operation "DEST := DEST + SRC"; Flags Affected "The OF,
SF, ZF, AF, CF, and PF flags are set according to the result."

Definitions (all reuse, no duplication):
- `immSext : Nat -> Wort` via canonical `sext .b8`
- `addImmOp (b) (x) (n)` / `addImmFlags (b) (x) (n)`: width-generic value
  and flags from canonical `trunc/cfAdd/ofAdd/zfTest/parityEven/negB`;
  AF is `none` at every width (deliberate conservative gap vs the manual,
  booked in CUTS, following the Ganzzahl S4 discipline)
- `CompactAddForm` (`addImm8 dst imm`), `encodeCompactAdd` (Option:
  `none` outside i8), `compactAddLaenge`, `decodeCompactAddOp`,
  `decodeCompactAdd`, `CompactAddDec`, `compactAddSchritt` (through
  accepted `schrittRegister`), witness states `addKetteProg/Reg/Start/
  Mitte/Nach/Ende`

Theorems (33; every premise used; axioms all within
propext/Classical.choice/Quot.sound, most below):
pins `pin_immSext_7f/80/ff/00`, `pin_addImm_rax_5(_dekode)`,
`pin_addImm_r9_ff(_dekode)`; identities `addImmFlags_af`,
`addImmOp_b64`, `addImmFlags_cf/of/sf/zf/pf` (each IS the accepted
`add64` flag); range `encodeCompactAdd_some/verweigert/ursache`;
`roundtripCompactAdd`, `compactAddLaenge_ok`; refusals
`compactAdd_sonde_abgeschnitten`, `compactAdd_sonde_nachbarn` (imm32
opcode, other digits, memory ModRM, accumulator row, REX.R, missing
REX.W, bare opcode);
dispatch `pilot_verweigert_compactAdd`, `compactAdd_verweigert_pilot`;
steps `compactAddSchritt_laenge/weiter/immer/rahmen`;
`CompactImm8Add_verbindung` (bytes decode, encoder answers, step lands
the sum with accepted flags, pilot store hands sum to memory with word
read-back); witness `add_kette_dekode/schritt/speicher`;
`CompactImm8Add_verbindung_zeuge` (joint: imm 5, reached two-step run
changing data byte 0 to 15, plus planted length refusal).

Read as instructed: Typen, Wort, Speicher, Ausfuehrung, Codec, Bild,
TSO, NarrowOps, NarrowCodec, MulDiv, MulDivCodec, ShiftLogic,
ShiftCodec, ControlFlow (+ControlCodec), LockedOps, ScalarFloat (+Codec),
Ganzzahl, Gleitprofil, Vektor (+Codec), Relokation, ExtendedExecution,
DecodeFault, HardwareFaults, Byteschritt (fetchDekodiert). Reused:
canonical Zustand/Speicher, Wort tests, add64, negB_b64, codec helpers,
schritt/schrittRegister/store64 lemmas, zeugenSpeicher. No new numbers,
no MARKE changes, no source/checker/Spec/emitter edits, no
friend-reserved files. No `sorry/admit/axiom/native_decide/unsafe`.

## Build status

- `./lean-probe grammatik/Grammatik/X86/CompactImm8Add.lean`: 0 errors;
  every `#print axioms` within standard set.
- `./lean-bau` (full project): GREEN — `== exit 0; 0 error line(s)`,
  `Built Grammatik (483 jobs)`. Findings on the way: (a) three runs
  failed at the final link with "failed to read file ...olean" for a
  different untouched X86 module each time (all present right after) —
  fallout of the aborted link below, gone once the real defect was
  fixed; (b) the real defect was MINE: `sonde_abgeschnitten` collided
  with `ShiftCodec.sonde_abgeschnitten` ("environment already contains
  ... from Grammatik.X86.ShiftCodec"). Renamed to
  `compactAdd_sonde_abgeschnitten` / `compactAdd_sonde_nachbarn` and
  collision-checked every other new name against `grammatik/X86/`
  (clean). `gabbro_ziel` files untouched (only owned files differ from
  master); standard axioms unaffected.
- No Rust changes: `./cargo-pruef` not applicable (Lean-only lane).

## Open / next

- Re-run `./lean-bau` when the build dir is quiet; on green, run the
  publication checks and push per AGENTS.md (push/archival owned by
  coordinator, not this lane).
- Next integration (other owners): route the covered bytes through
  `fetchDekodiert`/`decodeExt`; memory-83 rows; TSO bridge (register
  form needs none); source correspondence (bridge lane business).

## Task feedback

The ZEUGE line asks for a "non-degenerate" companion in source terms
(tables/functions); for a hardware row this was interpreted, per the
task's own parenthetical, as a jointly inhabited memory-changing
reached run, which the zeuge provides (two-step ADD-then-store,
observable byte change 0 -> 15). No extra premise was needed; the
target statement was shaped by this lane and judged accordingly at
review. AF-none contradicts the manual's "AF set" line deliberately
and is booked as a conservative gap, as the task sentence orders.
