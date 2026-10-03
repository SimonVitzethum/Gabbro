# MUSE-REPORT-896: exact review of author 746 (compact zero-extending MOV reg, imm32)

Lane 896, branch `muse/896`, clone `/home/simon/Dokumente/gabbro-muse/a896`.
Task: report-only exact review of author 746. I own only this file; no source,
no live controls, no other clones were touched.

## CANDIDATE

CANDIDATE: 746 9f52fcb8f1e59667acd1dfb219a0f251b28ab07b

Pinned snapshot (`.tmp/review/SNAPSHOT.json`, base
`23b9a42fb44f2365b636cf8a9c440a2dfd8cae50`, clean): exactly three files —
`MUSE-REPORT-746.md`, `grammatik/Grammatik.lean` (one import line),
`grammatik/Grammatik/X86/CompactImmMov32Zero.lean` (914 lines). The PATCH diff
confirms no other file is touched: no diagnostic/gift/example/CLI numbers, no
MARKE changes, no source/checker/Spec/goal/emitter edits, no friend-reserved
optimiser files. Scope-compliant.

## VERDICT

VERDICT: ACCEPT (bounded: exactly the canonical no-REX.W `B8+rd id` row, with
the CUTS below; no hardware correspondence claimed or granted).

## What I inspected

- Full candidate file (914 lines) in `.tmp/review/author-746/`, owner task,
  author report, complete BUILD-EVIDENCE.json (all intermediate
  `./lean-probe` runs plus final `./lean-bau`), PATCH file list.
- Official local manuals: `intel-instruction-reference.txt` + REFERENCES.json
  (Intel SDM 325462-093US, sha-pinned). Verified: opcode table
  `B8+ rd id MOV r32, imm32` vs `REX.W + B8+ rd io MOV r64, imm64` (lines
  65711-65712); operand-size rule "32-bit operands generate a 32-bit result,
  zero-extended to a 64-bit result" (line 4378); default 32-bit operation size,
  REX.R reaching R8-R15, REX.W promoting to 64 bits (MOV Description context).
- Reused vocabulary confirmed present in accepted modules of this clone:
  `mergeRegNarrow_b32`, `extendNarrow_zero`, `narrowTruncMod` (NarrowOps);
  `laengeOk`, `ripNach`, `regSet`, `regSet_gleich/fremd`, `lauf`,
  `zeuge_speicher_aendert_sich`, `zeugeProg/Zustand/Flags` (Ausfuehrung);
  `geholt`, `ausfuehrbarN` (Byteschritt); `parseLe32_suffix`
  (DecodingCoverage); `decodeNarrow` (NarrowCodec).

## Architecture checks (all pass)

- Byte forms: bare `B8+rd` + LE imm32 (5 bytes, low regs); single `0x41`
  REX.B prefix for r8-r15 (6 bytes). `0x41` = W0 R0 X0 B1 is the only accepted
  prefix; REX.W (`0x48…`, pilot `movImm64` domain), redundant `0x40`, REX.X
  (`0x42`), truncated and unknown inputs are all explicitly refused with pins
  (`kompakt_nichts_*`). Refusing redundant-REX forms that silicon would
  execute is a sound canonical-row restriction (refusal-only), pinned and
  CUTS-declared — not fake closure.
- Semantics: value is canonical `trunc .b32` with width-exact lemmas
  (`compactWert_nat/fits`), bridged to the accepted clearing discipline
  (`compactWert_gleich_merge`, `compactWert_gleich_extend`) — no second
  extension operator, no duplicated arithmetic.
- Flags preserved (MOV Flags Affected: None — correct); no memory operand, and
  `stepCompact_ohne_speicher` proves memory-independence, so no TSO event,
  fault class or permission gate arises from this row. RIP advances past the
  decoded length; bad lengths refuse via `laengeOk`.
- Dispatch: pilot-first `decodeComboCompact` with proven pilot disjointness
  (`compact_pilot_verweigert`) and narrow disjointness
  (`kompakt_narrow_verweigert`); no pilot form shadowed. Arbitrary-input
  coverage is decoder-side (`decodeCompact_abdeckung/consumes`), not
  round-trip-derived.
- imm64 gate exact both ways: `keinKompaktFuerGross` (refusal) +
  `kompaktFuerKlein` (positive) + joint pin.
- Destination-dead obligation `compact_dst_tot` proved (successor destination
  independent of old value).
- Fetch/byte-step from actual executable memory (`geholt`, `ausfuehrbarN`,
  length equation); `verweigert` is absence of transition, never a fault
  claim; no #UD membership claimed (CUTS-honest, same stance as
  `HardwareFaults.fehlbyte_kein_stiller_ud`).
- Witness `CompactImmMov32Zero_verbindung_zeuge`: hostile all-ones registers
  with `rax := 0x80000001` (upper-half clearing observable, bit63 1→0;
  register-changing step by `decide`) jointly with the reached
  memory-changing `lauf` run (cell 8192, 0→42 via
  `zeuge_speicher_aendert_sich`). Non-degenerate, all premises jointly
  instantiated. The ZEUGE requirement is met.
- Hygiene: grep of the final file finds no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` (only benign substrings: `#print axioms`,
  "admitted" in a doc comment). One intermediate build row showed `sorryAx`
  on `kompakt_gross_verweigert_pin`; the final `./lean-probe` row lists it
  under standard axioms only — the `sorry` was removed before the final
  commit. Every added premise is used (`hok` in step lemmas); no Prop-typed
  premises; no quantified-away contracts; no discarded premises.
- Build: final `./lean-bau` green (`== exit 0; 0 error line(s)`, 483 jobs,
  `Built Grammatik`); final `./lean-probe` 0 errors with all 18 `#print
  axioms` within `[propext, Classical.choice, Quot.sound]`.
- CUTS block is precise: self-consistency only (no silicon correspondence),
  no other MOV rows, shared `byteschritt`/`extByteschritt` not yet rewired
  (dispatcher owners' integration), no TSO/W/GX bridge, no source/ABI/image/
  entry/relocation/cost claims.

## Minimal notes (no repair required)

- The bare-low + `0x41`-only convention vs always-REX is a coordinator-level
  taste call; the author flagged it explicitly with the refusal pin, and proofs
  carry over either way. Not a defect.
- The next integration (rewiring shared dispatchers through
  `decodeComboCompact`) belongs to the dispatcher owners, as CUTS states.

## Last build result

No `./lean-bau` run by this reviewer (report-only lane; build evidence taken
from the author's recorded runs: final `./lean-bau` `== exit 0`, 0 error
lines, 483 jobs). This review added no source, so the tree is untouched.
