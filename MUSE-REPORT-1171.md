# MUSE-REPORT-1171: Linking, relocations and the final mapping

## What was done

New file `grammatik/Grammatik/X86/PipelineLink.lean` (~590 lines) plus one
`import Grammatik.X86.PipelineLink` line appended to `grammatik/Grammatik.lean`.
Generic linking of two separately lowered units: symbol resolution,
relocation operands (rel32/abs64) applied then re-decoded, file offsets vs
virtual addresses vs load bias checked against the ACTUAL `geladen`
mapping, W^X. No existing file was otherwise touched; no second decoder,
loader, executor, ISA model or IR was created.

## New definitions

- `LinkEinheit` (`bytes`, `vaddr`): one separately lowered unit with its
  link-time virtual base. Byte `k` of unit `u` maps to `bias + u.vaddr + k`.
- `verknuepfeDatei a b`: linked file bytes (`a.bytes ++ b.bytes`).
- `LinkFeld` (`rel32 disp` | `abs64 wert`): the only two operand shapes that
  link here; `feldBytes` is the canonical rel32/abs64 split.
- `linkPatch img off f`: one applied operand (`patchRel32` / `patchAbs64`).
- `loeseSymbol`: id-to-target table; only listed ids resolve.
- `linkAbschnittA/B`, `linkBildAus`, `linkBild`: two code sections (R-X,
  never W+X) over explicit/patched file bytes, empty `reloks`, fixed bias.
- Witnesses: `zeugenEinheitA` (5-byte jump), `zeugenEinheitB` (`ret`),
  `zeugenVerknuepft`, `zeugenGepatcht` (disp +16 at offset 1), `wxVerletzt`.

## New theorems (all green, axioms within propext/Classical.choice/Quot.sound)

- `loeseSymbol_trifft/leer/fremd_verweigert`: only listed ids resolve.
- `linkPatch_bereich/stelle/rahmen/laenge`: range, exact site bytes, the
  FRAME (no relocation changes a byte outside its operand), length kept.
- `verknuepft_abdeckung_union`: linked decode coverage = conjunction of the
  units' section coverages (union leg required by the task).
- `verknuepft_byte_geladen`: found VA loads the mapped file byte through
  the actual `geladen` mapping (reuses `geladenByte_datei`).
- `verknuepft_wx`: member sections of a well-formed image are W^X
  (reuses `wohlgeformt_wx`).
- `verknuepft_rel32_schliesst`: patched rel32 re-decodes to the patched
  value (reuses `ComposePatchBytes_feld_verbindung`).
- `verknuepft_korrekt`: the link closing -- re-decoded displacement, fit,
  form coverage, coverage union, W^X, executed mapping, site range, frame.
  Every premise is used by the proof.
- Refusals (poison probes): `verknuepft_ueberlapp/ueberlauf/aussen`
  (overlap, overrun, out-of-range disp), `verknuepft_symbol_verweigert`
  (unlisted id), `verknuepft_wx_verweigert` (W+X), `verknuepft_opcode_falsch`
  (forged opcode), `verknuepft_loch_verweigert` (unlisted target 0x1800).
- `verknuepft_korrekt_zeuge`: joint premise inhabitation on the concrete
  two-unit link (jump unit + `ret` unit, patched +16, re-decoded with B's
  byte as rest, image well-formed, coverage true) with the reached
  memory-changing run (`ruf_schritt_zeuge`: return address stored at the
  stack slot, byte observably changed) and five planted refusals.

## Build results

- `./lean-probe grammatik/Grammatik/X86/PipelineLink.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed successfully
  (608 jobs)`. Whole project stays green.

## What remains open (see CUTS in the file)

Source correspondence (units arrive already lowered; no claim the bytes are
any source block's emission), `valX86_sound` / full source-to-final-byte
closing, hardware correspondence (model `Speicher`, not silicon), TSO/GX,
concurrency, budget/work. Link scope: exactly two code units and one operand
per closing; multi-unit convergence, abs64-operand re-decode, rel8,
conditional field agreement and non-jump/call/conditional sites are OPEN and
refused, never guessed.

## Task fidelity note

Nothing in the task was weakened. The coverage-union claim is stated at the
`Bild` level (`bildDeckung` over the two linked sections), which is the exact
form the validator consumes; per-byte decoder concatenation facts were
deliberately not re-proved. The memory-changing run reuses the accepted
`ruf_schritt_zeuge` (call class) while the patch witness is a jump -- the
same split the accepted `ComposePatchBytes_verbindung_zeuge` uses.
