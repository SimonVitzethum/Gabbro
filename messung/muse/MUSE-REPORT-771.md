# MUSE-REPORT-771 — Hardware completion: 16-byte call alignment

Lane 771, clone `/home/simon/Dokumente/gabbro-muse/a771`, branch `muse/771`.
Owned files only: `grammatik/Grammatik/X86/CallAlign16.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## Result: done, green

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`, final line
`Build completed successfully (485 jobs).` `./lean-probe` on the new file:
`== 0 error(s)`. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
Every premise of every theorem is used. No new diagnostic/gift/example/CLI
numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits, no
friend-reserved optimiser files touched.

## What was proved

16-byte call alignment obligation, enforced per loaded image through a
checked gate over the canonical vocabulary (no new machine, decoder, or
source interpreter):

- Call-site alignment `rufAlignOk` (rsp 16-aligned before the call) reuses
  the accepted `Stapel.ausgerichtet16`; post-call offset `nachRufVersatz`
  (top carries offset 8); `callGeprueft` refuses misaligned call sites with
  `none` and is the accepted `schritt` otherwise; `rufByteschritt` lifts the
  gate to actual fetched bytes via the accepted `fetchDekodiert`.
- `CallAlign16_verbindung`: aligned call takes the checked step, post-call
  top has offset 8 (from `BitVec.sub_add_cancel` via `rsp8_versatz8`), and
  the matching return restores the aligned top (reuses accepted
  `StackUnwind.call_ret_wiederhergestellt`).
- `CallAlign16_verbindung_zeuge`: joint witness over an accepted image
  (`alignBild_wohlgeformt`, profile 48) carrying canonical call bytes whose
  fetch decodes from loaded memory (`alignS0_fetch`); `lauf [call, ret]`
  reaches the restored state with an observable zero-to-return-address
  memory change; plus a misaligned twin the gate loudly refuses.

## Exact new names

Definitions: `istRuf`, `rufAlignOk`, `nachRufVersatz`, `callGeprueft`,
`rufByteschritt`, `alignDisp`, `alignDatei`, `alignCode`, `alignDaten`,
`alignBild`, `alignReg`, `alignS0`, `alignOben`, `alignM1`, `alignS1`,
`alignS2`, `alignSmis`.
Theorems: `istRuf_call`, `rsp8_versatz8`, `callGeprueft_call_erfolg`,
`callGeprueft_fehlalign`, `callGeprueft_durchlass`, `CallAlign16_verbindung`,
`rufByteschritt_verweigert_fehlalign`, `rufByteschritt_weiter_ausgerichtet`,
`alignBild_wohlgeformt`, `alignS0_ausgerichtet`, `alignS0_slot_schreibbar`,
`alignS0_slot_lesbar`, `alignS0_fetch`, `alignSmis_fehlalign`,
`CallAlign16_verbindung_zeuge`.
Axioms (all `#print axioms` in the file): subset of `[propext, Quot.sound]`
— standard, nothing else.

## Remains open (see CUTS in the file)

Silicon correspondence of the 16-byte rule; exact SDM section transfer for
faulting misaligned SSE accesses; TSO/concurrency bridge (all facts
sequential); source correspondence, costs, handler/fault delivery; process-
entry rsp alignment (not stated). `gabbro_ziel` axiom re-print
(`BeweisAtomar.lean` probe) was blocked three times by apparatus failures
(`failed to create thread`, transient olean reads of untouched files under
parallel load); the green full `./lean-bau` already elaborated that file,
and this lane's module is not in its import closure and adds no axioms.

## Task notes (things I believe are scoped narrower than written)

- The lane paragraph asks for flags/widths/TSO/async modelling "for every
  form claimed". This lane claims only call/return forms; everything else is
  explicitly OPEN in CUTS rather than modelled thinly.
- "Per image" is discharged as uniformity over loaded-image memory plus a
  witness over one accepted image — not as a per-image validator predicate.
- Rule 13's "table that some function writes" is source-syntax language;
  the X86 analogue delivered is the memory-changing reached run the ZEUGE
  line itself requires.
