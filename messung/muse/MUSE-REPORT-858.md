# MUSE-REPORT-858: Composition closing — entry-duties closing

## What was done

New owned file `grammatik/Grammatik/X86/ComposeEntryDuties.lean`
(plus the one-line import in owned `grammatik/Grammatik.lean`) closes
entry-state, image permissions and user binding duties to one checked
conjunction per image.

**Producer/consumer interface closed:** producers are the accepted joint
entry admission (`EntryExecution.eintrittZulassung` = checked mapping AND
entry state AND caller gates), the accepted validator skeleton
(`ValidatorSkeleton.valX86` = mapping AND decode coverage, `valTore`,
`valLayout`, `externOk`), the accepted computed layout
(`TableLayout.layoutOk`) and the accepted byte-step execution
(`Byteschritt.byteschritt` through `zulassung_erster_schritt`). The
consumer is the per-image duty conjunction `pflichtSchluss` and the
source binding duties at their actual place (`ReqAmEintritt` through the
accepted reached run, the gate channel link through the accepted
`tor_grund_im_kanal`). Nothing is re-proved: no second loader, decoder,
executor, layout or ISA model.

## Exact new names

- `pflichtSchluss` (def): `eintrittZulassung && bildDeckung &&
  valLayout && externOk` per image; any unresolved obligation refuses.
- `pflicht_eintritt`, `pflicht_valX86` (projections to the accepted
  admission and image skeleton).
- `ComposeEntryDuties_verbindung` (TARGET): generic over arbitrary
  admitted inputs — one admission yields entry admission, image
  skeleton, layout/extern duties, checked mapping, and RIP executability
  through the CHECKED loaded mapping.
- `pflicht_erster_schritt`: the closing is execution — a fetched
  instruction with an outcome steps the actual byte machine.
- `pflicht_verweigert_eintritt` / `_ohne_deckung` / `_ohne_layout` /
  `_ohne_extern`: one generic refusal per unresolved obligation.
- `pflicht_zeuge_ok` (`decide` acceptance on the minimal image),
  `pflicht_mutiert_verweigert` (coverage refusal, mapping intact),
  `pflicht_layout_verweigert` (overlap), `pflicht_extern_verweigert`
  (unproved foreign body).
- `ComposeEntryDuties_verbindung_zeuge` (TARGET companion): all premises
  jointly inhabited on the minimal accepted image with the admitted
  hosted entry — fetched `ret` steps, reached non-degenerate source run
  (table-writing call, `0 -> 5` change) carries `ReqAmEintritt` at its
  place, real eight-byte x86 memory change, three planted refusals
  (unlisted RIP, clobbered gate, mutated opcode).

## Verification

- `./lean-probe grammatik/Grammatik/X86/ComposeEntryDuties.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `exit 0`, `Build completed successfully (511 jobs)`.
- Axioms: every theorem on `[propext]` except `pflicht_erster_schritt`
  on `[propext, Quot.sound]` (inherited from the accepted
  `zulassung_erster_schritt`) and the TARGET witness on exactly
  `[propext, Classical.choice, Quot.sound]` — the standard `gabbro_ziel`
  set. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files touched.

## What remains open (explicit CUTS in the file, never assumed)

- Source-to-entry lowering (admitted bytes are a source program's
  emission): OPEN, owner shared-IR lane 287 + QUELLBRUECKE bridge.
- Per-access target-to-W/GX simulation: OPEN, owner TSO bridge lane
  (source `schwach_ist_gX` reused, never assumed for the target).
- Budget/work transfer and `valX86_sound`: OPEN (budget lane,
  validator-soundness follow-up).
- Multi-step control flow, entry legality beyond containment,
  callee-side templates: with their owners.

## Task remarks

Nothing in the task statement was found wrong. The
`torRuferPflicht` caller-duty interface (stated but never jointly
instantiated in `EntryExecution`, since the fixture carries no gate
inhabitant) is consumed here only through the accepted channel-link
theorem and the reached-run contract at actual values; a gate-call
lowering that discharges it at an actual call site remains the named
open consumer obligation.
