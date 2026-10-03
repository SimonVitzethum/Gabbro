# MUSE-REPORT-824: Composition closing — decode-to-execution closing

## Task
Close decode-then-execute for admitted families through the common
dispatcher: every decoded form reaches its execution rule; undecoded bytes
never execute. Compose already-accepted modules; no re-proofs, no second
interpreter, generic over arbitrary admitted inputs, reached
memory-changing runs plus planted refusals, missing legs as explicit CUTS.

## What was done
New file `grammatik/Grammatik/X86/ComposeDecodeExec.lean` (owned) plus one
registry import line in `grammatik/Grammatik.lean` (owned). The closed
producer/consumer interface: unified decoder `ExtendedExecution.decodeExt`
(pilot + narrow, multiply/divide, shift, SETcc/CMOVcc, scalar FP,
packed-integer) produces, unified step `stepExt` over the accepted
per-family evaluators consumes, common dispatcher `fetchExt` over the
actual fetched window `Byteschritt.geholt` plus `extByteschritt` connects.

New definitions/theorems (all in `Gabbro.Grammatik.X86`):
- `dekodiertErreichtSchritt` (def): interface predicate — every form the
  dispatcher fetches reaches its unified execution rule.
- `dispatcher_erreicht_schritt`: generic over arbitrary `ExtInstr`
  (all eight families) via accepted `extByteschritt_weiter`.
- `fetchTrifftDekodierer`: fetch success carries decoder agreement +
  admission via accepted `fetchExt_erfolg`.
- `undekodiertVerweigert`: `decodeExt` refusal on the fetched window is
  dispatcher refusal via accepted `extByteschritt_verweigert`.
- `pilotKanonischErreicht`: for an ARBITRARY pilot `Befehl`, canonical
  bytes in the window plus checked execute permission reach the pilot
  rule (via accepted `roundtrip`, `decodeExt_kanonisch`, `encode_len`).
- `ComposeDecodeExec_verbindung` (TARGET): the conjunction of both
  directions, premise-free over `(t b)`, proved by composing the above.
- `ComposeDecodeExec_verbindung_zeuge` (companion): joint instantiation
  at the accepted mixed pilot/scalar-FP witness (`extWitStart`,
  `extWitBereit`) plus the non-degenerate memory-changing reached run
  (two actual cells zero, then 42 after two dispatcher steps from fetched
  bytes, via `extWit_zwei_schritte_speichern`/`extWit_anfang_null`) and
  the planted refusal past the image (`extWit_nachBild_verweigert`).

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeDecodeExec.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed
  successfully (509 jobs)`, including `Built Grammatik.X86.ComposeDecodeExec`.
- Axioms: `dekodiertErreichtSchritt`, `dispatcher_erreicht_schritt`,
  `undekodiertVerweigert`, `ComposeDecodeExec_verbindung`,
  `ComposeDecodeExec_verbindung_zeuge`: `[propext, Quot.sound]`;
  `fetchTrifftDekodierer`: `[propext]`; `pilotKanonischErreicht`:
  `[propext, Classical.choice, Quot.sound]` (the standard `gabbro_ziel`
  set). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved files.

## Open / CUTS (in-file, explicit)
- Per-family canonical-byte closing beyond the pilot is NOT claimed:
  extension families reach their arms only through the accepted pins
  (`pin_ext_*`); arbitrary-input encoder-to-dispatcher legs need general
  non-shadowing owned by the extension codec lanes (`decodeNarrow`,
  `decodeMulDiv`, `decodeShift`, `decodeSetCC`/`decodeCmov`, `fpDecode`,
  `decodeVector`).
- No hardware, source/IR, TSO/W/GX, LOCK/wider-SIMD, ABI/loader/entry/
  budget, or whole-image-beyond-window claim. `verweigert` is absence of
  transition, not termination; the divide `halt` is carried, not proved.

## Task assessment
The task statement is sound as written: the dispatcher-level generic
closing plus the arbitrary-pilot corollary is the most that can be closed
without the missing general non-shadowing legs, which are correctly left
as named CUTS rather than assumed. Nothing in the task appeared wrong;
the ZEUGE companion is provided with a memory-changing reached run as
required (X86-state analogue: two actual cells 0 to 42 through the
composed dispatcher step).
