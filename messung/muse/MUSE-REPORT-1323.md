# MUSE-REPORT-1323: valX86 decode coverage over the capstone decoder chain

## What was done

New file `grammatik/Grammatik/X86/ValidatorKapDecoder.lean` (~460 lines),
plus one import line in `grammatik/Grammatik.lean`. Coverage check over
the accepted capstone chain `kapDecode` (`HwKapsteinDecoder`, reused
unchanged, never redefined or copied). `ValidatorSkeleton` checks image
mapping and decode coverage against the ORIGINAL decoder only; this file
lifts coverage to the full 8-level capstone chain with its stated
priority (first match wins, inherited from `kapDecode`).

## New definitions

- `KapGrund` (`keinDekoder`, `keinFortschritt`, `keinBrennstoff`): named
  refusal reasons; every non-covered byte list gets one.
- `kapDecktFuel : Nat -> List Byte -> Bool`: greedy fuel-bounded full
  decode through `kapDecode`; zero-progress steps refuse instead of looping.
- `kapKetteFuel : Nat -> List Byte -> Option (List KapDekodiert x List Byte)`:
  the same walk returning the decoded rows (derivation witness).
- `KapErw` / `kapDecodeErw`: extension interface (chain first, new row only
  where the chain refuses; mirrors `ErwDec`/`decodeErw`).
- `kapDecktErwFuel`: coverage under the extended chain.
- `kapAbschnittDeckt`, `kapBildDeckt`, `valKap`: section/image admission
  (checked mapping AND capstone-chain coverage of every executable section;
  mirrors `abschnittDeckung`/`bildDeckung`/`valX86`).
- `kapGrundFuel`: named refusal of one walk (`none` iff the Bool check passes).
- `kapZeugeDatei/Bild/Code` (LOCK XADD ++ VEX VPADDQ, 14 bytes, VEX last),
  `kapStreuBild` (one stray opcode byte `0x06`).

## New theorems (all premises used, no Prop-typed premises invented)

- `kapDecktFuel_schritt`, `kapKetteFuel_schritt`,
  `kapDecktErwFuel_schritt`, `kapGrundFuel_schritt` (definitional, `rfl`).
- `valKap_deckung` (soundness): covered bytes derive into chain rows with
  no remainder.
- `kapDecodeErw_kanonisch` (no chain row shadowed) and `valKap_monoton`:
  adding a decoder row cannot uncover a covered byte list.
- `valKap_wohlgeformt`, `valKap_deckt` (admission implies mapping + coverage).
- `kapGrund_klassifiziert`: every byte list decodes or carries a named reason.
- Witnesses: `kapZeuge_wohlgeformt`, `kapZeuge_gedeckt`, `kapZeuge_valKap`;
  stray refusal at all 8 chain levels
  (`kapStreu_breit/s32/mxcsr/lock/lockAdr/kompakt/kern/avx2_verweigert`,
  each closed `decide`), `kapStreu_kette` (via `kapDecode_nichts`),
  `kapStreu_verweigert`, `kapStreu_grund` (`keinDekoder`),
  `kapStreu_wohlgeformt` (refusal is decode, not mapping);
  joint `kapZeuge_gelenk`.

## Last build result

`./lean-bau`: `Build completed successfully (688 jobs).`
`./lean-probe` on the new file: `0 error(s)`.
`#print axioms`: every main theorem depends only on `[propext]`
or `[propext, Quot.sound]` (subset of the goal-allowed set; no
`Classical.choice`, no `sorryAx`).
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file
(verified by grep; only English words "admits"/"admitted" match).

## What remains open (also in the file CUTS block)

- `valX86_sound_full` stays OPEN: no source, refinement, TSO/GX, concurrency,
  contract, entry, budget, cost/time, FP, or hardware claim.
- VEX exact-match limitation (accepted `dekodiereAvx2` matches whole lists
  only): coverage sees a VEX row at a section tail; mid-section VEX refuses
  with `keinDekoder`. Inherited, documented, not repaired.
- No per-row consumed-length theorem (progress guarded, not proved);
  no chain-tie facts beyond `kapDecode`'s definition; no silicon re-check
  (vendor-neutral, rule 17); no loader/entry/relocation/control-flow claim.

## Task note (plainly, per rule 4)

The lane file's second CONTEXT paragraph and MECHANISM paragraph describe a
different lane shape (family-to-`HwMaschine` connection via `HwAdapter`,
multi-core memory-changing witness, `HwWf` preservation) and contradict the
first paragraph's deliverable (coverage check over `kapDecode` with
`valKap_deckung`, monotonicity, LOCK+VEX + stray witnesses,
`valX86_sound_full` OPEN). I implemented the first paragraph, which is
self-consistent and matches the file/ownership line. No `ZEUGE:` lines were
present, so no `_zeuge` obligations arose; the two requested witnesses plus
the joint witness are delivered as theorems. Nothing else in the task looks
wrong: `kapDecode [natByte 6] = none` and the LOCK-prefix/VEX-tail walk both
verified by evaluation before proving.
