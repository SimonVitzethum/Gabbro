# MUSE-REPORT-828: stack-to-ABI composition closing

## Task

Close stack frames with the ABI discipline: callee/caller saves on all paths,
red-zone rule per image, unwind facts agree with frame bytes. Compose
already-accepted modules into one checked closing step; no re-proofs, no
duplicated interpreter/executor. Target: `ComposeStackAbi_verbindung` with
companion `ComposeStackAbi_verbindung_zeuge`.

## What was done

New file `grammatik/Grammatik/X86/ComposeStackAbi.lean` (owned), plus the
one-line import appended to `grammatik/Grammatik.lean` (owned). Three
commits: skeleton (`587e5a8f`), closing theorem (`b5d53d19`),
witness plus refusals (`5b328a33`).

### Producer/consumer interface closed

- Producers (reused by name, never re-proved): `Stapel` (`Rahmen`,
  `Belegung`, `sichereWort`/`ladeWort`, `sichere_lade_rundreise`),
  `StackUnwind` (`push_pop_wiederhergestellt`,
  `belegung_gerettet_schranke`, `rspImRahmen`, `zeugS` witness family),
  `CallAlign16` (`rufAlignOk`, `callGeprueft_fehlalign`, `alignSmis`
  family), `Ausfuehrung` (`schritt_push64_erfolg`, `schritt_pop64_reg`,
  `lauf`), `Speicher` (`writeBytesN_hit`, `addrOff_null`).
- Interface: the callee-save slot `r.schlitzAddr (b.gerettetIdx i)` is
  identified with the machine word below the top
  (`s.register rsp - 8`) by premise `hslot`. That equation bridges the
  frame save to the machine store and back.

### New definitions/theorems

- `rotZoneImRahmen` (def): per-frame red-zone rule, the 128 bytes below
  `rsp` lie inside the frame extent. No axioms.
- `abiRahmen` / `abiBelegung` (defs): witness frame (base 8032, depth 160,
  top 8192) and layout (10 spill, 10 callee-save, 0 stack args), so
  callee-save index 9 names slot 19, the word below the witness top.
- `abi_passt`, `abi_idx19`, `abi_slot_unten`, `abi_rotzone`,
  `abi_ausgerichtet`: decide sondes. No axioms.
- `ComposeStackAbi_verbindung` (target): from layout fit, slot position,
  the slot/top equation, frame save plus readability, an actual push/pop
  pair with its guards, incoming alignment and red zone, concludes pointer
  restoration, value delivery on the register path, slot read-back on the
  frame path, register/frame agreement, and alignment/membership/red-zone
  transfer after the composed step. Axioms `[propext, Quot.sound]`.
  Every premise is consumed by the proof (fit plus position bound the slot;
  the equation bridges both stores; save/readability feed both round-trips;
  step premises feed the unwind; alignment/red-zone transfer).
- `ComposeStackAbi_verbindung_zeuge` (companion): all 15 premises jointly
  inhabited on the shared push/pop witness, plus observable memory change
  (zero becomes 42 below the old top) and a reached `lauf [push, pop]`
  run. Axioms `[propext, Quot.sound]`.
- `abi_slot_verweigert`: planted bounds refusal (slot 20 of a 20-slot
  frame). No axioms. `abi_fehlalign_verweigert`: planted misaligned call
  gate refusal (reuses `alignSmis`). Axioms `[propext, Quot.sound]`.

## Last `./lean-bau` result line

`Build completed successfully (509 jobs).` with
`== exit 0; 0 error line(s) in the COMPLETE output`.
`./lean-probe grammatik/Grammatik/X86/ComposeStackAbi.lean`:
`== 0 error(s) in the COMPLETE output`. All axioms are subsets of the
standard `gabbro_ziel` set (`propext`, `Classical.choice`, `Quot.sound`);
goal/Spec/checker/emitter files untouched. No new diagnostic, gift,
example, CLI, MARKE_EMIT, or optimiser changes.

## What remains open

- The call/ret plus alignment leg is closed by producer
  `CallAlign16_verbindung`; the fetched nested leg by producer
  `geholt_verschachtelt_wiederhergestellt` (lane 569). Neither is
  duplicated here; a future lane may fold all three legs into one
  whole-call theorem.
- TSO/store-buffer/forwarding/GX bridge, source correspondence, System V
  leaf/async-signal red-zone clobber semantics beyond the checked in-frame
  rule, and loader/entry/relocation/cost/final-image claims stay OPEN as
  listed in the file CUTS.
- Inhabitation note: the theorem quantifies over machine states, not over
  program syntax (`Vertrag`/`Stmt`/etc.), so the source-level
  table-writing non-degeneracy clause does not apply; the companion
  instead shows a non-degenerate memory-changing reached run, as the task
  requires.

## Believed-wrong items in the task

None. The scope (one checked closing step over named producers, reached
runs plus refusals, missing legs as CUTS) was provable as stated.
