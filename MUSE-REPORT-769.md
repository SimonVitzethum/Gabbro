# MUSE-REPORT-769: Hardware completion -- jump-table certificates

## Task

Lane 769: cover indirect JMP through validated jump tables in
`grammatik/Grammatik/X86/JumpTableCert.lean`: validator-tracked target
set, every target a decoded start or listed entry, no forged pointer
(M140), pinned bytes. Reuse canonical state/memory/TSO and the accepted
fetched-step dispatchers; no new machines, decoders, or interpreters.

## What was done

New file `grammatik/Grammatik/X86/JumpTableCert.lean` (~600 lines),
imported at the end of `grammatik/Grammatik.lean`. All work reuses the
accepted vocabulary: `Typen`/`Speicher`/`Ausfuehrung`/`Byteschritt`
fetch discipline, `IndirectControlHardwareForms` (`decodeIndirekt`,
`jmpMemSchritt`, `fetchInd`, `indByteschritt`, `indirektZielOk`,
`indAdapterDecode`), `HardwareFaults` (`leseKlasse`, `istKanonisch`,
`adrKlasse`), and `TSO.TSOZustand`. No new decoder row, no new
interpreter, no source/checker/Spec/goal/emitter change, no new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT change.

Definitions: `tabSlot` (base + 8*i), `tabEintrag` (`read64` at the
slot), `jtZertOk` (reused `indirektZielOk` at every slot of the n-entry
table; unreadable slot refuses), `tabWorte`, `jtGeschmiedetB` (M140
mirror: true means no slot reads the word), `jtSprungOk` (effective
address is in-bounds slot), `jtTsoNach` (store buffer untouched).

Theorems: `jtZertOk_eintrag`, `tabWorte_enthaelt`,
`jtEcht_nicht_geschmiedet`, `jtGeschmiedet_verweigert`,
`jtSprungOk_slot`, the TARGET `JumpTableCert_verbindung` (a certified
fetched `JMP [base+disp]` lands on a tracked target -- decoded start or
listed entry -- with flags/memory/registers kept except RIP, no fault
class, through the accepted fetched byte step, unforged; admission is
DERIVED from the certificate via `jtZertOk_eintrag`, never assumed),
`jtSprung_tso_neutral`, `jtLesefehler_pf`,
`jtSprung_verweigert_ohne_leserecht`, `jtIndex_ausserhalb_verweigert`,
canonical-gate pins, pinned bytes `48 FF A0 00 00 00 00` with
common-adapter dispatch (`jtAdapter_bytes`) and pilot separation, three
neighbour refusals (far `/3`, `mod=0`, `E3`), two certificate refusals
(unreadable slot, foreign target), and the companion
`JumpTableCert_verbindung_zeuge` (all six premises jointly on concrete
values -- two-slot table at 8200 holding 4200/4208, fetched
`JMP [rax+0]` at 4096 -- all eight conclusion conjuncts through the
fired connection, plus a memory-changing run: data cell 8300 zero to 42,
read back).

## Verification

- `./lean-probe grammatik/Grammatik/X86/JumpTableCert.lean`: 0 errors.
- `./lean-bau`: `== exit 0; 0 error line(s)`, 485 jobs, build
  completed successfully (run after the final edit, before commit).
- `#print axioms` for every main theorem: only `propext`,
  `Classical.choice` (inherited from two reused adapter round-trip
  lemmas), `Quot.sound` -- the standard set, no `sorry`/`admit`/
  `axiom`/`native_decide`/`unsafe` anywhere in the file.
- Every theorem uses all its premises; no conclusion restates a premise.

## What remains open

Explicitly listed in the file CUTS block: no hardware correspondence
(canonical subset only); the unified-`decodeExt` admission of these
bytes stays with the dispatcher owner (reused `indAdapterDecode`
instead, pilot-first-disjoint by proved construction); the
decoded-start producer and patched-site re-decode stay with their
owners; no per-access target-to-W/GX simulation (per-byte TSO facts do
not give whole-word atomicity); no source/contract/cost/time claim; no
fault delivery (only class observation).

## Assessment of the task

The task as written is sound: the requested certificate shape
(target-set admission + M140 no-forge + pinned fetched bytes) composes
with the accepted `IndirectControlHardwareForms` fetch/step interface
without new axioms or vocabulary. Nothing in it needed weakening; the
one judgment call was deriving (not assuming) target admission from
the certificate, which the interface supports directly.
