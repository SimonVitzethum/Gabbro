# Muse Report 854: Composition closing — support-bytes closing

## What was done

New file `grammatik/Grammatik/X86/ComposeSupportBytes.lean` (owned) plus one
import line in `grammatik/Grammatik.lean` (owned). It closes the
producer/consumer interface "every reachable support byte (arena, thread,
float shims the program uses) is validated; unvalidated reachable bytes
refuse" by composing already-accepted modules only:

- Producers reused by name, nothing re-proved: `ValidatorSkeleton.valX86` /
  `valTore` / `valLayout`, `GateStub.torOkB` / `bindungErstelltB` /
  `stubEndsTrapB` / `trapBytes` / `schreibTor` / `zeugenMoves`,
  `TableLayout.layoutFuer` / `layoutOk` / `slotAufz` / `zeugenU`,
  `EntryState.eintrittOk` / `zeugenEintrittHosted`, `Gleitprofil.mxcsrGueltig`,
  `Byteschritt.byteschritt` / `fetchDekodiert` / `schritt` (+ `byteschritt_weiter`,
  `byteschritt_verweigert_ohne_fetch`, `byteschritt_verweigert_ohne_schritt`,
  `ausgangByte`, `ausgangRip`), `LoadedExecution` (`bildZustand`,
  `bildStore`, `bildStoreStart`, `bildStoreStartMutiert`,
  `bildStore_schritt_speichert`, `bildStore_datenRip_verweigert`,
  `bildStore_mutiert_verweigert`, `storeReg`, `storeFlags`),
  `Bild` (`geladen`, `valZeuge`, `valWx`, `schreibLese_zeuge`).
- No second interpreter, executor, loader, or decoder is defined; no source,
  checker, Spec, goal, emitter, or optimiser file is touched; no new
  diagnostic/gift/example/CLI numbers; no MARKE_EMIT changes.

## Exact new names

Definitions: `StuetzArt` (`arena` / `faden` / `gleit`), `stuetzOk`,
`stuetzSchritt`, `stuetzWitS`, `stuetzWitDaten`, `stuetzWitMutiert`.

Theorems: `stuetzOk_teile`, `stuetzSchritt_weiter`,
`stuetzSchritt_verweigert_ohne_fetch`,
`stuetzSchritt_verweigert_ohne_schritt`, `stuetz_verweigert_ohne_bild`,
`stuetz_verweigert_ohne_tor`, `stuetz_verweigert_ohne_layout`,
`stuetz_verweigert_ohne_bindung`, `stuetz_verweigert_ohne_trap`,
`stuetz_verweigert_ohne_eintritt`, `stuetz_verweigert_ohne_mxcsr`,
`ComposeSupportBytes_verbindung` (TARGET),
`ComposeSupportBytes_verbindung_zeuge` (companion),
`stuetzWit_schritt`, `stuetzWit_ok`, `stuetzWit_wx_verweigert`,
`stuetzWit_daten_verweigert`, `stuetzWit_mutiert_verweigert`.

The TARGET is generic over arbitrary admitted inputs (all eight
`ExtInstr`-independent parameters: profile, image, bias, gate, moves,
layouts, entry kind/state, caller state). The companion instantiates the
closing jointly at the accepted store tuple, shows the reached
memory-changing run through the composed step (42 into `0x102000` via
`stuetzSchritt`, zero before), planted step-level refusals (data-section
start, forged opcode byte, both inverted from the accepted `ausgangRip`
refusals to `verweigert`), the admitted tuple on the minimal accepted image,
the non-degenerate source side (`layoutOk` true, `slotAufz` nonempty,
`setze` writes `konto`), a real write/read change, and planted admission
refusals (W^X image, FTZ word).

## Last build result

`./lean-bau`: `Build completed successfully (511 jobs).`, exit 0.
`./lean-probe grammatik/Grammatik/X86/ComposeSupportBytes.lean`:
`0 error(s)`. Axioms per in-file `#print axioms`: `[propext]` for the
`Bool`-inversion/refusal/decide facts, `[propext, Quot.sound]` for the
step-composing facts and the joint witness. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` anywhere in the file.

## What remains open (also as CUTS in the file)

Source correspondence (waits on shared IR lane 287), hardware
correspondence, TSO/W/GX per-access bridge (owners 573-574), budget/cost
transfer, whole-binary/control-flow/relocation/ABI claims, and one
explicit scoping CUT: admission is witnessed on the minimal accepted image
(`valZeuge`) while the storing run and step-level refusals are witnessed on
the accepted store image (`bildStore`); an admitted thread-root entry
combined with a storing run on a single image is not exhibited.

## Task remarks

- The initial admission attempt on `Bild.zeugenBild` failed `decide`: its
  four `0x90` code bytes are not covered by the canonical decoder, so
  `valX86` refuses it. This is correct validator behaviour (mapping holds,
  coverage does not), and the admission witness uses the accepted minimal
  `ret` image instead. No producer needed any change.
- One stylistic note: a line break immediately after `:=` inside an inline
  `{ s with field := ... }` record update in a statement triggered a parse
  error; keeping the update on one line parses. No semantic impact.
