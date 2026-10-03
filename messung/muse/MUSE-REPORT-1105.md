# MUSE-REPORT-1105: Exact review of lane 1104 (ComposeAcceptedConsumers)

Clone `/home/simon/Dokumente/gabbro-muse/a1105`, branch `muse/1105`.
Report-only independent review; OWN ONLY this file. No source, private,
root, or network changes. No other models called.

CANDIDATE: 1104 3d507bc49895d0890452d9c20f3236e1ce7ca2ad

The reviewed candidate is lane 1104 at the HEAD pinned above
(per `.tmp/review/SNAPSHOT.json`; files `MUSE-REPORT-1104.md`,
`grammatik/Grammatik/X86/ComposeAcceptedConsumers.lean`, clean).
Reviewed the exact snapshot copy under `.tmp/review/author-1104/`
against this clone's accepted tree. No Lean or Rust work of my own;
`./lean-bau` / `./cargo-pruef` not applicable to a report-only review
(no tree changes to check). Author build evidence (BUILD-EVIDENCE.json):
final `./lean-probe` `0 error(s)` with full axiom prints, `./lean-bau`
`Build completed successfully (512 jobs)`.

## Checks performed (all against evidence, not claims)

1. Backbone is the accepted 824 composition, no re-proved rival.
   The closing `composeAccepted_gesamt` is built only from
   `fetchTrifftDekodierer` + `pilotKanonischErreicht` (both proved in
   `ComposeDecodeExec.lean`, the 824 module in this tree),
   `extByteschritt_weiter` + `decodeExt_kanonisch` (proved in
   `ExtendedExecution.lean`, the 575/660 line), `HwSchritt.reg`
   (constructor from `HardwareExecution.lean`), and the candidate's own
   quiet-row projections. No new decoder, evaluator, fetch, admission,
   or executor is defined anywhere in the file (grep for
   `def|theorem`: only witness machines, pins, and the closing).
2. Pending datatype covers exactly the unaccepted families.
   `PendingFam` has exactly 9 constructors: `breite696`, `breite698`,
   `lock722`, `fp724`, `seiten726`, `steuer734`, `kontext736`,
   `avx690`, `rueck708` — the task's list, no missing family, and no
   accepted piece (824/720/730/738/728) misfiled as pending. Lane 718
   (`HardwareDecodeDispatch.lean`) is absent from this tree
   (unaccepted rival dispatch); it is correctly neither imported nor
   enumerated as a producer family.
3. No unaccepted import. Import block is exactly 6 modules:
   `ComposeDecodeExec`, `ConcurrentIntegerExecution`,
   `AddressedHardwareExecution`, `ExceptionPriorityHardware`,
   `InterruptDescriptorHardware`, `HardwareExecution`. None of
   718/722/724/726/734/736/690/708/696/698 appears in any import;
   those numbers occur only as constructor names, audit codes, and
   CUTS text. All 6 imported modules exist in this tree.
4. Priority relation is the 738 one, not a fiat order. All of
   `kandidatenReihe`, `ersteWahl`, `abrufKandidat`,
   `dekodiereKandidat`, `adressKandidat`, `zugriffKandidat`,
   `teilungsKandidat`, `steuerKandidat` are defined in
   `ExceptionPriorityHardware.lean` (lines 136-453, verified); the
   four `reiheOhne*` projections derive per-stage silence from the
   actual `kandidatenReihe`/`ersteWahl` equations.
5. Joint _zeuge spans all three row kinds + three probes.
   `composeAccepted_zeuge` conjoins: fetched register run
   (`hwWit_o1_rip`, `hwWit_o1_rax` — both verified present in
   `HardwareExecution.lean`), integer drain 0->4
   (`concWit_anfang_null`, `concWit_spuelung` — present in
   `ConcurrentIntegerExecution.lean`), fetched LOCK XADD
   (`lockXaddGeholt_zeuge` — present in
   `AddressedHardwareExecution.lean`), both address spellings of 8200
   (`adress_formen_alias_pin` — present), divide-trap priority choice
   with halt verdict (`wahl_divFalle`, `urteil_divFalle` — present in
   `ExceptionPriorityHardware.lean`), same-level stack input
   (`waehleStapel_behalten` — present in
   `InterruptDescriptorHardware.lean`), and three planted
   `decodeExt = none` refusals by `decide` (width `[66,89,D8]`,
   LOCK XADD bytes, MOVSS bytes). `composeAccepted_gesamt_zeuge`
   jointly inhabits ALL closing premises on the reached pilot-move
   run (RIP 4096->4099, rax 5->9) with two independent
   memory-changing runs beside the register run.
6. No forbidden tactics; axioms standard. Grep finds no
   `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (only the words
   "admitted" in a comment and `#print axioms` lines). Reported axiom
   sets (`[propext]`, `[propext, Quot.sound]`, `[propext,
   Classical.choice, Quot.sound]`) are within the standard set.
7. Every premise of `composeAccepted_gesamt` is used (`hfetch` in
   both backbone legs, `hstep` in dispatcher + reg legs, `hmem` in
   the `HwSchritt.reg` leg, `hquiet` in both silence legs); no
   conclusion-shaped premise (the `HwSchritt` leg applies the
   constructor to `hstep`+`hmem`, it does not assume the step).
   The pending-family conjunct is discharged by the proved
   `composeAccepted_luecken`, not assumed.
8. CUTS honesty. The CUTS block states exactly what is and is not
   proved: pins show dispatcher refusal, not row ownership; near
   `ret` stays accepted pilot so the returns pin uses `iret`; the
   hardware layer has no Gabbro source program so non-degeneracy is
   witnessed by reached memory-changing runs (disclosed, not
   hidden); the one-line `Grammatik.lean` import is left for the
   merger (ownership-correct: this lane owns only module + report).

## Notes (not defects)

- The LOCK pin reuses the closed 730 witness bytes while
  `lockXaddGeholt_zeuge` runs a fetched LOCK XADD through the 730
  adapter: no contradiction, because `istOffen` pins the unified
  *dispatcher* (`decodeExt = none`) while the adapter-level run goes
  through a different path. The report states this reading
  explicitly ("the adapter takes exactly what the dispatcher
  refuses").
- The task's ZEUGE wording ("table-writing function") is
  Gabbro-source vocabulary with no literal hardware-layer witness;
  the author discloses the substitution (two independent
  memory-changing reached runs + register run spanning integer
  access, address computation, and fault-priority decision). At the
  hardware layer this is the correct non-degeneracy content.
- PATCH.diff touches only the two owned files (module + report),
  matching SNAPSHOT.json.

VERDICT: ACCEPT

The candidate composes the accepted 824/720/730/738/728 pieces
through the common dispatcher with no rival executor, no unaccepted
import, the exact 9-family pending enumeration threaded through as
still open, the genuine 738 priority relation, joint witnesses
spanning all three row kinds plus the three planted probes, honest
CUTS, and standard axioms. Integration need only add the one-line
`import Grammatik.X86.ComposeAcceptedConsumers` to
`grammatik/Grammatik.lean`.

## What remains open (for the merger, not this lane)

- One-line umbrella import at integration; re-run `./lean-bau`
  with the file covered.
- Per-family canonical-byte closings stay with lanes
  696/698/722/724/726/734/736/690/708. No hardware/source/TSO-bridge
  claim is made or needed here.
