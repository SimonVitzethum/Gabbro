# MUSE-REPORT-1104: Close the accepted consumers through the common dispatcher

Clone `/home/simon/Dokumente/gabbro-muse/a1104`, branch `muse/1104` verified
at start. Lane owns only `grammatik/Grammatik/X86/ComposeAcceptedConsumers.lean`
(new, ~470 lines) and this report. No network, no push, no other models called.
Rust work: none (Lean-only lane; `./cargo-pruef` not applicable).

## What was done

ONE fetched-execution closing over `HwMaschine` composed from already-accepted
pieces, reusing `decodeExt`/`stepExt`/`extByteschritt` and the 824 composition
lemmas. No second executor defined; no unaccepted module imported (imports are
exactly `ComposeDecodeExec`, `ConcurrentIntegerExecution`,
`AddressedHardwareExecution`, `ExceptionPriorityHardware`,
`InterruptDescriptorHardware`, `HardwareExecution`).

New definitions:

- `PendingFam` — checked enumeration of the 9 pending families
  (`breite696/698`, `lock722`, `fp724`, `seiten726`, `steuer734`,
  `kontext736`, `avx690`, `rueck708`).
- `familienCode : PendingFam → Nat` — owning lane number per family (audit).
- `istOffen : PendingFam → Prop` — one dispatcher-refusal pin per family
  (`decodeExt <bytes> = none`; LOCK pin reuses the closed 730 witness bytes,
  returns pin uses `iret` since near `ret` stays accepted pilot).
- `gesamtWitBf/Bild/Bytes/Code/Daten/Mem/Reg/Kern/M` — witness machine: pilot
  `movReg64 rax, rcx` at 4096 with exactly-3-byte execute permission, so the
  fetched window is exactly the encoding with empty suffix.
- `gesamtWitS1/T1` — named successor states (parser workaround, see below).

New theorems (every premise is used; no premise is shaped like its conclusion):

- `composeAccepted_luecken (p)` — every family stays open through its pin;
  explicit `cases ... with` arms, so adding a family without a pin is a type
  error. `composeAccepted_luecken_zeuge` inhabits it (LOCK).
- `reiheOhneAbruf/Dekodiere/Adresse/Zugriff` — a silent 738 ordered row
  carries no per-stage candidate.
- `composeAccepted_gesamt` — fetched bytes to `HwSchritt.reg` runs: 824
  decoder agreement (`fetchTrifftDekodierer`) and dispatcher selection
  (`extByteschritt_weiter`), the 660 register-path gate, 738 priority
  silence on address and access, pending families threaded through as
  still open (`composeAccepted_luecken`).
- `composeAccepted_gesamt_zeuge` — joint instantiation of ALL closing
  premises on the reached pilot-move run (RIP 4096→4099, rax 5→9); the
  `HwSchritt` leg reuses the closing itself.
- `composeAccepted_zeuge` — cross-piece joint witness: fetched register run
  (`hwWit_o1_rip/rax`), integer drain 0→4 (`concWit_anfang_null/spuelung`),
  fetched LOCK XADD (`lockXaddGeholt_zeuge`), both address spellings of 8200
  (`adress_formen_alias_pin`), divide-trap choice with halt verdict
  (`wahl_divFalle`, `urteil_divFalle`), same-level stack input
  (`waehleStapel_behalten` on `concWitMem`/`idtWitSteuer`), and the three
  planted pending refusals (width `[66,89,D8]`, LOCK XADD bytes, single-
  precision MOVSS bytes — all `decodeExt = none` by `decide`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/ComposeAcceptedConsumers.lean`:
  `0 error(s)`.
- `./lean-bau`: `Build completed successfully (512 jobs).`
- Axioms: `familienCode` none; `luecken(+zeuge)`, `reihe*` `[propext]`;
  `gesamt` `[propext, Quot.sound]`; both `zeige` `[propext,
  Classical.choice, Quot.sound]` — all within the standard set.
- No `sorry/admit/axiom/native_decide/unsafe`; every proof premise is used.

## What remains open (by design)

Pending families 696/698/722/724/726/734/736/690/708 stay explicit gaps in
CUTS. No hardware/source/TSO-bridge/entry/budget claim is made. The merger
must add `import Grammatik.X86.ComposeAcceptedConsumers` to
`grammatik/Grammatik.lean` — this lane's permission set allows owning only
its module and report, so the one-line import is left for integration
(`./lean-bau` is therefore green without covering the new file; coverage
comes with the import).

## Notes / things in the task I read strictly

1. "Shared author gates (see lane 1100 task)" — no `lanes/1100.md` exists in
   this clone; I worked to the HARD RULES gates (small pieces, probe after
   each, green commits, exact review-shape theorems).
2. Parser finding: a multi-line `{ s with field := <application> }` update
   directly after `.weiter` fails to parse (`unexpected token '('`), while
   the single-line form parses. Workaround used: named successor defs
   (`gesamtWitS1/T1`). Reproducible minimal cases were probed in
   `.tmp/probe1104*.lean` (scratch; kept in git-ignored `.tmp/`, no
   removal tool is available to this lane and `git status` is clean).
3. ZEUGE wording ("table-writing function") is Gabbro-source vocabulary and
   has no literal witness at the hardware layer: `geholt`/`decodeExt` know
   no `Vertrag`/`Stmt`. Non-degeneracy here is witnessed by two independent
   memory-changing reached runs (integer drain 0→4, LOCK XADD byte
   8201→32) beside the register run; the `HwSchritt.reg` leg of the closing
   is memory-unchanged by construction (its gate premise). This is stated
   in CUTS, not hidden.
4. The `istOffen` pins show dispatcher refusal, not row ownership: which
   bytes each pending family will accept stays with the owning lanes.
5. One commit message was reused verbatim across two commits (the
   `arbeitsprotokoll/.commitmsg` file was not rewritten before the second
   `commit.sh`); content of both commits is as described here. The file is
   gitignored and carries no audit content.
