# MUSE-REPORT-1125: Asynchronous interrupt delivery on the coherent machine

Clone `/home/simon/Dokumente/gabbro-muse/a1125`, branch `muse/1125`. Owned files
only: `grammatik/Grammatik/X86/HwInterrupts.lean` (new, ~1060 lines),
`grammatik/Grammatik.lean` (one appended import line), this report.

## What was done

Connected the interrupt family to the coherent machine (`HwMaschine`/`HwSchritt`,
`HardwareExecution.lean` §11), lifting the accepted descriptor-layer evaluator
`liefere` (`InterruptDescriptorHardware.lean`) unchanged. No existing file was
edited except the one import line; no model was copied.

New definitions (all in `Gabbro.Grammatik.X86`):

- `AsyncArt` (`maskierbar` | `nichtMaskierbar`), `AsyncEreignis` (vector, kind,
  control snapshot `Steuerstand`, `codeOk`, privilege-change data, frame words;
  gate bytes are read from machine memory via `liesTorBytes`, never carried).
- Gates: `asyncVektorOk` (NMI is vector 2; maskable 32-255), `asyncBereit`
  (maskable needs IF; NMI bypasses).
- `asyncAnfrage` (builds the accepted `LieferAnfrage`: external source, read gate
  words, acting core's RSP), `asyncMasch` (delivery successor: new memory,
  handler RIP, frame-descended RSP; buffers/profiles/everything else copied).
- `asyncFertig` (mirrors `schiebeUndStelle`), `asyncSchritt` (checks-before-effects:
  vector, IF, IDT limit, gate read, `pruefeTor`, `waehleStapel`, canonical check,
  `schiebeRahmen`).
- `adapterInterrupt1125 : HwAdapter AsyncEreignis` (event carries its control
  snapshot; machine projection).
- `HwIntMaschine` (machine + per-core control), `IntEreignis`
  (`syncEv` | `asyncEv`), `HwIntSchritt` (`sync` embeds `HwSchritt` unchanged;
  `async` requires snapshot agreement and stores the IF update).
- Witness: `witSteuerNmi`, `witNmi` (NMI, IF=false snapshot), `witMaskiert`,
  `witFalschVektor`, `witLimitSteuer`, `witLimit`, `intWitKern`, `intWitStart`
  (reuses accepted `witMem`/`idtWitSteuer`/`loWit`), `intWitDunkel`, `witSchritt`,
  projections (`asyncMemOut`, `asyncRipOut`, `asyncIfOut`, `asyncGewOut`,
  `asyncBufOut`), TSO chain (`witIntZelle` = 16336, `witIntM2/Tso1/LoadEigen/
  LoadFremd/Tso2/NachFlush/FremdNachFlush`), `witIntSteuerAlle`.

New theorems: gate equations (`asyncVektorOk_nmi/maskierbar`, `asyncBereit_
maskierbar/nmi`) and refusals (`asyncBereit_maskiert`, `asyncVektor_nmi_falsch`,
`asyncVektor_maskierbar_klein`); successor projections (`asyncMasch_rip/rsp_neu/
mem/puffer_still/wf`); success equations (`asyncSchritt_zugestellt_wechsel/
behalten`); (1) `asyncSchritt_zugestellt_wechsel/behalten_wf`; (2)
`asyncSchritt_liefere_wechsel/behalten`; ten step refusals
(`asyncSchritt_verweigert_vektor/maskiert/limit/torlesung/torfehler/stapel/
kanonisch_wechsel/kanonisch_behalten/rahmen_wechsel/rahmen_behalten`); IF
behaviour (`asyncSchritt_interrupt_loescht_if`, `asyncSchritt_trap_behaelt_if`);
adapter refusals (`adapterInterrupt1125_verweigert_maskiert/vektor`); embedding
(`hwIntSchritt_sync_einbetten/nur`); witness facts (`intWitStart_wf`,
`witNmi_vektor_ok/bereit/limit/liest/gate_bereit/stapel/kanonisch/liefert_rip/
if/gew/puffer_0/puffer_1/rahmen_ss/rahmen_rip/aendert_ss/maskiert_verweigert/
bereich_verweigert/limit_verweigert/dunkel_verweigert`, `witInt_anfang_null/
weiterleitung/fremd_alt/spuelung_aendert/fremd_neu`, `witNmi_erfolg_ex`,
`witNmi_relation`); joint witness `asyncLiefer_zeuge` (18 conjuncts: handler
8192, IF false, switch true, both buffers still 0, frame words 16/4660 read back,
changed cell, four refusals, owner-only forwarding 42 vs 0, post-drain 42 on
both cores, `HwWf`, reached `HwIntSchritt.async` step).

## Check results

- `./lean-probe grammatik/Grammatik/X86/HwInterrupts.lean`: 0 errors.
- `./lean-bau`: "Build completed successfully (601 jobs)" — whole `grammatik/`
  green, including the new module.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the file. `#print axioms`
  per main theorem: everything is `propext` (or nothing), plus `Quot.sound`
  exactly where inductive existentials/cases are used (`hwIntSchritt_sync_*`,
  `witNmi_relation`, `asyncLiefer_zeuge`) — within the standard
  `propext/Classical.choice/Quot.sound` set; no new axioms.
- Silicon assumptions named S1/S2/S3/S5 in §1 and CUTS (INTR IF-gating with NMI
  bypass, NMI vector 2, maskable range 32-255, delivery is not a store-buffer
  drain, interrupt-clears/trap-keeps IF); stated as provenance, with only
  self-consistency proved.

## What remains open (see CUTS)

No hardware correspondence beyond self-consistency; no concrete maskable-success
witness (reused IDT image carries one gate — maskable admission is proved
abstractly through the same stage equations); no nested delivery/#DF/handler
execution; no target-to-W/GX simulation; no timing/APIC-arbitration/SMI; the
adapter reads control from the event, stored-control agreement (`hst`) is the
relation's premise.

## Task feedback

Nothing in the task was wrong. Two observations: (a) `HwMaschine` stores no
IDT/TSS/IF state, so the `HwAdapter` plug alone cannot thread the IF update —
the extended relation carries it, and the task's "or an extended step relation"
alternative was the right call; (b) the witness reuse of `witMem` constrained
the data cell to the stack window (16336, clear of the frame) — worked without
new byte images.
