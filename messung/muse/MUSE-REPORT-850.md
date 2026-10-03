# MUSE-REPORT-850: Composition closing — handler-table closing

## Task
Close declared interrupt handlers to their IDT entries and stacks;
undeclared vectors refuse at entry. Compose already-accepted modules
into one checked closing step; never re-prove producer internals and
never duplicate an interpreter or executor.

## What was done
New file `grammatik/Grammatik/X86/ComposeHandlerTable.lean`
(+ import line in `grammatik/Grammatik.lean`), importing only the
accepted producer `Grammatik.X86.InterruptDescriptorHardware` (lane 728).

Producer/consumer interface closed here (all producer names reused):
- Producer: `torAdresse`, `liesTorBytes`, `pruefeTor`,
  `waehleStapel`, `liefere`, `torFehlerCode`, plus the witness
  vocabulary (`witMem`, `witMemDunkel`, `idtWitSteuer`, `witAnfrage`,
  `loWit`, `wit_rahmen_ss`, `wit_rahmen_rip`, `wit_rahmen_aendert`,
  `ergebnisSpeicher`) and the success equations
  (`liefere_zugestellt_wechsel`, `liefere_zugestellt_behalten`).
- Consumer: the one checked closing step `handlerEintritt` over an
  explicit declared table `List HandlerDekl` (vector to handler RIP):
  declared lookup, gate bytes read from actual IDT memory at
  `torAdresse`, accepted `pruefeTor`, binding check of the parsed gate
  offset against the declared RIP, accepted `liefere`. Undeclared
  vectors refuse before any byte is read.

New definitions/theorems (exact names):
- `HandlerDekl`, `handlerFuer`, `HandlerWeigerung` (members
  `undeclariert`, `unlesbar`, `fehlbindung`, `torFehler`),
  `HandlerErgebnis`, `handlerEintritt`, `handlerWeigerung`,
  `handlerSpeicher`, `rahmenWorte_mit_tor`.
- `ComposeHandlerTable_verbindung` (generic success, switched stack,
  with producer agreement `liefere = .zugestellt ...`),
  `ComposeHandlerTable_verbindung_behalten` (kept-stack leg).
- `handler_undeclariert_verweigert`,
  `handler_unlesbar_verweigert`, `handler_torfehler_verweigert`,
  `handler_fehlbindung_verweigert`.
- Witness: `witHandler`, `witHandlers`, `witGate`,
  `witHandlersFalsch`, and `ComposeHandlerTable_verbindung_zeuge`:
  every premise jointly instantiated on the byte-populated IDT/TSS
  witness (declared vector 2, IST switch taken, IF cleared,
  five-word frame reads back, two cells observably change) plus three
  planted refusals (undeclared vector, renamed handler, dark stack).

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeHandlerTable.lean`:
  `== 0 error(s)`, no warnings.
- `./lean-bau`: `Build completed successfully (511 jobs)` for the
  whole project.
- `#print axioms`: main theorems depend on exactly
  `[propext, Classical.choice, Quot.sound]` (inherited from the
  accepted producer theorems); auxiliaries on `[propext]` or nothing.
  No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise
  of every theorem is used by its proof.
- No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved files.

## What remains open (CUTS in the file)
GDT/code-row ownership (`codeOk` stays an explicit input; lane 672),
async completion (nested delivery, #DF, TSO/store-buffer: lanes
672/708 and concurrency lanes), handler fetch past delivery, full
256-vector table, source lowering (shared IR lane 287,
QUELLBRUECKE), hardware/silicon claims. An unreadable gate half
refuses as `unlesbar`, since the accepted producer has no distinct
in-limit-unreadable member.

## Believed-wrong items in the task
None. The target names were satisfiable as specified; the generic
theorem quantifies over X86 machine/interface values only (no program
syntax), so the syntax-witness clause of rule 13 does not trigger;
non-degeneracy is carried by the X86 analogue (populated IDT/TSS,
taken IST switch, five-word frame with two observably changed cells),
as in the `ComposeImageFetch` precedent.
