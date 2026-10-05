# MUSE-REPORT-1139: Stack, call and return per core through TSO

Lane 1139, clone /home/simon/Dokumente/gabbro-muse/a1139, branch muse/1139.
Owned files only: `grammatik/Grammatik/X86/HwStackCalls.lean`,
`grammatik/Grammatik.lean` (one appended import line), this report.

## What was done

NEW FILE `grammatik/Grammatik/X86/HwStackCalls.lean` (~950 lines) connects
the stack/call/return family (`StackExecution`, `StackUnwind`,
`CallAlign16`, pilot push/pop/call/ret) to the coherent machine
(`HwMaschine`/`HwSchritt`/`HwWf` in `HardwareExecution.lean`), reusing all
accepted definitions unchanged. Push/call are stores through the acting
core's TSO buffer; pop/ret are loads with forwarding. Alignment and spill
privacy are stated premises with witnesses.

Definitions:
- `stapelSlot` (core slot = rsp minus 8), `stapelPush`, `stapelCall`
  (both via accepted `hwWortAusgabe`, i.e. eight `issueByte` steps).
- `StapelEreignis` (`push`/`ruf`/`pop`/`ret`), `stapelLadeWort` (eight
  `loadByte` reads with owner-only forwarding, reassembled via `bytesWort`),
  `stapelAdapter : HwAdapter StapelEreignis` (misaligned `ruf` refuses).
- `HwStern` (reflexive-transitive closure of `HwSchritt`).
- Witness machines/values `stapelWitM0`, `stapelWitGuardM0`,
  `stapelWitSlotAddr` (= 8184), `stapelWitWort` (= 42), chained drains
  `stapelWitD1..D8`, observations `stapelWitLoadEigen/Fremd`,
  `stapelWitNachRead/FremdNachFlush`, all `stapelWit_*` facts.

Theorems (all premises used; no `sorry`/`admit`/`axiom`/`native_decide`):
- (1) wf: `stapelPush_wf`, `stapelCall_wf`, `stapelAdapter_wf`.
- (2) agreement: `stapelPush_puffer`, `stapelPush_kein_speicher`,
  `stapelCall_puffer`, `stapelCall_kein_speicher`, `stapelEcho_schreiben`
  (buffer bytes = `write64` footprint bytes), `wortEintraege_mem`,
  `stapelLadeWort_still` (unbuffered load = accepted `read64`),
  `stapelByte_ausgabe` / `stapelByte_beob` (exact byte embedding into
  `HwSchritt.gibAus`/`lade`), `issueListe_stern`, `stapelPush_stern`,
  `stapelCall_stern` (word push = eight machine steps).
- Duties: `stapelRuf_ausgerichtet` (aligned passes, premise `hali`),
  `stapelRuf_fehlalign` (misaligned refuses, premise `hmis`),
  `stapelSpill_fetch_bleibt` (privacy premise `hpriv` feeds accepted
  `geholt_nach_fremd_schreiben`), `stapelAdapter_pop_still`,
  `stapelAdapter_ret_still`.
- (3) refusals: `issueListe_cons_none`, `stapelPush_wache`,
  `stapelCall_wache`, `stapelPop_unlesbar`, `stapelRet_unlesbar`.
- (4) witness: `stapelWit_wf/slot/align0/misalign1/priv/puffer8/
  mem_still/weiterleitung/fremd_alt/spuelung_aendert_speicher/fremd_neu/
  anfang_null/still_beispiel/guard_dicht/guard_push_verweigert/dark_dicht/
  dark_pop_verweigert/ruf_fehlalign_verweigert/ruf_ausgerichtet_puffert`
  and the joint `stapelTso_zeuge` (two cores, owner-only forwarding of
  42, foreign zero, eight-drain changing shared memory 0 to 42 observed
  from both cores, guard/dark/misaligned refusals beside it).

Axioms: every `#print axioms` reports a subset of
`[propext, Classical.choice, Quot.sound]` (the goal's allowed set);
most are `[propext]` or axiom-free.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwStackCalls.lean`:
  `== 0 error(s) ... exit 0`.
- `./lean-bau`: `Build completed successfully (601 jobs).`
  (One incident on the way: my first witness names `witMem`, `witBytes`,
  `witCode`, `witDaten`, `witKern`, `witM0` collided with
  `InterruptDescriptorHardware` / `MemoryTypeHardwareExecution`; all
  witness names now carry the `stapelWit` prefix. No other file was
  touched.)
- Five lane commits on `muse/1139` (skeleton, adapter+agreement,
  embedding+duties+refusals, witness+zeuge, rename+CUTS).

## What remains open (see CUTS block in the file)

- No silicon correspondence (self-consistency only); I did NOT consult
  the `.tmp/HARDWARE-REFERENCES` SDM extracts — the lane introduces no
  new hardware fact (every effect reuses an accepted definition), so
  there was nothing new to check against silicon, but the check was not
  performed and is recorded here, not claimed.
- No generic word-forwarding theorem (witnessed only; generic leg stays
  byte-level via cited `hwWeiterleitung` + `stapelLadeWort_still`).
- No generic drain-equals-`write64` theorem (eight-flush induction OPEN).
- No register/RIP movement (memory half only; registers ARE the accepted
  `schrittPush/Call/PopReg/Ret` shapes, restoration stays with
  `StackUnwind`).
- No LOCK/RMW, faults, interrupts, SIB, FP-control, SIMD, source/loader/
  budget link, or W/GX bridge.

## Task remarks

- Nothing in the task text appears wrong. Note rule 13 (`_zeuge` for
  ∀-over-syntax premises / `ZEUGE:` targets): the task names no `ZEUGE:`
  target and my theorems quantify over addresses/words/machines only, so
  no mechanical witness obligation applied; `stapelTso_zeuge` still joins
  all duty premises (alignment T/F, privacy, guard/dark denials,
  buffer/readability facts) on one reached non-degenerate run.
- `wit_still_beispiel` pulls in `Classical.choice` (via `decide` over the
  load path); within the allowed axiom set, no action taken.
